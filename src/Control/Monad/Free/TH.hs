{-# LANGUAGE TemplateHaskell #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Trans.TH
-- Copyright   :  (C) 2008-2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  MPTCs, fundeps
--
-- Automatic generation of free monadic actions.
--
----------------------------------------------------------------------------
module Control.Monad.Free.TH (
  makeFree
) where

import Control.Arrow
import Control.Applicative
import Control.Monad
import Data.Char (toLower)
import Language.Haskell.TH

data Arg
  = Captured Type Exp
  | Param    Type
  deriving (Show)

params :: [Arg] -> [Type]
params [] = []
params (Param t : xs) = t : params xs
params (_ : xs) = params xs

captured :: [Arg] -> [(Type, Exp)]
captured [] = []
captured (Captured t e : xs) = (t, e) : captured xs
captured (_ : xs) = captured xs

zipExprs :: [Exp] -> [Exp] -> [Arg] -> [Exp]
zipExprs (p:ps) cs (Param    _   : as) = p : zipExprs ps cs as
zipExprs ps (c:cs) (Captured _ _ : as) = c : zipExprs ps cs as
zipExprs _ _ _ = []

tyVarBndrName :: TyVarBndr -> Name
tyVarBndrName (PlainTV  name)   = name
tyVarBndrName (KindedTV name _) = name

findTypeOrFail :: String -> Q Name
findTypeOrFail s = lookupTypeName s >>= maybe (fail $ s ++ " is not in scope") return

findValueOrFail :: String -> Q Name
findValueOrFail s = lookupValueName s >>= maybe (fail $ s ++ "is not in scope") return

-- | Pick a name for an operation.
-- For normal constructors it lowers first letter.
-- For infix ones it omits the first @:@.
mkOpName :: String -> Q String
mkOpName (':':name) = return name
mkOpName ( c :name) = return $ toLower c : name
mkOpName _ = fail "null constructor name"

-- | Check if parameter is used in type.
usesTV :: Name -> Type -> Bool
usesTV n (VarT name)  = n == name
usesTV n (AppT t1 t2) = any (usesTV n) [t1, t2]
usesTV n (SigT t  _ ) = usesTV n t
usesTV n (ForallT bs _ t) = usesTV n t && n `notElem` map tyVarBndrName bs
usesTV _ _ = False

-- | Analyze constructor argument.
mkArg :: Name -> Type -> Q Arg
mkArg n t
  | usesTV n t =
      case t of
        -- if parameter is used as is, the return type should be ()
        -- as well as the corresponding expression
        VarT _ -> return $ Captured (TupleT 0) (TupE [])
        -- if argument is of type (a1 -> ... -> aN -> param) then the
        -- return type is N-tuple (a1, ..., aN) and the corresponding
        -- expression is an N-tuple secion (,...,).
        AppT (AppT ArrowT _) _ -> do
          (ts, name) <- arrowsToTuple t
          when (name /= n) $ fail "return type is not the parameter"
          let tup = foldl AppT (TupleT $ length ts) ts
          xs <- mapM (const $ newName "x") ts
          return $ Captured tup (LamE (map VarP xs) (TupE (map VarE xs)))
        _ -> fail "don't know how to make Arg"
  | otherwise = return $ Param t
  where
    arrowsToTuple (AppT (AppT ArrowT t1) (VarT name)) = return ([t1], name)
    arrowsToTuple (AppT (AppT ArrowT t1) t2) = do
      (ts, name) <- arrowsToTuple t2
      return (t1:ts, name)
    arrowsToTuple _ = fail "return type is not a variable"

-- | Apply transformation to the return value independently of how many
-- parameters does @e@ have.
-- E.g. @mapRet Just (\x y z -> x + y * z)@ goes to
-- @\x y z -> Just (x + y * z)@
mapRet :: (Exp -> Exp) -> Exp -> Exp
mapRet f (LamE ps e) = LamE ps $ mapRet f e
mapRet f e = f e

-- | Unification of two types.
-- @next@ with @a -> next@ gives @Maybe a@ return type
-- @a -> next@ with @b -> next@ gives @Either a b@ return type
unifyT :: (Type, Exp) -> (Type, Exp) -> Q (Type, [Exp])
unifyT (TupleT 0, _) (TupleT 0, _) = fail "can't accept 2 mere parameters"
unifyT (TupleT 0, _) (t, e) = do
  maybe'   <- ConT <$> findTypeOrFail  "Maybe"
  nothing' <- ConE <$> findValueOrFail "Nothing"
  just'    <- ConE <$> findValueOrFail "Just"
  return $ (AppT maybe' t, [nothing', mapRet (AppE just') e])
unifyT x y@(TupleT 0, _) = second reverse <$> unifyT y x
unifyT (t1, e1) (t2, e2) = do
  either' <- ConT <$> findTypeOrFail  "Either"
  left'   <- ConE <$> findValueOrFail "Left"
  right'  <- ConE <$> findValueOrFail "Right"
  return $ (AppT (AppT either' t1) t2, [mapRet (AppE left') e1, mapRet (AppE right') e2])

-- | Unifying a list of types (possibly refining expressions).
-- Name is used when the return type is supposed to be arbitrary.
unifyCaptured :: Name -> [(Type, Exp)] -> Q (Type, [Exp])
unifyCaptured a []       = return (VarT a, [])
unifyCaptured _ [(t, e)] = return (t, [e])
unifyCaptured _ [x, y]   = unifyT x y
unifyCaptured _ _ = fail "can't unify more than 2 arguments that use type parameter"

liftCon' :: Type -> Name -> [Name] -> Name -> [Type] -> Q [Dec]
liftCon' f n ns cn ts = do
  -- prepare some names
  opName <- mkName <$> mkOpName (nameBase cn)
  m      <- newName "m"
  a      <- newName "a"
  monadFree <- findTypeOrFail  "MonadFree"
  liftF     <- findValueOrFail "liftF"
  -- look at the constructor parameters
  args <- mapM (mkArg n) ts
  let ps = params args    -- these are not using type parameter
      cs = captured args  -- these capture it somehow
  -- based on cs we get return type and refined expressions
  -- (e.g. with Nothing/Just or Left/Right tags)
  (retType, es) <- unifyCaptured a cs
  -- operation type is (a1 -> a2 -> ... -> aN -> m r)
  let opType  = foldr (AppT . AppT ArrowT) (AppT (VarT m) retType) ps
  -- picking names for the implementation
  xs  <- mapM (const $ newName "p") ps
  let pat  = map VarP xs                      -- this is LHS
      exprs = zipExprs (map VarE xs) es args  -- this is what ctor would be applied to
      fval = foldl AppE (ConE cn) exprs       -- this is RHS without liftF
      q = map PlainTV $ qa ++ m : ns
      qa = case retType of VarT b | a == b -> [a]; _ -> []
      f' = foldl AppT f (map VarT ns)
  return $
    [ SigD opName (ForallT q [ClassP monadFree [f', VarT m]] opType)
    , FunD opName [ Clause pat (NormalB $ AppE (VarE liftF) fval) [] ] ]

-- | Provide free monadic actions for a single value constructor.
liftCon :: Type -> Name -> [Name] -> Con -> Q [Dec]
liftCon f n ns con =
  case con of
    NormalC cName fields -> liftCon' f n ns cName $ map snd fields
    RecC    cName fields -> liftCon' f n ns cName $ map (\(_, _, ty) -> ty) fields
    _ -> fail $ "liftCon: Don't know how to lift " ++ show con

-- | Provide free monadic actions for a type declaration.
liftDec :: Dec -> Q [Dec]
liftDec (DataD _ tyName tyVarBndrs cons _)
  | null tyVarBndrs = fail $ "Type " ++ show tyName ++ " needs at least one free variable"
  | otherwise = concat <$> mapM (liftCon con nextTyName (init tyNames)) cons
    where
      tyNames    = map tyVarBndrName tyVarBndrs
      nextTyName = last tyNames
      con        = ConT tyName
liftDec dec = fail $ "liftDec: Don't know how to lift " ++ show dec

-- | @$(makeFree ''Type)@ provides free monadic actions for the
-- constructors of the given type.
makeFree :: Name -> Q [Dec]
makeFree tyCon = do
  info <- reify tyCon
  case info of
    TyConI dec -> liftDec dec
    _ -> fail "makeFree expects a type constructor"

