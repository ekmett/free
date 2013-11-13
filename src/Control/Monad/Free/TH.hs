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

mkOpName :: String -> Q String
mkOpName (':':name) = return name
mkOpName ( c :name) = return $ toLower c : name
mkOpName _ = fail "null constructor name"

usesTV :: Name -> Type -> Bool
usesTV n (VarT name)  = n == name
usesTV n (AppT t1 t2) = any (usesTV n) [t1, t2]
usesTV n (SigT t  _ ) = usesTV n t
usesTV n (ForallT bs _ t) = usesTV n t && n `notElem` map tyVarBndrName bs
usesTV _ _ = False

mkArg :: Name -> Type -> Q Arg
mkArg n t
  | usesTV n t =
      case t of
        VarT _ -> return $ Captured (TupleT 0) (TupE []) -- () :: ()
        AppT (AppT ArrowT _) _ -> do
          (ts, name) <- arrowsToTuple t
          when (name /= n) $ fail "mkArg: don't know how to make Arg"
          let tup = foldl AppT (TupleT $ length ts) ts
          xs <- mapM (const $ newName "x") ts
          return $ Captured tup (LamE (map VarP xs) (TupE (map VarE xs)))
        _ -> fail "mkArg: don't know how to make Arg"
  | otherwise = return $ Param t
  where
    arrowsToTuple (AppT (AppT ArrowT t1) (VarT name)) = return ([t1], name)
    arrowsToTuple (AppT (AppT ArrowT t1) t2) = do
      (ts, name) <- arrowsToTuple t2
      return (t1:ts, name)
    arrowsToTuple _ = fail "mkArg: not an arrow"

mapRet :: (Exp -> Exp) -> Exp -> Exp
mapRet f (LamE ps e) = LamE ps $ mapRet f e
mapRet f e = f e

unifyT :: (Type, Exp) -> (Type, Exp) -> Q (Type, [Exp])
unifyT (TupleT 0, _) (TupleT 0, _) = fail "can't unify"
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

unifyCaptured :: [(Type, Exp)] -> Q (Type, [Exp])
unifyCaptured [] = return (TupleT 0, []) -- FIXME: should be any 'a'
unifyCaptured [(t, e)] = return (t, [e])
unifyCaptured [x, y] = unifyT x y
unifyCaptured _ = fail "unifyCaptured: can't unify more than 2 distinct types"

liftCon' :: Type -> Name -> Name -> [Type] -> Q [Dec]
liftCon' f n cn ts = do
  opName <- mkName <$> mkOpName (nameBase cn)
  m      <- newName "m"
  monadFree <- findTypeOrFail  "MonadFree"
  liftF     <- findValueOrFail "liftF"
  args <- mapM (mkArg n) ts
  let ps = params args
      cs = captured args
  (retType, es) <- unifyCaptured cs
  let opType  = foldr (AppT . AppT ArrowT) (AppT (VarT m) retType) ps
  xs <- mapM (const $ newName "p") ps
  let pat  = map VarP xs
      exprs = zipExprs (map VarE xs) es args
      fval = foldl AppE (ConE cn) exprs
  return $
    [ SigD opName (ForallT [PlainTV m] [ClassP monadFree [f, VarT m]] opType)
    , FunD opName [ Clause pat (NormalB $ AppE (VarE liftF) fval) [] ] ]

-- | Provide free monadic actions for a single value constructor.
liftCon :: Type -> Name -> Con -> Q [Dec]
liftCon f n (NormalC cName fields) = liftCon' f n cName $ map snd fields
liftCon f n (RecC    cName fields) = liftCon' f n cName $ map (\(_, _, ty) -> ty) fields
liftCon _ _ con = fail $ "liftCon: Don't know how to lift " ++ show con

-- | Provide free monadic actions for type declaration.
liftDec :: Dec -> Q [Dec]
liftDec (DataD _ tyName tyVarBndrs cons _)
  | null tyVarBndrs = fail $ "Type " ++ show tyName ++ " needs at least one free variable"
  | otherwise = concat <$> mapM (liftCon con nextTyName) cons
    where
      nextTyName = tyVarBndrName $ last tyVarBndrs
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

