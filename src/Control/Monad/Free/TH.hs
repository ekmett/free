{-# LANGUAGE CPP #-}
#if MIN_VERSION_template_haskell(2,12,0)
{-# LANGUAGE Safe #-}
#else
{-# LANGUAGE Trustworthy #-}
#endif

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
module Control.Monad.Free.TH
  (
   -- * Free monadic actions
   makeFree,
   makeFree_,
   makeFreeCon,
   makeFreeCon_,

   -- * Documentation
   -- $doc

   -- * Examples
   -- $examples
  ) where

import Control.Arrow
import Control.Monad
import Data.Char (toLower)
import Data.List ((\\), nub)
import Language.Haskell.TH.Datatype.TyVarBndr
import Language.Haskell.TH.Lib
import Language.Haskell.TH.Ppr (pprint)
import Language.Haskell.TH.Syntax

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
mkOpName _ = fail "impossible happened: empty (null) constructor name"

-- | Check if parameter is used in type.
usesTV :: Name -> Type -> Bool
usesTV n (VarT name)  = n == name
usesTV n (AppT t1 t2) = any (usesTV n) [t1, t2]
usesTV n (SigT t  _ ) = usesTV n t
usesTV n (ForallT bs _ t) = usesTV n t && n `notElem` map tvName bs
usesTV _ _ = False

-- | Analyze constructor argument.
mkArg :: Type -> Type -> Q Arg
mkArg (VarT n) t
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
          when (any (usesTV n) ts) $ fail $ unlines
            [ "type variable " ++ pprint n ++ " is forbidden"
            , "in a type like (a1 -> ... -> aN -> " ++ pprint n ++ ")"
            , "in a constructor's argument type: " ++ pprint t ]
          when (name /= n) $ fail $ unlines
            [ "expected final return type `" ++ pprint n ++ "'"
            , "but got `" ++ pprint name ++ "'"
            , "in a constructor's argument type: `" ++ pprint t ++ "'" ]
          let tup = nonUnaryTupleT ts
          xs <- mapM (const $ newName "x") ts
          Captured tup <$> lamE (map varP xs) (pure $ nonUnaryTupE $ map VarE xs)
        _ -> fail $ unlines
              [ "expected a type variable `" ++ pprint n ++ "'"
              , "or a type like (a1 -> ... -> aN -> " ++ pprint n ++ ")"
              , "but got `" ++ pprint t ++ "'"
              , "in a constructor's argument" ]
  | otherwise = return $ Param t
  where
    arrowsToTuple (AppT (AppT ArrowT t1) t2) = do
      (ts, name) <- arrowsToTuple t2
      return (t1:ts, name)
    arrowsToTuple (VarT name) = return ([], name)
    arrowsToTuple rt = fail $ unlines
      [ "expected final return type `" ++ pprint n ++ "'"
      , "but got `" ++ pprint rt ++ "'"
      , "in a constructor's argument type: `" ++ pprint t ++ "'" ]

    nonUnaryTupleT :: [Type] -> Type
    nonUnaryTupleT [t'] = t'
    nonUnaryTupleT ts   = foldl AppT (TupleT $ length ts) ts

    nonUnaryTupE :: [Exp] -> Exp
    nonUnaryTupE [e] = e
    nonUnaryTupE es  = TupE $
#if MIN_VERSION_template_haskell(2,16,0)
                              map Just
#endif
                              es

mkArg n _ = fail $ unlines
  [ "expected a type variable"
  , "but got `" ++ pprint n ++ "'"
  , "as the last parameter of the type constructor" ]

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
  return (AppT maybe' t, [nothing', mapRet (AppE just') e])
unifyT x y@(TupleT 0, _) = second reverse <$> unifyT y x
unifyT (t1, e1) (t2, e2) = do
  either' <- ConT <$> findTypeOrFail  "Either"
  left'   <- ConE <$> findValueOrFail "Left"
  right'  <- ConE <$> findValueOrFail "Right"
  return (AppT (AppT either' t1) t2, [mapRet (AppE left') e1, mapRet (AppE right') e2])

-- | Unifying a list of types (possibly refining expressions).
-- Name is used when the return type is supposed to be arbitrary.
unifyCaptured :: Name -> [(Type, Exp)] -> Q (Type, [Exp])
unifyCaptured a []       = return (VarT a, [])
unifyCaptured _ [(t, e)] = return (t, [e])
unifyCaptured _ [x, y]   = unifyT x y
unifyCaptured _ xs = fail $ unlines
  [ "can't unify more than 2 return types"
  , "that use type parameter"
  , "when unifying return types: "
  , unlines (map (pprint . fst) xs) ]

extractVars :: Type -> [Name]
extractVars (ForallT bs _ t) = extractVars t \\ map tvName bs
extractVars (VarT n) = [n]
extractVars (AppT x y) = extractVars x ++ extractVars y
extractVars (SigT x k) = extractVars x ++ extractVars k
extractVars (InfixT x _ y) = extractVars x ++ extractVars y
extractVars (UInfixT x _ y) = extractVars x ++ extractVars y
extractVars (ParensT x) = extractVars x
extractVars _ = []

liftCon' :: Bool -> [TyVarBndrSpec] -> Cxt -> Type -> Type -> [Type] -> Name -> [Type] -> Q [Dec]
liftCon' typeSig tvbs cx f n ns cn ts = do
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
  let pat  = map varP xs                      -- this is LHS
      exprs = zipExprs (map VarE xs) es args  -- this is what ctor would be applied to
      fval = foldl AppE (ConE cn) exprs       -- this is RHS without liftF
      ns' = nub (concatMap extractVars ns)
      q = filter nonNext tvbs ++ map plainTVSpecified (qa ++ m : ns')
      qa = case retType of VarT b | a == b -> [a]; _ -> []
      f' = foldl AppT f ns
  funClause <- clause pat (normalB $ appE (varE liftF) $ pure fval) []
  return $ concat
    [ if typeSig
        then [ SigD opName (ForallT q (cx ++ [ConT monadFree `AppT` f' `AppT` VarT m]) opType) ]
        else []
    , [ FunD opName [funClause] ] ]
  where
    nonNext tv = VarT (tvName tv) /= n

-- | Provide free monadic actions for a single value constructor.
liftCon :: Bool -> [TyVarBndrSpec] -> Cxt -> Type -> Type -> [Type] -> Maybe [Name] -> Con -> Q [Dec]
liftCon typeSig ts cx f n ns onlyCons con
  | not (any (`melem` onlyCons) (constructorNames con)) = return []
  | otherwise = case con of
      NormalC cName fields -> liftCon' typeSig ts cx f n ns cName $ map snd fields
      RecC    cName fields -> liftCon' typeSig ts cx f n ns cName $ map (\(_, _, ty) -> ty) fields
      InfixC  (_,t1) cName (_,t2) -> liftCon' typeSig ts cx f n ns cName [t1, t2]
      ForallC ts' cx' con' -> liftCon typeSig (ts ++ ts') (cx ++ cx') f n ns onlyCons con'
      GadtC cNames fields resType -> do
        decs <- forM (filter (`melem` onlyCons) cNames) $ \cName ->
                  liftGadtC cName fields resType typeSig ts cx f
        return (concat decs)
      RecGadtC cNames fields resType -> do
        let fields' = map (\(_, x, y) -> (x, y)) fields
        decs <- forM (filter (`melem` onlyCons) cNames) $ \cName ->
                  liftGadtC cName fields' resType typeSig ts cx f
        return (concat decs)

splitAppT :: Type -> (Type, [Type])
splitAppT ty = go ty ty []
  where
    go :: Type -> Type -> [Type] -> (Type, [Type])
    go _      (AppT ty1 ty2)     args = go ty1 ty1 (ty2:args)
    go origTy (SigT ty' _)       args = go origTy ty' args
    go origTy (InfixT ty1 n ty2) args = go origTy (ConT n `AppT` ty1 `AppT` ty2) args
    go origTy (ParensT ty')      args = go origTy ty' args
    go origTy _                  args = (origTy, args)

liftGadtC :: Name -> [BangType] -> Type -> Bool -> [TyVarBndrSpec] -> Cxt -> Type -> Q [Dec]
liftGadtC cName fields resType typeSig ts cx f =
  liftCon typeSig ts cx f nextTy (init tys) Nothing (NormalC cName fields)
  where
    (_f, tys) = splitAppT resType
    nextTy = last tys

melem :: Eq a => a -> Maybe [a] -> Bool
melem _ Nothing   = True
melem x (Just xs) = x `elem` xs

-- | Get construstor name(s).
constructorNames :: Con -> [Name]
constructorNames (NormalC  name _)    = [name]
constructorNames (RecC     name _)    = [name]
constructorNames (InfixC   _ name _)  = [name]
constructorNames (ForallC  _ _ c)     = constructorNames c
constructorNames (GadtC names _ _)    = names
constructorNames (RecGadtC names _ _) = names

-- | Provide free monadic actions for a type declaration.
liftDec :: Bool             -- ^ Include type signature?
        -> Maybe [Name]     -- ^ Include only mentioned constructor names. Use all constructors when @Nothing@.
        -> Dec              -- ^ Data type declaration.
        -> Q [Dec]
liftDec typeSig onlyCons (DataD _ tyName tyVarBndrs _ cons _)
  | null tyVarBndrs = fail $ "Type constructor " ++ pprint tyName ++ " needs at least one type parameter"
  | otherwise = concat <$> mapM (liftCon typeSig [] [] con nextTy (init tys) onlyCons) cons
    where
      tys     = map (VarT . tvName) tyVarBndrs
      nextTy  = last tys
      con        = ConT tyName
liftDec _ _ dec = fail $ unlines
  [ "failed to derive makeFree operations:"
  , "expected a data type constructor"
  , "but got " ++ pprint dec ]

-- | Generate monadic actions for a data type.
genFree :: Bool         -- ^ Include type signature?
        -> Maybe [Name] -- ^ Include only mentioned constructor names. Use all constructors when @Nothing@.
        -> Name         -- ^ Type name.
        -> Q [Dec]      -- ^ Generated declarations.
genFree typeSig cnames tyCon = do
  info <- reify tyCon
  case info of
    TyConI dec -> liftDec typeSig cnames dec
    _ -> fail "makeFree expects a type constructor"

-- | Generate monadic action for a single constructor of a data type.
genFreeCon :: Bool         -- ^ Include type signature?
           -> Name         -- ^ Constructor name.
           -> Q [Dec]      -- ^ Generated declarations.
genFreeCon typeSig cname = do
  info <- reify cname
  case info of
    DataConI _ _ tname -> genFree typeSig (Just [cname]) tname
    _ -> fail $ unlines
          [ "expected a data constructor"
          , "but got " ++ pprint info ]

-- | @$('makeFree' ''T)@ provides free monadic actions for the
-- constructors of the given data type @T@.
makeFree :: Name -> Q [Dec]
makeFree = genFree True Nothing

-- | Like 'makeFree', but does not provide type signatures.
-- This can be used to attach Haddock comments to individual arguments
-- for each generated function.
--
-- @
-- data LangF x = Output String x
--
-- makeFree_ 'LangF
--
-- -- | Output a string.
-- output :: MonadFree LangF m =>
--           String   -- ^ String to output.
--        -> m ()     -- ^ No result.
-- @
--
-- 'makeFree_' must be called *before* the explicit type signatures.
makeFree_ :: Name -> Q [Dec]
makeFree_ = genFree False Nothing

-- | @$('makeFreeCon' 'Con)@ provides free monadic action for a data
-- constructor @Con@. Note that you can attach Haddock comment to the
-- generated function by placing it before the top-level invocation of
-- 'makeFreeCon':
--
-- @
-- -- | Output a string.
-- makeFreeCon 'Output
-- @
makeFreeCon :: Name -> Q [Dec]
makeFreeCon = genFreeCon True

-- | Like 'makeFreeCon', but does not provide a type signature.
-- This can be used to attach Haddock comments to individual arguments.
--
-- @
-- data LangF x = Output String x
--
-- makeFreeCon_ 'Output
--
-- -- | Output a string.
-- output :: MonadFree LangF m =>
--           String   -- ^ String to output.
--        -> m ()     -- ^ No result.
-- @
--
-- 'makeFreeCon_' must be called *before* the explicit type signature.
makeFreeCon_ :: Name -> Q [Dec]
makeFreeCon_ = genFreeCon False

{- $doc
 To generate free monadic actions from a @Type@, it must be a @data@
 declaration (maybe GADT) with at least one free variable. For each constructor of the type, a
 new function will be declared.

 Consider the following generalized definitions:

 > data Type a1 a2 … aN param = …
 >                            | FooBar t1 t2 t3 … tJ
 >                            | (:+) t1 t2 t3 … tJ
 >                            | t1 :* t2
 >                            | t1 `Bar` t2
 >                            | Baz { x :: t1, y :: t2, …, z :: tJ }
 >                            | forall b1 b2 … bN. cxt => Qux t1 t2 … tJ
 >                            | …

 where each of the constructor arguments @t1, …, tJ@ is either:

 1. A type, perhaps depending on some of the @a1, …, aN@.

 2. A type dependent on @param@, of the form @s1 -> … -> sM -> param@, M ≥ 0.
      At most 2 of the @t1, …, tJ@ may be of this form. And, out of these two,
      at most 1 of them may have @M == 0@; that is, be of the form @param@.

 For each constructor, a function will be generated. First, the name
 of the function is derived from the name of the constructor:

 * For prefix constructors, the name of the constructor with the first
   letter in lowercase (e.g. @FooBar@ turns into @fooBar@).

 * For infix constructors, the name of the constructor with the first
   character (a colon @:@), removed (e.g. @:+@ turns into @+@).

 Then, the type of the function is derived from the arguments to the constructor:

 > …
 > fooBar :: (MonadFree Type m) => t1' -> … -> tK' -> m ret
 > (+)    :: (MonadFree Type m) => t1' -> … -> tK' -> m ret
 > bar    :: (MonadFree Type m) => t1  -> … -> tK' -> m ret
 > baz    :: (MonadFree Type m) => t1' -> … -> tK' -> m ret
 > qux    :: (MonadFree Type m, cxt) => t1' -> … -> tK' -> m ret
 > …

 The @t1', …, tK'@ are those @t1@ … @tJ@ that only depend on the
 @a1, …, aN@.

 The type @ret@ depends on those constructor arguments that reference the
 @param@ type variable:

     1. If no arguments to the constructor depend on @param@, @ret ≡ a@, where
       @a@ is a fresh type variable.

     2. If only one argument in the constructor depends on @param@, then
       @ret ≡ (s1, …, sM)@. In particular, if @M == 0@, then @ret ≡ ()@; if @M == 1@, @ret ≡ s1@.

     3. If two arguments depend on @param@, (e.g. @u1 -> … -> uL -> param@ and
       @v1 -> … -> vM -> param@, then @ret ≡ Either (u1, …, uL) (v1, …, vM)@.

 Note that @Either a ()@ and @Either () a@ are both isomorphic to @Maybe a@.
 Because of this, when @L == 0@ or @M == 0@ in case 3., the type of
 @ret@ is simplified:

     * @ret ≡ Either (u1, …, uL) ()@ is rewritten to @ret ≡ Maybe (u1, …, uL)@.

     * @ret ≡ Either () (v1, …, vM)@ is rewritten to @ret ≡ Maybe (v1, …, vM)@.

-}

{- $examples

<examples/Teletype.lhs Teletype> (regular data type declaration)

<examples/RetryTH.hs Retry> (GADT declaration)

-}
