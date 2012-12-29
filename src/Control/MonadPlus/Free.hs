{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.MonadPlus.Free
-- Copyright   :  (C) 2008-2012 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  MPTCs, fundeps
--
-- left-distributive MonadPlus for free.
----------------------------------------------------------------------------
module Control.MonadPlus.Free
  ( MonadFree(..)
  , Free(..)
  , retract
  , liftF
  , iter
  , hoistFree
  ) where

import Control.Applicative
import Control.Monad (liftM, MonadPlus(..))
import Control.Monad.Trans.Class
import Control.Monad.Free.Class
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class
import Control.Monad.State.Class
import Control.Monad.Error.Class
import Control.Monad.Cont.Class
import Data.Functor.Bind
import Data.Foldable
import Data.Traversable
import Data.Semigroup

#ifdef GHC_TYPEABLE
import Data.Data
#endif

-- | The 'Free' 'MonadPlus' for a 'Functor' @f@.
--
-- /Formally/
--
-- A 'MonadPlus' @n@ is a free 'MonadPlus' for @f@ if every monadplus homomorphism
-- from @n@ to another MonadPlus @m@ is equivalent to a natural transformation
-- from @f@ to @m@.
--
-- We model this internally as if left-distribution holds.
--
-- <<http://www.haskell.org/haskellwiki/MonadPlus>>
data Free f a
  = Pure a
  | Free (f (Free f a))
  | Plus [Free f a]

instance (Eq (f (Free f a)), Eq a) => Eq (Free f a) where
  Pure a == Pure b = a == b
  Free fa == Free fb = fa == fb
  Plus as == Plus bs = as == bs
  _ == _ = False

instance (Ord (f (Free f a)), Ord a) => Ord (Free f a) where
  Pure a `compare` Pure b = a `compare` b
  Pure _ `compare` Free _ = LT
  Pure _ `compare` Plus _ = LT
  Free _ `compare` Pure _ = GT
  Free fa `compare` Free fb = fa `compare` fb
  Free _ `compare` Plus _ = LT
  Plus _ `compare` Pure _ = GT
  Plus _ `compare` Free _ = GT
  Plus as `compare` Plus bs = as `compare` bs

instance (Show (f (Free f a)), Show a) => Show (Free f a) where
  showsPrec d (Pure a) = showParen (d > 10) $
    showString "Pure " . showsPrec 11 a
  showsPrec d (Free m) = showParen (d > 10) $
    showString "Free " . showsPrec 11 m
  showsPrec d (Plus as) = showParen (d > 10) $
    showString "Plus " . showsPrec 11 as

instance (Read (f (Free f a)), Read a) => Read (Free f a) where
  readsPrec d r = readParen (d > 10)
      (\r' -> [ (Pure m, t)
             | ("Pure", s) <- lex r'
             , (m, t) <- readsPrec 11 s]) r
    ++ readParen (d > 10)
      (\r' -> [ (Free m, t)
             | ("Free", s) <- lex r'
             , (m, t) <- readsPrec 11 s]) r
    ++ readParen (d > 10)
      (\r' -> [ (Plus as, t)
             | ("Plus", s) <- lex r'
             , (as, t) <- readsPrec 11 s]) r

instance Functor f => Functor (Free f) where
  fmap f = go where
    go (Pure a)  = Pure (f a)
    go (Free fa) = Free (go <$> fa)
    go (Plus as) = Plus (map go as)
  {-# INLINE fmap #-}

instance Functor f => Apply (Free f) where
  Pure f  <.> Pure b = Pure (f b)
  Pure f  <.> Plus bs = Plus $ fmap f <$> bs
  Pure f  <.> Free fb = Free $ fmap f <$> fb
  Free ff <.> b = Free $ (<.> b) <$> ff
  Plus fs <.> b = Plus $ (<.> b) <$> fs -- left distribution ???

instance Functor f => Applicative (Free f) where
  pure = Pure
  {-# INLINE pure #-}
  Pure f  <*> Pure b  = Pure (f b)
  Pure f  <*> Free mb = Free $ fmap f <$> mb
  Pure f  <*> Plus bs = Plus $ fmap f <$> bs
  Free ff <*> b = Free $ (<*> b) <$> ff
  Plus fs <*> b = Plus $ (<*> b) <$> fs -- left distribution

instance Functor f => Bind (Free f) where
  Pure a >>- f = f a
  Free m >>- f = Free ((>>- f) <$> m)
  Plus m >>- f = Plus ((>>- f) <$> m)

instance Functor f => Monad (Free f) where
  return = Pure
  {-# INLINE return #-}
  Pure a >>= f = f a
  Free m >>= f = Free ((>>= f) <$> m)
  Plus m >>= f = Plus (map (>>= f) m) -- left distribution law

instance Functor f => Alternative (Free f) where
  empty = Plus []
  {-# INLINE empty #-}
  Plus [] <|> r       = r
  l       <|> Plus [] = l
  Plus as <|> Plus bs = Plus (as ++ bs)
  a       <|> b       = Plus [a, b]
  {-# INLINE (<|>) #-}

instance Functor f => MonadPlus (Free f) where
  mzero = empty
  {-# INLINE mzero #-}
  mplus = (<|>)
  {-# INLINE mplus #-}

instance Functor f => Semigroup (Free f a) where
  (<>) = (<|>)
  {-# INLINE (<>) #-}

instance Functor f => Monoid (Free f a) where
  mempty = empty
  {-# INLINE mempty #-}
  mappend = (<|>)
  {-# INLINE mappend #-}
  mconcat as = from (as >>= to)
    where
      to (Plus xs) = xs
      to x       = [x]
      from [x] = x
      from xs  = Plus xs
  {-# INLINE mconcat #-}

-- | This is not a true monad transformer. It is only a monad transformer \"up to 'retract'\".
instance MonadTrans Free where
  lift = Free . liftM Pure
  {-# INLINE lift #-}

instance Foldable f => Foldable (Free f) where
  foldMap f = go where
    go (Pure a) = f a
    go (Free fa) = foldMap go fa
    go (Plus as) = foldMap go as
  {-# INLINE foldMap #-}

instance Traversable f => Traversable (Free f) where
  traverse f = go where
    go (Pure a) = Pure <$> f a
    go (Free fa) = Free <$> traverse go fa
    go (Plus as) = Plus <$> traverse go as
  {-# INLINE traverse #-}

instance (Functor m, MonadPlus m, MonadWriter e m) => MonadWriter e (Free m) where
  tell = lift . tell
  {-# INLINE tell #-}
  listen = lift . listen . retract
  {-# INLINE listen #-}
  pass = lift . pass . retract
  {-# INLINE pass #-}

instance (Functor m, MonadPlus m, MonadReader e m) => MonadReader e (Free m) where
  ask = lift ask
  {-# INLINE ask #-}
  local f = lift . local f . retract
  {-# INLINE local #-}

instance (Functor m, MonadState s m) => MonadState s (Free m) where
  get = lift get
  {-# INLINE get #-}
  put s = lift (put s)
  {-# INLINE put #-}

instance (Functor m, MonadPlus m, MonadError e m) => MonadError e (Free m) where
  throwError = lift . throwError
  {-# INLINE throwError #-}
  catchError as f = lift (catchError (retract as) (retract . f))
  {-# INLINE catchError #-}

instance (Functor m, MonadPlus m, MonadCont m) => MonadCont (Free m) where
  callCC f = lift (callCC (retract . f . liftM lift))
  {-# INLINE callCC #-}

-- | A version of 'lift' that can be used with just a 'Functor' for @f@.
liftF :: Functor f => f a -> Free f a
liftF = Free . fmap Pure
{-# INLINE liftF #-}

instance Functor f => MonadFree f (Free f) where
  wrap = Free
  {-# INLINE wrap #-}

-- |
-- 'retract' is the left inverse of 'lift' and 'liftF'
--
-- @
-- 'retract' . 'lift' = 'id'
-- 'retract' . 'liftF' = 'id'
-- @
retract :: MonadPlus f => Free f a -> f a
retract (Pure a) = return a
retract (Free as) = as >>= retract
retract (Plus as) = Prelude.foldr (mplus . retract) mzero as

-- | Tear down a 'Free' 'Monad' using iteration.
iter :: Functor f => (f a -> a) -> ([a] -> a) -> Free f a -> a
iter phi psi = go where
  go (Pure a) = a
  go (Free as) = phi (go <$> as)
  go (Plus as) = psi (go <$> as)
{-# INLINE iter #-}

-- | Lift a natural transformation from @f@ to @g@ into a natural transformation from @'FreeT' f@ to @'FreeT' g@.
hoistFree :: Functor g => (forall a. f a -> g a) -> Free f b -> Free g b
hoistFree f = go where
  go (Pure a)  = Pure a
  go (Free as) = Free (go <$> f as)
  go (Plus as) = Plus (map go as)

#ifdef GHC_TYPEABLE
instance Typeable1 f => Typeable1 (Free f) where
  typeOf1 t = mkTyConApp freeTyCon [typeOf1 (f t)] where
    f :: Free f a -> f a
    f = undefined

freeTyCon :: TyCon
#if __GLASGOW_HASKELL__ < 704
freeTyCon = mkTyCon "Control.MonadPlus.Free.Free"
#else
freeTyCon = mkTyCon3 "free" "Control.MonadPlus.Free" "Free"
#endif
{-# NOINLINE freeTyCon #-}

instance
  ( Typeable1 f, Typeable a
  , Data a, Data (f (Free f a))
  ) => Data (Free f a) where
    gfoldl f z (Pure a) = z Pure `f` a
    gfoldl f z (Free as) = z Free `f` as
    gfoldl f z (Plus as) = z Plus `f` as
    toConstr Pure{} = pureConstr
    toConstr Free{} = freeConstr
    toConstr Plus{} = plusConstr
    gunfold k z c = case constrIndex c of
        1 -> k (z Pure)
        2 -> k (z Free)
        3 -> k (z Plus)
        _ -> error "gunfold"
    dataTypeOf _ = freeDataType
    dataCast1 f = gcast1 f

pureConstr, freeConstr, plusConstr :: Constr
pureConstr = mkConstr freeDataType "Pure" [] Prefix
freeConstr = mkConstr freeDataType "Free" [] Prefix
plusConstr = mkConstr freeDataType "Plus" [] Prefix
{-# NOINLINE pureConstr #-}
{-# NOINLINE freeConstr #-}

freeDataType :: DataType
freeDataType = mkDataType "Control.MonadPlus.Free.Free" [pureConstr, freeConstr, plusConstr]
{-# NOINLINE freeDataType #-}

#endif
