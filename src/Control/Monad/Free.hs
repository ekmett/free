{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Free
-- Copyright   :  (C) 2008-2011 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  MPTCs, fundeps
--
-- Free monads
--
----------------------------------------------------------------------------
module Control.Monad.Free
  ( MonadFree(..)
  , Free(..)
  , retract
  , liftF
  , iter
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
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable

#ifdef GHC_TYPEABLE
import Data.Data
#endif

data Free f a = Pure a | Free (f (Free f a))


instance (Eq (f (Free f a)), Eq a) => Eq (Free f a) where
  Pure a == Pure b = a == b
  Free fa == Free fb = fa == fb
  _ == _ = False

instance (Ord (f (Free f a)), Ord a) => Ord (Free f a) where
  Pure a `compare` Pure b = a `compare` b
  Pure _ `compare` Free _ = LT
  Free _ `compare` Pure _ = GT
  Free fa `compare` Free fb = fa `compare` fb

instance (Show (f (Free f a)), Show a) => Show (Free f a) where
  showsPrec d (Pure a) = showParen (d > 10) $
    showString "Pure " . showsPrec 11 a
  showsPrec d (Free m) = showParen (d > 10) $
    showString "Free " . showsPrec 11 m

instance (Read (f (Free f a)), Read a) => Read (Free f a) where
  readsPrec d r = readParen (d > 10)
      (\r' -> [ (Pure m, t)
             | ("Pure", s) <- lex r'
             , (m, t) <- readsPrec 11 s]) r
    ++ readParen (d > 10)
      (\r' -> [ (Free m, t)
             | ("Free", s) <- lex r'
             , (m, t) <- readsPrec 11 s]) r

instance Functor f => Functor (Free f) where
  fmap f (Pure a)  = Pure (f a)
  fmap f (Free fa) = Free (fmap f <$> fa)

instance Functor f => Apply (Free f) where
  Pure a  <.> Pure b = Pure (a b)
  Pure a  <.> Free fb = Free $ fmap a <$> fb
  Free fa <.> b = Free $ (<.> b) <$> fa

instance Functor f => Applicative (Free f) where
  pure = Pure
  Pure a <*> Pure b = Pure $ a b
  Pure a <*> Free mb = Free $ fmap a <$> mb
  Free ma <*> b = Free $ (<*> b) <$> ma

instance Functor f => Bind (Free f) where
  Pure a >>- f = f a
  Free m >>- f = Free ((>>- f) <$> m)

instance Functor f => Monad (Free f) where
  return = Pure
  Pure a >>= f = f a
  Free m >>= f = Free ((>>= f) <$> m)

-- | This violates the Alternative laws, handle with care.
instance Alternative v => Alternative (Free v) where
  empty = Free empty
  a <|> b = Free (pure a <|> pure b)

-- | This violates the MonadPlus laws, handle with care.
instance (Functor v, MonadPlus v) => MonadPlus (Free v) where
  mzero = Free mzero
  a `mplus` b = Free (return a `mplus` return b)

-- | This is not a true monad transformer. It is only a monad transformer \"up to 'retract'\".
instance MonadTrans Free where
  lift = Free . liftM Pure

instance Foldable f => Foldable (Free f) where
  foldMap f (Pure a) = f a
  foldMap f (Free fa) = foldMap (foldMap f) fa

instance Foldable1 f => Foldable1 (Free f) where
  foldMap1 f (Pure a) = f a
  foldMap1 f (Free fa) = foldMap1 (foldMap1 f) fa

instance Traversable f => Traversable (Free f) where
  traverse f (Pure a) = Pure <$> f a
  traverse f (Free fa) = Free <$> traverse (traverse f) fa

instance Traversable1 f => Traversable1 (Free f) where
  traverse1 f (Pure a) = Pure <$> f a
  traverse1 f (Free fa) = Free <$> traverse1 (traverse1 f) fa

instance (Functor m, MonadWriter e m) => MonadWriter e (Free m) where
  tell = lift . tell
  listen = lift . listen . retract
  pass = lift . pass . retract

instance (Functor m, MonadReader e m) => MonadReader e (Free m) where
  ask = lift ask
  local f = lift . local f . retract

instance (Functor m, MonadState s m) => MonadState s (Free m) where
  get = lift get
  put s = lift (put s)

instance (Functor m, MonadError e m) => MonadError e (Free m) where
  throwError = lift . throwError
  catchError as f = lift (catchError (retract as) (retract . f))

instance (Functor m, MonadCont m) => MonadCont (Free m) where
  callCC f = lift (callCC (retract . f . liftM lift))

liftF :: Functor f => f a -> Free f a
liftF = Free . fmap Pure

instance Functor f => MonadFree f (Free f) where
  wrap = Free

-- |
-- @
-- 'retract' . 'lift' = 'id'
-- 'retract' . 'liftF' = 'id'
-- @
retract :: Monad f => Free f a -> f a
retract (Pure a) = return a
retract (Free as) = as >>= retract

iter :: Functor f => (f a -> a) -> Free f a -> a
iter _ (Pure a) = a
iter phi (Free m) = phi (iter phi <$> m)

#ifdef GHC_TYPEABLE
instance Typeable1 f => Typeable1 (Free f) where
  typeOf1 t = mkTyConApp freeTyCon [typeOf1 (f t)] where
    f :: Free f a -> f a
    f = undefined

freeTyCon :: TyCon
#if __GLASGOW_HASKELL__ < 704
freeTyCon = mkTyCon "Control.Monad.Free.Free"
#else
freeTyCon = mkTyCon3 "free" "Control.Monad.Free" "Free"
#endif
{-# NOINLINE freeTyCon #-}

instance
  ( Typeable1 f, Typeable a
  , Data a, Data (f (Free f a))
  ) => Data (Free f a) where
    gfoldl f z (Pure a) = z Pure `f` a
    gfoldl f z (Free as) = z Free `f` as
    toConstr Pure{} = pureConstr
    toConstr Free{} = freeConstr
    gunfold k z c = case constrIndex c of
        1 -> k (z Pure)
        2 -> k (z Free)
        _ -> error "gunfold"
    dataTypeOf _ = freeDataType
    dataCast1 f = gcast1 f

pureConstr, freeConstr :: Constr
pureConstr = mkConstr freeDataType "Pure" [] Prefix
freeConstr = mkConstr freeDataType "Free" [] Prefix
{-# NOINLINE pureConstr #-}
{-# NOINLINE freeConstr #-}

freeDataType :: DataType
freeDataType = mkDataType "Control.Monad.Free.FreeF" [pureConstr, freeConstr]
{-# NOINLINE freeDataType #-}

#endif
