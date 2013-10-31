{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE Rank2Types #-}
#if __GLASGOW_HASKELL__ >= 707
{-# LANGUAGE DeriveDataTypeable #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Iter
-- Copyright   :  (C) 2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  MPTCs, fundeps
--
-- Monads for free
----------------------------------------------------------------------------
module Control.Monad.Iter
  ( MonadFree(..)
  , Iter(..)
  , retract
  , iter
  , hoistIter
  ) where

import Control.Applicative
import Control.Monad (ap, liftM, MonadPlus(..))
import Control.Monad.Fix
import Control.Monad.Trans.Class
import Control.Monad.Free.Class
-- import Control.Monad.Reader.Class
-- import Control.Monad.Writer.Class
import Control.Monad.State.Class
-- import Control.Monad.Error.Class
-- import Control.Monad.Cont.Class
import Data.Bifunctor
import Data.Bitraversable
import Data.Functor.Bind
import Data.Foldable
import Data.Traversable
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable

#ifdef GHC_TYPEABLE
import Data.Data
#endif

data Iter m a = Iter { runIter :: m (Either a (Iter m a)) }
#if __GLASGOW_HASKELL__ >= 707
  deriving (Typeable)
#endif

deriving instance Eq (m (Either a (Iter m a))) => Eq (Iter m a)
deriving instance Ord (m (Either a (Iter m a))) => Ord (Iter m a)
deriving instance Show (m (Either a (Iter m a))) => Show (Iter m a)
deriving instance Read (m (Either a (Iter m a))) => Read (Iter m a)

instance Monad m => Functor (Iter m) where
  fmap f = Iter . liftM (bimap f (fmap f)) . runIter
  {-# INLINE fmap #-}

instance Monad m => Applicative (Iter m) where
  pure = Iter . return . Left
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad m => Monad (Iter m) where
  return = Iter . return . Left
  {-# INLINE return #-}
  Iter m >>= k = Iter $ m >>= either (runIter . k) (return . Right . (>>= k))
  {-# INLINE (>>=) #-}
  fail = Iter . fail
  {-# INLINE fail #-}

instance Monad m => Apply (Iter m) where
  (<.>) = ap
  {-# INLINE (<.>) #-}

instance Monad m => Bind (Iter m) where
  (>>-) = (>>=)
  {-# INLINE (>>-) #-}

instance MonadFix m => MonadFix (Iter m) where
  mfix f = Iter $ mfix (runIter . f . unLeft) where
    unLeft (Left x)  = x
    unLeft (Right _) = error "mfix (Iter m): Right"
  {-# INLINE mfix #-}

instance MonadPlus m => Alternative (Iter m) where
  empty = Iter mzero
  {-# INLINE empty #-}
  Iter a <|> Iter b = Iter (mplus a b)
  {-# INLINE (<|>) #-}

instance MonadPlus m => MonadPlus (Iter m) where
  mzero = Iter mzero
  {-# INLINE mzero #-}
  Iter a `mplus` Iter b = Iter (mplus a b)
  {-# INLINE mplus #-}

-- | This is not a true monad transformer. It is only a monad transformer \"up to 'retract'\".
instance MonadTrans Iter where
  lift = Iter . liftM Left
  {-# INLINE lift #-}

instance Foldable m => Foldable (Iter m) where
  foldMap f = foldMap (either f (foldMap f)) . runIter
  {-# INLINE foldMap #-}

instance Foldable1 m => Foldable1 (Iter m) where
  foldMap1 f = foldMap1 (either f (foldMap1 f)) . runIter
  {-# INLINE foldMap1 #-}

instance (Monad m, Traversable m) => Traversable (Iter m) where
  traverse f (Iter m) = Iter <$> traverse (bitraverse f (traverse f)) m
  {-# INLINE traverse #-}

instance (Monad m, Traversable1 m) => Traversable1 (Iter m) where
  traverse1 f (Iter m) = Iter <$> traverse1 go m where
    go (Left a) = Left <$> f a
    go (Right a) = Right <$> traverse1 f a
  {-# INLINE traverse1 #-}

{-
instance MonadWriter e m => MonadWriter e (Iter m) where
  tell = lift . tell
  {-# INLINE tell #-}
  listen = lift . listen . retract
  {-# INLINE listen #-}
  pass = lift . pass . retract
  {-# INLINE pass #-}

instance (Functor m, MonadReader e m) => MonadReader e (Free m) where
  ask = lift ask
  {-# INLINE ask #-}
  local f = lift . local f . retract
  {-# INLINE local #-}
-}

instance (Functor m, MonadState s m) => MonadState s (Iter m) where
  get = lift get
  {-# INLINE get #-}
  put s = lift (put s)
  {-# INLINE put #-}

{-
instance (Functor m, MonadError e m) => MonadError e (Free m) where
  throwError = lift . throwError
  {-# INLINE throwError #-}
  catchError as f = lift (catchError (retract as) (retract . f))
  {-# INLINE catchError #-}

instance (Functor m, MonadCont m) => MonadCont (Free m) where
  callCC f = lift (callCC (retract . f . liftM lift))
  {-# INLINE callCC #-}
-}

instance Monad m => MonadFree m (Iter m) where
  wrap mi = Iter (mi >>= runIter)
  {-# INLINE wrap #-}

-- |
-- 'retract' is the left inverse of 'lift'
--
-- @
-- 'retract' . 'lift' = 'id'
-- @
retract :: Monad m => Iter m a -> m a
retract m = runIter m >>= either return retract

-- | Tear down a 'Free' 'Monad' using iteration.
iter :: Monad m => (m a -> a) -> Iter m a -> a
iter phi (Iter m) = phi (either id (iter phi) `liftM` m)

-- | Lift a monad homomorphism from @m@ to @n@ into a Monad homomorphism from @'Iter' m@ to @'Iter' n@.
hoistIter :: Monad n => (forall a. m a -> n a) -> Iter m b -> Iter n b
hoistIter f (Iter as) = Iter (fmap (hoistIter f) `liftM` f as)

#if defined(GHC_TYPEABLE) && __GLASGOW_HASKELL__ < 707
instance Typeable1 m => Typeable1 (Iter m) where
  typeOf1 t = mkTyConApp freeTyCon [typeOf1 (f t)] where
    f :: Iter m a -> m a
    f = undefined

freeTyCon :: TyCon
#if __GLASGOW_HASKELL__ < 704
freeTyCon = mkTyCon "Control.Monad.Iter.Iter"
#else
freeTyCon = mkTyCon3 "free" "Control.Monad.Iter" "Iter"
#endif
{-# NOINLINE freeTyCon #-}

instance
  ( Typeable1 m, Typeable a
  , Data (m (Either a (Iter m a)))
  , Data a
  ) => Data (Iter m a) where
    gfoldl f z (Iter as) = z Iter `f` as
    toConstr Iter{} = iterConstr
    gunfold k z c = case constrIndex c of
        1 -> k (z Iter)
        _ -> error "gunfold"
    dataTypeOf _ = iterDataType
    dataCast1 f  = gcast1 f

iterConstr :: Constr
iterConstr = mkConstr iterDataType "Iter" [] Prefix
{-# NOINLINE iterConstr #-}

iterDataType :: DataType
iterDataType = mkDataType "Control.Monad.Iter.Iter" [iterConstr]
{-# NOINLINE iterDataType #-}

#endif
