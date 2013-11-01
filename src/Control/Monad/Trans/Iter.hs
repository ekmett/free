{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE DeriveDataTypeable #-}

#ifndef MIN_VERSION_MTL
#define MIN_VERSION_MTL(x,y,z) 1
#endif

-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Trans.Iter
-- Copyright   :  (C) 2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  MPTCs, fundeps
--
-- Based on <http://www.ioc.ee/~tarmo/tday-veskisilla/uustalu-slides.pdf Capretta's Iterative Monad Transformer>
--
-- Unlike 'Free', this is a true monad transformer.
----------------------------------------------------------------------------
module Control.Monad.Trans.Iter
  (
  -- * The iterative monad transformer
    IterT(..)
  -- * Capretta's iterative monad
  , Iter, iter, runIter
  -- * Operations
  , delay
  , hoistIterT
  -- * Consuming iterative monads
  , retract
  , fold
  , foldM
  -- * IterT ~ FreeT Identity
  , MonadFree(..)
  ) where

import Control.Applicative
import Control.Monad (ap, liftM, MonadPlus(..))
import Control.Monad.Fix
import Control.Monad.Trans.Class
import Control.Monad.Free.Class
import Control.Monad.State.Class
import Control.Monad.Reader.Class
import Control.Monad.IO.Class
import Data.Bifunctor
import Data.Bitraversable
import Data.Functor.Bind
import Data.Functor.Identity
import Data.Foldable hiding (fold)
import Data.Traversable
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import Data.Typeable

#ifdef GHC_TYPEABLE
import Data.Data
#endif

-- | The monad supporting iteration based over a base monad @m@.
--
-- @
-- 'IterT' ~ 'FreeT' 'Identity'
-- @
newtype IterT m a = IterT { runIterT :: m (Either a (IterT m a)) }
#if __GLASGOW_HASKELL__ >= 707
  deriving (Typeable)
#endif

type Iter = IterT Identity

iter :: Either a (Iter a) -> Iter a
iter = IterT . Identity
{-# INLINE iter #-}

runIter :: Iter a -> Either a (Iter a)
runIter = runIdentity . runIterT
{-# INLINE runIter #-}

instance Eq (m (Either a (IterT m a))) => Eq (IterT m a) where
  IterT m == IterT n = m == n

instance Ord (m (Either a (IterT m a))) => Ord (IterT m a) where
  compare (IterT m) (IterT n) = compare m n

instance Show (m (Either a (IterT m a))) => Show (IterT m a) where
  showsPrec d (IterT m) = showParen (d > 10) $
    showString "IterT " . showsPrec 11 m

instance Read (m (Either a (IterT m a))) => Read (IterT m a) where
  readsPrec d =  readParen (d > 10) $ \r ->
    [ (IterT m,t) | ("IterT",s) <- lex r, (m,t) <- readsPrec 11 s]

instance Monad m => Functor (IterT m) where
  fmap f = IterT . liftM (bimap f (fmap f)) . runIterT
  {-# INLINE fmap #-}

instance Monad m => Applicative (IterT m) where
  pure = IterT . return . Left
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad m => Monad (IterT m) where
  return = IterT . return . Left
  {-# INLINE return #-}
  IterT m >>= k = IterT $ m >>= either (runIterT . k) (return . Right . (>>= k))
  {-# INLINE (>>=) #-}
  fail = IterT . fail
  {-# INLINE fail #-}

instance Monad m => Apply (IterT m) where
  (<.>) = ap
  {-# INLINE (<.>) #-}

instance Monad m => Bind (IterT m) where
  (>>-) = (>>=)
  {-# INLINE (>>-) #-}

instance MonadFix m => MonadFix (IterT m) where
  mfix f = IterT $ mfix $ runIterT . f . either id (error "mfix (IterT m): Right")
  {-# INLINE mfix #-}

instance MonadPlus m => Alternative (IterT m) where
  empty = IterT mzero
  {-# INLINE empty #-}
  IterT a <|> IterT b = IterT (mplus a b)
  {-# INLINE (<|>) #-}

instance MonadPlus m => MonadPlus (IterT m) where
  mzero = IterT mzero
  {-# INLINE mzero #-}
  IterT a `mplus` IterT b = IterT (mplus a b)
  {-# INLINE mplus #-}

instance MonadTrans IterT where
  lift = IterT . liftM Left
  {-# INLINE lift #-}

instance Foldable m => Foldable (IterT m) where
  foldMap f = foldMap (either f (foldMap f)) . runIterT
  {-# INLINE foldMap #-}

instance Foldable1 m => Foldable1 (IterT m) where
  foldMap1 f = foldMap1 (either f (foldMap1 f)) . runIterT
  {-# INLINE foldMap1 #-}

instance (Monad m, Traversable m) => Traversable (IterT m) where
  traverse f (IterT m) = IterT <$> traverse (bitraverse f (traverse f)) m
  {-# INLINE traverse #-}

instance (Monad m, Traversable1 m) => Traversable1 (IterT m) where
  traverse1 f (IterT m) = IterT <$> traverse1 go m where
    go (Left a) = Left <$> f a
    go (Right a) = Right <$> traverse1 f a
  {-# INLINE traverse1 #-}

instance (Functor m, MonadReader e m) => MonadReader e (IterT m) where
  ask = lift ask
  {-# INLINE ask #-}
  local f = hoistIterT (local f)
  {-# INLINE local #-}

instance (Functor m, MonadState s m) => MonadState s (IterT m) where
  get = lift get
  {-# INLINE get #-}
  put s = lift (put s)
  {-# INLINE put #-}
#if MIN_VERSION_mtl(2,1,1)
  state f = lift (state f)
  {-# INLINE state #-}
#endif

instance (Functor m, MonadIO m) => MonadIO (IterT m) where
  liftIO = lift . liftIO

instance Monad m => MonadFree Identity (IterT m) where
  wrap = IterT . return . Right . runIdentity
  {-# INLINE wrap #-}

delay :: (Monad f, MonadFree f m) => m a -> m a
delay = wrap . return
{-# INLINE delay #-}

-- |
-- 'retract' is the left inverse of 'lift'
--
-- @
-- 'retract' . 'lift' = 'id'
-- @
retract :: Monad m => IterT m a -> m a
retract m = runIterT m >>= either return retract

-- | Tear down a 'Free' 'Monad' using iteration.
fold :: Monad m => (m a -> a) -> IterT m a -> a
fold phi (IterT m) = phi (either id (fold phi) `liftM` m)

-- | Like 'fold' with monadic result.
foldM :: (Monad m, Monad n) => (m (n a) -> n a) -> IterT m a -> n a
foldM phi (IterT m) = phi (either return (foldM phi) `liftM` m)

-- | Lift a monad homomorphism from @m@ to @n@ into a Monad homomorphism from @'IterT' m@ to @'IterT' n@.
hoistIterT :: Monad n => (forall a. m a -> n a) -> IterT m b -> IterT n b
hoistIterT f (IterT as) = IterT (fmap (hoistIterT f) `liftM` f as)

#if defined(GHC_TYPEABLE) && __GLASGOW_HASKELL__ < 707
instance Typeable1 m => Typeable1 (IterT m) where
  typeOf1 t = mkTyConApp freeTyCon [typeOf1 (f t)] where
    f :: IterT m a -> m a
    f = undefined

freeTyCon :: TyCon
#if __GLASGOW_HASKELL__ < 704
freeTyCon = mkTyCon "Control.Monad.Iter.IterT"
#else
freeTyCon = mkTyCon3 "free" "Control.Monad.Iter" "IterT"
#endif
{-# NOINLINE freeTyCon #-}

instance
  ( Typeable1 m, Typeable a
  , Data (m (Either a (IterT m a)))
  , Data a
  ) => Data (IterT m a) where
    gfoldl f z (IterT as) = z IterT `f` as
    toConstr IterT{} = iterConstr
    gunfold k z c = case constrIndex c of
        1 -> k (z IterT)
        _ -> error "gunfold"
    dataTypeOf _ = iterDataType
    dataCast1 f  = gcast1 f

iterConstr :: Constr
iterConstr = mkConstr iterDataType "IterT" [] Prefix
{-# NOINLINE iterConstr #-}

iterDataType :: DataType
iterDataType = mkDataType "Control.Monad.Iter.IterT" [iterConstr]
{-# NOINLINE iterDataType #-}

#endif
