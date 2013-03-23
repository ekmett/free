{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
#if __GLASGOW_HASKELL__ >= 707
{-# LANGUAGE DeriveDataTypeable #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Trans.Free
-- Copyright   :  (C) 2008-2012 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  MPTCs, fundeps
--
-- The free monad transformer
--
----------------------------------------------------------------------------
module Control.Monad.Trans.Free
  ( FreeF(..)
  , FreeT(..)
  , MonadFree(..)
  , liftF
  , hoistFreeT
  , transFreeT
  ) where

import Control.Applicative
import Control.Monad (liftM, MonadPlus(..), ap)
import Control.Monad.Trans.Class
import Control.Monad.Free.Class
import Control.Monad.IO.Class
import Data.Monoid
import Data.Foldable
import Data.Traversable
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
#ifdef GHC_TYPEABLE
import Data.Data
#endif

-- | The base functor for a free monad.
data FreeF f a b = Pure a | Free (f b)
  deriving (Eq,Ord,Show,Read
#if __GLASGOW_HASKELL__ >= 707
           ,Typeable
#endif
           )

instance Functor f => Functor (FreeF f a) where
  fmap _ (Pure a)  = Pure a
  fmap f (Free as) = Free (fmap f as)

instance Foldable f => Foldable (FreeF f a) where
  foldMap f (Free as) = foldMap f as
  foldMap _ _         = mempty

instance Traversable f => Traversable (FreeF f a) where
  traverse _ (Pure a)  = pure (Pure a)
  traverse f (Free as) = Free <$> traverse f as

instance Functor f => Bifunctor (FreeF f) where
  bimap f _ (Pure a)  = Pure (f a)
  bimap _ g (Free as) = Free (fmap g as)

instance Foldable f => Bifoldable (FreeF f) where
  bifoldMap f _ (Pure a)  = f a
  bifoldMap _ g (Free as) = foldMap g as

instance Traversable f => Bitraversable (FreeF f) where
  bitraverse f _ (Pure a)  = Pure <$> f a
  bitraverse _ g (Free as) = Free <$> traverse g as

transFreeF :: (forall x. f x -> g x) -> FreeF f a b -> FreeF g a b
transFreeF _ (Pure a) = Pure a
transFreeF t (Free as) = Free (t as)
{-# INLINE transFreeF #-}

-- | The \"free monad transformer\" for a functor @f@.
newtype FreeT f m a = FreeT { runFreeT :: m (FreeF f a (FreeT f m a)) }

instance Eq (m (FreeF f a (FreeT f m a))) => Eq (FreeT f m a) where
  FreeT m == FreeT n = m == n

instance Ord (m (FreeF f a (FreeT f m a))) => Ord (FreeT f m a) where
  compare (FreeT m) (FreeT n) = compare m n

instance Show (m (FreeF f a (FreeT f m a))) => Show (FreeT f m a) where
  showsPrec d (FreeT m) = showParen (d > 10) $
    showString "FreeT " . showsPrec 11 m

instance Read (m (FreeF f a (FreeT f m a))) => Read (FreeT f m a) where
  readsPrec d =  readParen (d > 10) $ \r ->
    [ (FreeT m,t) | ("FreeT",s) <- lex r, (m,t) <- readsPrec 11 s]

instance (Functor f, Monad m) => Functor (FreeT f m) where
  fmap f (FreeT m) = FreeT (liftM f' m) where
    f' (Pure a)  = Pure (f a)
    f' (Free as) = Free (fmap (fmap f) as)

instance (Functor f, Monad m) => Applicative (FreeT f m) where
  pure a = FreeT (return (Pure a))
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance (Functor f, Monad m) => Monad (FreeT f m) where
  return a = FreeT (return (Pure a))
  {-# INLINE return #-}
  FreeT m >>= f = FreeT $ m >>= \v -> case v of
    Pure a -> runFreeT (f a)
    Free w -> return (Free (fmap (>>= f) w))

instance MonadTrans (FreeT f) where
  lift = FreeT . liftM Pure
  {-# INLINE lift #-}

instance (Functor f, MonadIO m) => MonadIO (FreeT f m) where
  liftIO = lift . liftIO
  {-# INLINE liftIO #-}

instance (Functor f, MonadPlus m) => Alternative (FreeT f m) where
  empty = FreeT mzero
  FreeT ma <|> FreeT mb = FreeT (mplus ma mb)
  {-# INLINE (<|>) #-}

instance (Functor f, MonadPlus m) => MonadPlus (FreeT f m) where
  mzero = FreeT mzero
  {-# INLINE mzero #-}
  mplus (FreeT ma) (FreeT mb) = FreeT (mplus ma mb)
  {-# INLINE mplus #-}

instance (Functor f, Monad m) => MonadFree f (FreeT f m) where
  wrap = FreeT . return . Free
  {-# INLINE wrap #-}

-- | FreeT is a functor from the category of functors to the category of monads.
--
-- This provides the mapping.
liftF :: (Functor f, Monad m) => f a -> FreeT f m a
liftF = wrap . fmap return
{-# INLINE liftF #-}

instance (Foldable m, Foldable f) => Foldable (FreeT f m) where
  foldMap f (FreeT m) = foldMap (bifoldMap f (foldMap f)) m

instance (Monad m, Traversable m, Traversable f) => Traversable (FreeT f m) where
  traverse f (FreeT m) = FreeT <$> traverse (bitraverse f (traverse f)) m

-- | Lift a monad homomorphism from @m@ to @n@ into a monad homomorphism from @'FreeT' f m@ to @'FreeT' f n@
--
-- @'hoistFreeT' :: ('Monad' m, 'Functor' f) => (m ~> n) -> 'FreeT' f m ~> 'FreeT' f n@
hoistFreeT :: (Monad m, Functor f) => (forall a. m a -> n a) -> FreeT f m b -> FreeT f n b
hoistFreeT mh = FreeT . mh . liftM (fmap (hoistFreeT mh)) . runFreeT

-- | Lift a natural transformation from @f@ to @g@ into a monad homomorphism from @'FreeT' f m@ to @'FreeT' g n@
transFreeT :: (Monad m, Functor g) => (forall a. f a -> g a) -> FreeT f m b -> FreeT g m b
transFreeT nt = FreeT . liftM (fmap (transFreeT nt) . transFreeF nt) . runFreeT

#if defined(GHC_TYPEABLE) && __GLASGOW_HASKELL__ < 707
instance Typeable1 f => Typeable2 (FreeF f) where
  typeOf2 t = mkTyConApp freeFTyCon [typeOf1 (f t)] where
    f :: FreeF f a b -> f a
    f = undefined

instance (Typeable1 f, Typeable1 w) => Typeable1 (FreeT f w) where
  typeOf1 t = mkTyConApp freeTTyCon [typeOf1 (f t), typeOf1 (w t)] where
    f :: FreeT f w a -> f a
    f = undefined
    w :: FreeT f w a -> w a
    w = undefined

freeFTyCon, freeTTyCon :: TyCon
#if __GLASGOW_HASKELL__ < 704
freeTTyCon = mkTyCon "Control.Monad.Trans.Free.FreeT"
freeFTyCon = mkTyCon "Control.Monad.Trans.Free.FreeF"
#else
freeTTyCon = mkTyCon3 "free" "Control.Monad.Trans.Free" "FreeT"
freeFTyCon = mkTyCon3 "free" "Control.Monad.Trans.Free" "FreeF"
#endif
{-# NOINLINE freeTTyCon #-}
{-# NOINLINE freeFTyCon #-}

instance
  ( Typeable1 f, Typeable a, Typeable b
  , Data a, Data (f b), Data b
  ) => Data (FreeF f a b) where
    gfoldl f z (Pure a) = z Pure `f` a
    gfoldl f z (Free as) = z Free `f` as
    toConstr Pure{} = pureConstr
    toConstr Free{} = freeConstr
    gunfold k z c = case constrIndex c of
        1 -> k (z Pure)
        2 -> k (z Free)
        _ -> error "gunfold"
    dataTypeOf _ = freeFDataType
    dataCast1 f = gcast1 f

instance
  ( Typeable1 f, Typeable1 w, Typeable a
  , Data (w (FreeF f a (FreeT f w a)))
  , Data a
  ) => Data (FreeT f w a) where
    gfoldl f z (FreeT w) = z FreeT `f` w
    toConstr _ = freeTConstr
    gunfold k z c = case constrIndex c of
        1 -> k (z FreeT)
        _ -> error "gunfold"
    dataTypeOf _ = freeTDataType
    dataCast1 f = gcast1 f

pureConstr, freeConstr, freeTConstr :: Constr
pureConstr = mkConstr freeFDataType "Pure" [] Prefix
freeConstr = mkConstr freeFDataType "Free" [] Prefix
freeTConstr = mkConstr freeTDataType "FreeT" [] Prefix
{-# NOINLINE pureConstr #-}
{-# NOINLINE freeConstr #-}
{-# NOINLINE freeTConstr #-}

freeFDataType, freeTDataType :: DataType
freeFDataType = mkDataType "Control.Monad.Trans.Free.FreeF" [pureConstr, freeConstr]
freeTDataType = mkDataType "Control.Monad.Trans.Free.FreeT" [freeTConstr]
{-# NOINLINE freeFDataType #-}
{-# NOINLINE freeTDataType #-}
#endif

