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
-- Module      :  Control.Monad.Trans.Free
-- Copyright   :  (C) 2008-2013 Edward Kmett
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
  (
  -- * The base functor
    FreeF(..)
  -- * The free monad transformer
  , FreeT(..)
  -- * The free monad
  , Free, free, runFree
  -- * Operations
  , liftF
  , iterT
  , iterTM
  , hoistFreeT
  , transFreeT
  -- * Operations of free monad
  , retract
  , iter
  , iterM
  -- * Free Monads With Class
  , MonadFree(..)
  ) where

import Control.Applicative
import Control.Monad (liftM, MonadPlus(..), ap)
import Control.Monad.Trans.Class
import Control.Monad.Free.Class
import Control.Monad.IO.Class
import Control.Monad.Reader.Class
import Control.Monad.State.Class
import Control.Monad.Error.Class
import Control.Monad.Cont.Class
import Data.Monoid
import Data.Foldable
import Data.Functor.Identity
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
  {-# INLINE fmap #-}

instance Foldable f => Foldable (FreeF f a) where
  foldMap f (Free as) = foldMap f as
  foldMap _ _         = mempty
  {-# INLINE foldMap #-}

instance Traversable f => Traversable (FreeF f a) where
  traverse _ (Pure a)  = pure (Pure a)
  traverse f (Free as) = Free <$> traverse f as
  {-# INLINE traverse #-}

instance Functor f => Bifunctor (FreeF f) where
  bimap f _ (Pure a)  = Pure (f a)
  bimap _ g (Free as) = Free (fmap g as)
  {-# INLINE bimap #-}

instance Foldable f => Bifoldable (FreeF f) where
  bifoldMap f _ (Pure a)  = f a
  bifoldMap _ g (Free as) = foldMap g as
  {-# INLINE bifoldMap #-}

instance Traversable f => Bitraversable (FreeF f) where
  bitraverse f _ (Pure a)  = Pure <$> f a
  bitraverse _ g (Free as) = Free <$> traverse g as
  {-# INLINE bitraverse #-}

transFreeF :: (forall x. f x -> g x) -> FreeF f a b -> FreeF g a b
transFreeF _ (Pure a) = Pure a
transFreeF t (Free as) = Free (t as)
{-# INLINE transFreeF #-}

-- | The \"free monad transformer\" for a functor @f@
newtype FreeT f m a = FreeT { runFreeT :: m (FreeF f a (FreeT f m a)) }

-- | The \"free monad\" for a functor @f@.
type Free f = FreeT f Identity

-- | Evaluates the first layer out of a free monad value.
runFree :: Free f a -> FreeF f a (Free f a)
runFree = runIdentity . runFreeT
{-# INLINE runFree #-}

-- | Pushes a layer into a free monad value.
free :: FreeF f a (Free f a) -> Free f a
free = FreeT . Identity
{-# INLINE free #-}

deriving instance Eq (m (FreeF f a (FreeT f m a))) => Eq (FreeT f m a)
deriving instance Ord (m (FreeF f a (FreeT f m a))) => Ord (FreeT f m a)

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

instance (Functor f, MonadReader r m) => MonadReader r (FreeT f m) where
  ask = lift ask
  {-# INLINE ask #-}
  local f = hoistFreeT (local f)
  {-# INLINE local #-}

instance (Functor f, MonadState s m) => MonadState s (FreeT f m) where
  get = lift get
  {-# INLINE get #-}
  put = lift . put
  {-# INLINE put #-}
#if MIN_VERSION_mtl(2,1,1)
  state f = lift (state f)
  {-# INLINE state #-}
#endif

instance (Functor f, MonadError e m) => MonadError e (FreeT f m) where
  throwError = lift . throwError
  {-# INLINE throwError #-}
  FreeT m `catchError` f = FreeT $ (liftM (fmap (`catchError` f)) m) `catchError` (runFreeT . f)

instance (Functor f, MonadCont m) => MonadCont (FreeT f m) where
  callCC f = FreeT $ callCC (\k -> runFreeT $ f (lift . k . Pure))

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

-- | Tear down a free monad transformer using iteration.
iterT :: (Functor f, Monad m) => (f (m a) -> m a) -> FreeT f m a -> m a
iterT f (FreeT m) = do
    val <- m
    case fmap (iterT f) val of
        Pure x -> return x
        Free y -> f y

-- | Tear down a free monad transformer using iteration over a transformer.
iterTM :: (Functor f, Monad m, MonadTrans t, Monad (t m)) => (f (t m a) -> t m a) -> FreeT f m a -> t m a
iterTM f (FreeT m) = do
    val <- lift m
    case fmap (iterTM f) val of
        Pure x -> return x
        Free y -> f y

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

-- |
-- 'retract' is the left inverse of 'liftF'
--
-- @
-- 'retract' . 'liftF' = 'id'
-- @
retract :: Monad f => Free f a -> f a
retract m =
  case runIdentity (runFreeT m) of
    Pure a  -> return a
    Free as -> as >>= retract

-- | Tear down a 'Free' 'Monad' using iteration.
iter :: Functor f => (f a -> a) -> Free f a -> a
iter phi = runIdentity . iterT (Identity . phi . fmap runIdentity)

-- | Like 'iter' for monadic values.
iterM :: (Functor f, Monad m) => (f (m a) -> m a) -> Free f a -> m a
iterM phi = iterT phi . hoistFreeT (return . runIdentity)

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

