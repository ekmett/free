{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE Safe #-}

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
  , foldFreeT
  , transFreeT
  , joinFreeT
  , cutoff
  , partialIterT
  , intersperseT
  , intercalateT
  , retractT
  -- * Operations of free monad
  , retract
  , iter
  , iterM
  -- * Free Monads With Class
  , MonadFree(..)
  ) where

import Control.Applicative
import Control.Monad (liftM, MonadPlus(..), ap, join)
import Control.Monad.Base (MonadBase(..))
import Control.Monad.Catch (MonadThrow(..), MonadCatch(..))
import Control.Monad.Trans.Class
import Control.Monad.Free.Class
import qualified Control.Monad.Fail as Fail
import Control.Monad.IO.Class
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class
import Control.Monad.State.Class
import Control.Monad.Error.Class
import Control.Monad.Cont.Class
import Data.Functor.Bind hiding (join)
import Data.Functor.Classes
import Data.Functor.Identity
import Data.Traversable
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Data
import GHC.Generics

-- | The base functor for a free monad.
data FreeF f a b = Pure a | Free (f b)
  deriving (Eq,Ord,Show,Read,Generic,Generic1,Data)

instance Show1 f => Show2 (FreeF f) where
  liftShowsPrec2 spa _sla _spb _slb d (Pure a) =
    showsUnaryWith spa "Pure" d a
  liftShowsPrec2 _spa _sla spb slb d (Free as) =
    showsUnaryWith (liftShowsPrec spb slb) "Free" d as

instance (Show1 f, Show a) => Show1 (FreeF f a) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList

instance Read1 f => Read2 (FreeF f) where
  liftReadsPrec2 rpa _rla rpb rlb = readsData $
    readsUnaryWith rpa "Pure" Pure `mappend`
    readsUnaryWith (liftReadsPrec rpb rlb) "Free" Free

instance (Read1 f, Read a) => Read1 (FreeF f a) where
  liftReadsPrec = liftReadsPrec2 readsPrec readList

instance Eq1 f => Eq2 (FreeF f) where
  liftEq2 eq _ (Pure a) (Pure b) = eq a b
  liftEq2 _ eq (Free as) (Free bs) = liftEq eq as bs
  liftEq2 _ _ _ _ = False

instance (Eq1 f, Eq a) => Eq1 (FreeF f a) where
  liftEq = liftEq2 (==)

instance Ord1 f => Ord2 (FreeF f) where
  liftCompare2 cmp _ (Pure a) (Pure b) = cmp a b
  liftCompare2 _ _ (Pure _) (Free _) = LT
  liftCompare2 _ _ (Free _) (Pure _) = GT
  liftCompare2 _ cmp (Free fa) (Free fb) = liftCompare cmp fa fb

instance (Ord1 f, Ord a) => Ord1 (FreeF f a) where
  liftCompare = liftCompare2 compare

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

instance (Eq1 f, Eq1 m, Eq a) => Eq (FreeT f m a) where
    (==) = eq1

instance (Eq1 f, Eq1 m) => Eq1 (FreeT f m) where
  liftEq eq = go
    where
      go (FreeT x) (FreeT y) = liftEq (liftEq2 eq go) x y

instance (Ord1 f, Ord1 m, Ord a) => Ord (FreeT f m a) where
    compare = compare1

instance (Ord1 f, Ord1 m) => Ord1 (FreeT f m) where
  liftCompare cmp = go
    where
      go (FreeT x) (FreeT y) = liftCompare (liftCompare2 cmp go) x y

instance (Show1 f, Show1 m) => Show1 (FreeT f m) where
  liftShowsPrec sp sl = go
    where
      goList = liftShowList sp sl
      go d (FreeT x) = showsUnaryWith
        (liftShowsPrec (liftShowsPrec2 sp sl go goList) (liftShowList2 sp sl go goList))
        "FreeT" d x

instance (Show1 f, Show1 m, Show a) => Show (FreeT f m a) where
  showsPrec = showsPrec1

instance (Read1 f, Read1 m) => Read1 (FreeT f m) where
  liftReadsPrec rp rl = go
    where
      goList = liftReadList rp rl
      go = readsData $ readsUnaryWith
        (liftReadsPrec (liftReadsPrec2 rp rl go goList) (liftReadList2 rp rl go goList))
        "FreeT" FreeT

instance (Read1 f, Read1 m, Read a) => Read (FreeT f m a) where
  readsPrec = readsPrec1

instance (Functor f, Monad m) => Functor (FreeT f m) where
  fmap f (FreeT m) = FreeT (liftM f' m) where
    f' (Pure a)  = Pure (f a)
    f' (Free as) = Free (fmap (fmap f) as)

instance (Functor f, Monad m) => Applicative (FreeT f m) where
  pure a = FreeT (return (Pure a))
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance (Functor f, Monad m) => Apply (FreeT f m) where
  (<.>) = (<*>)

instance (Functor f, Monad m) => Bind (FreeT f m) where
  (>>-) = (>>=)

instance (Functor f, Monad m) => Monad (FreeT f m) where
  return = pure
  {-# INLINE return #-}
  FreeT m >>= f = FreeT $ m >>= \v -> case v of
    Pure a -> runFreeT (f a)
    Free w -> return (Free (fmap (>>= f) w))

#if !MIN_VERSION_base(4,13,0)
  fail e = FreeT (fail e)
#endif

instance (Functor f, Fail.MonadFail m) => Fail.MonadFail (FreeT f m) where
  fail e = FreeT (Fail.fail e)

instance Functor f => MonadTrans (FreeT f) where
  lift = FreeT . liftM Pure
  {-# INLINE lift #-}

instance (Functor f, MonadIO m) => MonadIO (FreeT f m) where
  liftIO = lift . liftIO
  {-# INLINE liftIO #-}

instance (Functor f, MonadBase b m) => MonadBase b (FreeT f m) where
  liftBase = lift . liftBase
  {-# INLINE liftBase #-}

instance (Functor f, Functor m, MonadReader r m) => MonadReader r (FreeT f m) where
  ask = lift ask
  {-# INLINE ask #-}
  local f = hoistFreeT (local f)
  {-# INLINE local #-}

instance (Functor f, Functor m, MonadWriter w m) => MonadWriter w (FreeT f m) where
  tell = lift . tell
  {-# INLINE tell #-}
  listen (FreeT m) = FreeT $ liftM concat' $ listen (fmap listen `liftM` m)
    where
      concat' (Pure x, w) = Pure (x, w)
      concat' (Free y, w) = Free $ fmap (second (w `mappend`)) <$> y
  pass m = FreeT . pass' . runFreeT . hoistFreeT clean $ listen m
    where
      clean = pass . liftM (\x -> (x, const mempty))
      pass' = join . liftM g
      g (Pure ((x, f), w)) = tell (f w) >> return (Pure x)
      g (Free f)           = return . Free . fmap (FreeT . pass' . runFreeT) $ f
  writer w = lift (writer w)
  {-# INLINE writer #-}

instance (Functor f, MonadState s m) => MonadState s (FreeT f m) where
  get = lift get
  {-# INLINE get #-}
  put = lift . put
  {-# INLINE put #-}
  state f = lift (state f)
  {-# INLINE state #-}

instance (Functor f, MonadError e m) => MonadError e (FreeT f m) where
  throwError = lift . throwError
  {-# INLINE throwError #-}
  FreeT m `catchError` f = FreeT $ liftM (fmap (`catchError` f)) m `catchError` (runFreeT . f)

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

instance (Functor f, MonadThrow m) => MonadThrow (FreeT f m) where
  throwM = lift . throwM
  {-# INLINE throwM #-}

instance (Functor f, MonadCatch m) => MonadCatch (FreeT f m) where
  FreeT m `catch` f = FreeT $ liftM (fmap (`Control.Monad.Catch.catch` f)) m
                                `Control.Monad.Catch.catch` (runFreeT . f)
  {-# INLINE catch #-}

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
-- @'hoistFreeT' :: ('Functor' m, 'Functor' f) => (m ~> n) -> 'FreeT' f m ~> 'FreeT' f n@
hoistFreeT :: (Functor m, Functor f) => (forall a. m a -> n a) -> FreeT f m b -> FreeT f n b
hoistFreeT mh = FreeT . mh . fmap (fmap (hoistFreeT mh)) . runFreeT

-- | The very definition of a free monad transformer is that given a natural
-- transformation you get a monad transformer homomorphism.
foldFreeT :: (MonadTrans t, Monad (t m), Monad m)
          => (forall n x. Monad n => f x -> t n x) -> FreeT f m a -> t m a
foldFreeT f (FreeT m) = lift m >>= foldFreeF
  where
    foldFreeF (Pure a) = return a
    foldFreeF (Free as) = f as >>= foldFreeT f

-- | Lift a natural transformation from @f@ to @g@ into a monad homomorphism from @'FreeT' f m@ to @'FreeT' g m@
transFreeT :: (Monad m, Functor g) => (forall a. f a -> g a) -> FreeT f m b -> FreeT g m b
transFreeT nt = FreeT . liftM (fmap (transFreeT nt) . transFreeF nt) . runFreeT

-- | Pull out and join @m@ layers of @'FreeT' f m a@.
joinFreeT :: (Monad m, Traversable f) => FreeT f m a -> m (Free f a)
joinFreeT (FreeT m) = m >>= joinFreeF
  where
    joinFreeF (Pure x) = return (return x)
    joinFreeF (Free f) = wrap `liftM` Data.Traversable.mapM joinFreeT f

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

-- | Cuts off a tree of computations at a given depth.
-- If the depth is @0@ or less, no computation nor
-- monadic effects will take place.
--
-- Some examples (@n ≥ 0@):
--
-- @
-- 'cutoff' 0     _        ≡ 'return' 'Nothing'
-- 'cutoff' (n+1) '.' 'return' ≡ 'return' '.' 'Just'
-- 'cutoff' (n+1) '.' 'lift'   ≡ 'lift' '.' 'liftM' 'Just'
-- 'cutoff' (n+1) '.' 'wrap'   ≡ 'wrap' '.' 'fmap' ('cutoff' n)
-- @
--
-- Calling @'retract' '.' 'cutoff' n@ is always terminating, provided each of the
-- steps in the iteration is terminating.
cutoff :: (Functor f, Monad m) => Integer -> FreeT f m a -> FreeT f m (Maybe a)
cutoff n _ | n <= 0 = return Nothing
cutoff n (FreeT m) = FreeT $ bimap Just (cutoff (n - 1)) `liftM` m

-- | @partialIterT n phi m@ interprets first @n@ layers of @m@ using @phi@.
-- This is sort of the opposite for @'cutoff'@.
--
-- Some examples (@n ≥ 0@):
--
-- @
-- 'partialIterT' 0 _ m              ≡ m
-- 'partialIterT' (n+1) phi '.' 'return' ≡ 'return'
-- 'partialIterT' (n+1) phi '.' 'lift'   ≡ 'lift'
-- 'partialIterT' (n+1) phi '.' 'wrap'   ≡ 'join' . 'lift' . phi
-- @
partialIterT :: Monad m => Integer -> (forall a. f a -> m a) -> FreeT f m b -> FreeT f m b
partialIterT n phi m
  | n <= 0 = m
  | otherwise = FreeT $ do
      val <- runFreeT m
      case val of
        Pure a -> return (Pure a)
        Free f -> phi f >>= runFreeT . partialIterT (n - 1) phi

-- | @intersperseT f m@ inserts a layer @f@ between every two layers in
-- @m@.
--
-- @
-- 'intersperseT' f '.' 'return' ≡ 'return'
-- 'intersperseT' f '.' 'lift'   ≡ 'lift'
-- 'intersperseT' f '.' 'wrap'   ≡ 'wrap' '.' 'fmap' ('iterTM' ('wrap' '.' ('<$' f) '.' 'wrap'))
-- @
intersperseT :: (Monad m, Functor f) => f a -> FreeT f m b -> FreeT f m b
intersperseT f (FreeT m) = FreeT $ do
  val <- m
  case val of
    Pure x -> return $ Pure x
    Free y -> return . Free $ fmap (iterTM (wrap . (<$ f) . wrap)) y

-- | Tear down a free monad transformer using Monad instance for @t m@.
retractT :: (MonadTrans t, Monad (t m), Monad m) => FreeT (t m) m a -> t m a
retractT (FreeT m) = do
  val <- lift m
  case val of
    Pure x -> return x
    Free y -> y >>= retractT

-- | @intercalateT f m@ inserts a layer @f@ between every two layers in
-- @m@ and then retracts the result.
--
-- @
-- 'intercalateT' f ≡ 'retractT' . 'intersperseT' f
-- @
intercalateT :: (Monad m, MonadTrans t, Monad (t m)) => t m a -> FreeT (t m) m b -> t m b
intercalateT f (FreeT m) = do
  val <- lift m
  case val of
    Pure x -> return x
    Free y -> y >>= iterTM (\x -> f >> join x)
