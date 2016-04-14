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

#ifndef MIN_VERSION_base
#define MIN_VERSION_base(x,y,z) 1
#endif

#ifndef MIN_VERSION_mtl
#define MIN_VERSION_mtl(x,y,z) 1
#endif

--------------------------------------------------------------------------------
-- |
-- Given an applicative, the free monad transformer.
--------------------------------------------------------------------------------

module Control.Monad.Trans.Free.Ap
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
import Control.Monad (liftM, MonadPlus(..), join)
import Control.Monad.Catch (MonadThrow(..), MonadCatch(..))
import Control.Monad.Trans.Class
import Control.Monad.Free.Class
import Control.Monad.IO.Class
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class
import Control.Monad.State.Class
import Control.Monad.Error.Class
import Control.Monad.Cont.Class
import Data.Functor.Bind hiding (join)
import Data.Monoid
import Data.Function (on)
import Data.Functor.Identity
import Data.Traversable
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Data
import Prelude.Extras

#if !(MIN_VERSION_base(4,8,0))
import Data.Foldable
#endif

-- | The base functor for a free monad.
data FreeF f a b = Pure a | Free (f b)
  deriving (Eq,Ord,Show,Read
#if __GLASGOW_HASKELL__ >= 707
           ,Typeable
#endif
           )

instance Show1 f => Show2 (FreeF f) where
  showsPrec2 d (Pure a)  = showParen (d > 10) $ showString "Pure " . showsPrec 11 a
  showsPrec2 d (Free as) = showParen (d > 10) $ showString "Free " . showsPrec1 11 as

instance (Show1 f, Show a) => Show1 (FreeF f a) where
  showsPrec1 = showsPrec2

instance Read1 f => Read2 (FreeF f) where
  readsPrec2 d r = readParen (d > 10)
      (\r' -> [ (Pure m, t)
             | ("Pure", s) <- lex r'
             , (m, t) <- readsPrec 11 s]) r
    ++ readParen (d > 10)
      (\r' -> [ (Free m, t)
             | ("Free", s) <- lex r'
             , (m, t) <- readsPrec1 11 s]) r

instance (Read1 f, Read a) => Read1 (FreeF f a) where
  readsPrec1 = readsPrec2

instance Eq1 f => Eq2 (FreeF f) where
  Pure a  ==## Pure b = a == b
  Free as ==## Free bs = as ==# bs
  _       ==## _ = False

instance (Eq1 f, Eq a) => Eq1 (FreeF f a) where
  (==#) = (==##)

instance Ord1 f => Ord2 (FreeF f) where
  Pure a `compare2` Pure b = a `compare` b
  Pure _ `compare2` Free _ = LT
  Free _ `compare2` Pure _ = GT
  Free fa `compare2` Free fb = fa `compare1` fb

instance (Ord1 f, Ord a) => Ord1 (FreeF f a) where
  compare1 = compare2

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

-- | The \"free monad transformer\" for an applicative @f@
newtype FreeT f m a = FreeT { runFreeT :: m (FreeF f a (FreeT f m a)) }

-- | The \"free monad\" for an applicative @f@.
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

instance (Functor f, Eq1 f, Functor m, Eq1 m) => Eq1 (FreeT f m) where
  (==#) = on (==#) (fmap (Lift1 . fmap Lift1) . runFreeT)

deriving instance Ord (m (FreeF f a (FreeT f m a))) => Ord (FreeT f m a)

instance (Functor f, Ord1 f, Functor m, Ord1 m) => Ord1 (FreeT f m) where
  compare1 = on compare1 (fmap (Lift1 . fmap Lift1) . runFreeT)

instance (Functor f, Show1 f, Functor m, Show1 m) => Show1 (FreeT f m) where
  showsPrec1 d (FreeT m) = showParen (d > 10) $
    showString "FreeT " . showsPrec1 11 (Lift1 . fmap Lift1 <$> m)

instance Show (m (FreeF f a (FreeT f m a))) => Show (FreeT f m a) where
  showsPrec d (FreeT m) = showParen (d > 10) $
    showString "FreeT " . showsPrec 11 m

instance (Functor f, Read1 f, Functor m, Read1 m) => Read1 (FreeT f m) where
  readsPrec1 d =  readParen (d > 10) $ \r ->
    [ (FreeT (fmap lower1 . lower1 <$> m),t) | ("FreeT",s) <- lex r, (m,t) <- readsPrec1 11 s]

instance Read (m (FreeF f a (FreeT f m a))) => Read (FreeT f m a) where
  readsPrec d =  readParen (d > 10) $ \r ->
    [ (FreeT m,t) | ("FreeT",s) <- lex r, (m,t) <- readsPrec 11 s]

instance (Functor f, Monad m) => Functor (FreeT f m) where
  fmap f (FreeT m) = FreeT (liftM f' m) where
    f' (Pure a)  = Pure (f a)
    f' (Free as) = Free (fmap (fmap f) as)

instance (Applicative f, Applicative m, Monad m) => Applicative (FreeT f m) where
  pure a = FreeT (return (Pure a))
  {-# INLINE pure #-}
  FreeT f <*> FreeT a = FreeT $ g <$> f <*> a where
    g (Pure f') (Pure a') = Pure (f' a')
    g (Pure f') (Free as) = Free $ fmap f' <$> as
    g (Free fs) (Pure a') = Free $ fmap ($ a') <$> fs
    g (Free fs) (Free as) = Free $ (<*>) <$> fs <*> as
  {-# INLINE (<*>) #-}

instance (Apply f, Apply m, Monad m) => Apply (FreeT f m) where
  FreeT f <.> FreeT a = FreeT $ g <$> f <.> a where
    g (Pure f') (Pure a') = Pure (f' a')
    g (Pure f') (Free as) = Free $ fmap f' <$> as
    g (Free fs) (Pure a') = Free $ fmap ($ a') <$> fs
    g (Free fs) (Free as) = Free $ (<.>) <$> fs <.> as

instance (Apply f, Apply m, Monad m) => Bind (FreeT f m) where
  FreeT m >>- f = FreeT $ m >>= \v -> case v of
    Pure a -> runFreeT (f a)
    Free w -> return (Free (fmap (>>- f) w))

instance (Applicative f, Monad m) => Monad (FreeT f m) where
  fail e = FreeT (fail e)
  return = pure
  {-# INLINE return #-}
  FreeT m >>= f = FreeT $ m >>= \v -> case v of
    Pure a -> runFreeT (f a)
    Free w -> return (Free (fmap (>>= f) w))

instance MonadTrans (FreeT f) where
  lift = FreeT . liftM Pure
  {-# INLINE lift #-}

instance (Applicative f, MonadIO m) => MonadIO (FreeT f m) where
  liftIO = lift . liftIO
  {-# INLINE liftIO #-}

instance (Applicative f, MonadReader r m) => MonadReader r (FreeT f m) where
  ask = lift ask
  {-# INLINE ask #-}
  local f = hoistFreeT (local f)
  {-# INLINE local #-}

instance (Applicative f, MonadWriter w m) => MonadWriter w (FreeT f m) where
  tell = lift . tell
  {-# INLINE tell #-}
  listen (FreeT m) = FreeT $ liftM concat' $ listen (fmap listen `liftM` m)
    where
      concat' (Pure x, w) = Pure (x, w)
      concat' (Free y, w) = Free $ fmap (second (w <>)) <$> y
  pass m = FreeT . pass' . runFreeT . hoistFreeT clean $ listen m
    where
      clean = pass . liftM (\x -> (x, const mempty))
      pass' = join . liftM g
      g (Pure ((x, f), w)) = tell (f w) >> return (Pure x)
      g (Free f)           = return . Free . fmap (FreeT . pass' . runFreeT) $ f
#if MIN_VERSION_mtl(2,1,1)
  writer w = lift (writer w)
  {-# INLINE writer #-}
#endif

instance (Applicative f, MonadState s m) => MonadState s (FreeT f m) where
  get = lift get
  {-# INLINE get #-}
  put = lift . put
  {-# INLINE put #-}
#if MIN_VERSION_mtl(2,1,1)
  state f = lift (state f)
  {-# INLINE state #-}
#endif

instance (Applicative f, MonadError e m) => MonadError e (FreeT f m) where
  throwError = lift . throwError
  {-# INLINE throwError #-}
  FreeT m `catchError` f = FreeT $ liftM (fmap (`catchError` f)) m `catchError` (runFreeT . f)

instance (Applicative f, MonadCont m) => MonadCont (FreeT f m) where
  callCC f = FreeT $ callCC (\k -> runFreeT $ f (lift . k . Pure))

instance (Applicative f, MonadPlus m) => Alternative (FreeT f m) where
  empty = FreeT mzero
  FreeT ma <|> FreeT mb = FreeT (mplus ma mb)
  {-# INLINE (<|>) #-}

instance (Applicative f, MonadPlus m) => MonadPlus (FreeT f m) where
  mzero = FreeT mzero
  {-# INLINE mzero #-}
  mplus (FreeT ma) (FreeT mb) = FreeT (mplus ma mb)
  {-# INLINE mplus #-}

instance (Applicative f, Monad m) => MonadFree f (FreeT f m) where
  wrap = FreeT . return . Free
  {-# INLINE wrap #-}

instance (Applicative f, MonadThrow m) => MonadThrow (FreeT f m) where
  throwM = lift . throwM
  {-# INLINE throwM #-}

instance (Applicative f, MonadCatch m) => MonadCatch (FreeT f m) where
  FreeT m `catch` f = FreeT $ liftM (fmap (`Control.Monad.Catch.catch` f)) m
                                `Control.Monad.Catch.catch` (runFreeT . f)
  {-# INLINE catch #-}

-- | Given an applicative homomorphism from @f (m a)@ to @m a@,
-- tear down a free monad transformer using iteration.
iterT :: (Applicative f, Monad m) => (f (m a) -> m a) -> FreeT f m a -> m a
iterT f (FreeT m) = do
    val <- m
    case fmap (iterT f) val of
        Pure x -> return x
        Free y -> f y

-- | Given an applicative homomorphism from @f (t m a)@ to @t m a@,
-- tear down a free monad transformer using iteration over a transformer.
iterTM :: (Applicative f, Monad m, MonadTrans t, Monad (t m)) => (f (t m a) -> t m a) -> FreeT f m a -> t m a
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
hoistFreeT :: (Monad m, Applicative f) => (forall a. m a -> n a) -> FreeT f m b -> FreeT f n b
hoistFreeT mh = FreeT . mh . liftM (fmap (hoistFreeT mh)) . runFreeT

-- | Lift an applicative homomorphism from @f@ to @g@ into a monad homomorphism from @'FreeT' f m@ to @'FreeT' g m@
transFreeT :: (Monad m, Applicative g) => (forall a. f a -> g a) -> FreeT f m b -> FreeT g m b
transFreeT nt = FreeT . liftM (fmap (transFreeT nt) . transFreeF nt) . runFreeT

-- | Pull out and join @m@ layers of @'FreeT' f m a@.
joinFreeT :: (Monad m, Traversable f, Applicative f) => FreeT f m a -> m (Free f a)
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

-- | Given an applicative homomorphism from @f@ to 'Identity', tear down a 'Free' 'Monad' using iteration.
iter :: Applicative f => (f a -> a) -> Free f a -> a
iter phi = runIdentity . iterT (Identity . phi . fmap runIdentity)

-- | Like 'iter' for monadic values.
iterM :: (Applicative f, Monad m) => (f (m a) -> m a) -> Free f a -> m a
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
cutoff :: (Applicative f, Monad m) => Integer -> FreeT f m a -> FreeT f m (Maybe a)
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
intersperseT :: (Monad m, Applicative f) => f a -> FreeT f m b -> FreeT f m b
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
#if __GLASGOW_HASKELL__ < 710
intercalateT :: (Monad m, MonadTrans t, Monad (t m), Applicative (t m)) => t m a -> FreeT (t m) m b -> t m b
#else
intercalateT :: (Monad m, MonadTrans t, Monad (t m)) => t m a -> FreeT (t m) m b -> t m b
#endif
intercalateT f (FreeT m) = do
  val <- lift m
  case val of
    Pure x -> return x
    Free y -> y >>= iterTM (\x -> f >> join x)

#if __GLASGOW_HASKELL__ < 707
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
