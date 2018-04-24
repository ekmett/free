{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
#if __GLASGOW_HASKELL__ >= 707
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
#endif
#include "free-common.h"

--------------------------------------------------------------------------------
-- |
-- \"Applicative Effects in Free Monads\"
--
-- Often times, the '(\<*\>)' operator can be more efficient than 'ap'.
-- Conventional free monads don't provide any means of modeling this.
-- The free monad can be modified to make use of an underlying applicative.
-- But it does require some laws, or else the '(\<*\>)' = 'ap' law is broken.
-- When interpreting this free monad with 'foldFree',
-- the natural transformation must be an applicative homomorphism.
-- An applicative homomorphism @hm :: (Applicative f, Applicative g) => f x -> g x@
-- will satisfy these laws.
--
-- * @hm (pure a) = pure a@
-- * @hm (f \<*\> a) = hm f \<*\> hm a@
--
-- This is based on the \"Applicative Effects in Free Monads\" series of articles by Will Fancher
--
-- * <http://elvishjerricco.github.io/2016/04/08/applicative-effects-in-free-monads.html Applicative Effects in Free Monads>
--
-- * <http://elvishjerricco.github.io/2016/04/13/more-on-applicative-effects-in-free-monads.html More on Applicative Effects in Free Monads>
--------------------------------------------------------------------------------
module Control.Monad.Free.Ap
  ( MonadFree(..)
  , Free(..)
  , retract
  , liftF
  , iter
  , iterA
  , iterM
  , hoistFree
  , foldFree
  , toFreeT
  , cutoff
  , unfold
  , unfoldM
  , _Pure, _Free
  ) where

import Control.Applicative
import Control.Arrow ((>>>))
import Control.Monad (liftM, MonadPlus(..), (>=>))
import Control.Monad.Fix
import Control.Monad.Trans.Class
import qualified Control.Monad.Trans.Free.Ap as FreeT
import Control.Monad.Free.Class
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class
import Control.Monad.State.Class
import Control.Monad.Error.Class
import Control.Monad.Cont.Class
import Data.Functor.Bind
import Data.Functor.Classes.Compat
import Data.Foldable
import Data.Profunctor
import Data.Traversable
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import Data.Data
import Prelude hiding (foldr)
#if __GLASGOW_HASKELL__ >= 707
import GHC.Generics
#endif

-- | A free monad given an applicative
data Free f a = Pure a | Free (f (Free f a))
#if __GLASGOW_HASKELL__ >= 707
  deriving (Typeable, Generic, Generic1)
#endif

#ifdef LIFTED_FUNCTOR_CLASSES
instance Eq1 f => Eq1 (Free f) where
  liftEq eq = go
    where
      go (Pure a)  (Pure b)  = eq a b
      go (Free fa) (Free fb) = liftEq go fa fb
      go _ _                 = False
#else
instance (Functor f, Eq1 f) => Eq1 (Free f) where
  Pure a  `eq1` Pure b  = a == b
  Free fa `eq1` Free fb = fmap Lift1 fa `eq1` fmap Lift1 fb
  _       `eq1` _ = False
#endif

#ifdef LIFTED_FUNCTOR_CLASSES
instance (Eq1 f, Eq a) => Eq (Free f a) where
#else
instance (Eq1 f, Functor f, Eq a) => Eq (Free f a) where
#endif
  (==) = eq1

#ifdef LIFTED_FUNCTOR_CLASSES
instance Ord1 f => Ord1 (Free f) where
  liftCompare cmp = go
    where
      go (Pure a)  (Pure b)  = cmp a b
      go (Pure _)  (Free _)  = LT
      go (Free _)  (Pure _)  = GT
      go (Free fa) (Free fb) = liftCompare go fa fb
#else
instance (Functor f, Ord1 f) => Ord1 (Free f) where
  Pure a `compare1` Pure b = a `compare` b
  Pure _ `compare1` Free _ = LT
  Free _ `compare1` Pure _ = GT
  Free fa `compare1` Free fb = fmap Lift1 fa `compare1` fmap Lift1 fb
#endif

#ifdef LIFTED_FUNCTOR_CLASSES
instance (Ord1 f, Ord a) => Ord (Free f a) where
#else
instance (Ord1 f, Functor f, Ord a) => Ord (Free f a) where
#endif
  compare = compare1

#ifdef LIFTED_FUNCTOR_CLASSES
instance Show1 f => Show1 (Free f) where
  liftShowsPrec sp sl = go
    where
      go d (Pure a) = showsUnaryWith sp "Pure" d a
      go d (Free fa) = showsUnaryWith (liftShowsPrec go (liftShowList sp sl)) "Free" d fa
#else
instance (Functor f, Show1 f) => Show1 (Free f) where
  showsPrec1 d (Pure a) = showParen (d > 10) $
    showString "Pure " . showsPrec 11 a
  showsPrec1 d (Free m) = showParen (d > 10) $
    showString "Free " . showsPrec1 11 (fmap Lift1 m)
#endif

#ifdef LIFTED_FUNCTOR_CLASSES
instance (Show1 f, Show a) => Show (Free f a) where
#else
instance (Show1 f, Functor f, Show a) => Show (Free f a) where
#endif
  showsPrec = showsPrec1

#ifdef LIFTED_FUNCTOR_CLASSES
instance Read1 f => Read1 (Free f) where
  liftReadsPrec rp rl = go
    where
      go = readsData $
        readsUnaryWith rp "Pure" Pure `mappend`
        readsUnaryWith (liftReadsPrec go (liftReadList rp rl)) "Free" Free
#else
instance (Functor f, Read1 f) => Read1 (Free f) where
  readsPrec1 d r = readParen (d > 10)
      (\r' -> [ (Pure m, t)
             | ("Pure", s) <- lex r'
             , (m, t) <- readsPrec 11 s]) r
    ++ readParen (d > 10)
      (\r' -> [ (Free (fmap lower1 m), t)
             | ("Free", s) <- lex r'
             , (m, t) <- readsPrec1 11 s]) r
#endif

#ifdef LIFTED_FUNCTOR_CLASSES
instance (Read1 f, Read a) => Read (Free f a) where
#else
instance (Read1 f, Functor f, Read a) => Read (Free f a) where
#endif
  readsPrec = readsPrec1

instance Functor f => Functor (Free f) where
  fmap f = go where
    go (Pure a)  = Pure (f a)
    go (Free fa) = Free (go <$> fa)
  {-# INLINE fmap #-}

instance Apply f => Apply (Free f) where
  Pure a  <.> Pure b = Pure (a b)
  Pure a  <.> Free fb = Free $ fmap a <$> fb
  Free fa <.> Pure b = Free $ fmap ($ b) <$> fa
  Free fa <.> Free fb = Free $ fmap (<.>) fa <.> fb

instance Applicative f => Applicative (Free f) where
  pure = Pure
  {-# INLINE pure #-}
  Pure a <*> Pure b = Pure $ a b
  Pure a <*> Free mb = Free $ fmap a <$> mb
  Free ma <*> Pure b = Free $ fmap ($ b) <$> ma
  Free ma <*> Free mb = Free $ fmap (<*>) ma <*> mb

instance Apply f => Bind (Free f) where
  Pure a >>- f = f a
  Free m >>- f = Free ((>>- f) <$> m)

instance Applicative f => Monad (Free f) where
  return = pure
  {-# INLINE return #-}
  Pure a >>= f = f a
  Free m >>= f = Free ((>>= f) <$> m)

instance Applicative f => MonadFix (Free f) where
  mfix f = a where a = f (impure a); impure (Pure x) = x; impure (Free _) = error "mfix (Free f): Free"

-- | This violates the Alternative laws, handle with care.
instance Alternative v => Alternative (Free v) where
  empty = Free empty
  {-# INLINE empty #-}
  a <|> b = Free (pure a <|> pure b)
  {-# INLINE (<|>) #-}

-- | This violates the MonadPlus laws, handle with care.
instance (Applicative v, MonadPlus v) => MonadPlus (Free v) where
  mzero = Free mzero
  {-# INLINE mzero #-}
  a `mplus` b = Free (return a `mplus` return b)
  {-# INLINE mplus #-}

-- | This is not a true monad transformer. It is only a monad transformer \"up to 'retract'\".
instance MonadTrans Free where
  lift = Free . liftM Pure
  {-# INLINE lift #-}

instance Foldable f => Foldable (Free f) where
  foldMap f = go where
    go (Pure a) = f a
    go (Free fa) = foldMap go fa
  {-# INLINE foldMap #-}

  foldr f = go where
    go r free =
      case free of
        Pure a -> f a r
        Free fa -> foldr (flip go) r fa
  {-# INLINE foldr #-}

#if MIN_VERSION_base(4,6,0)
  foldl' f = go where
    go r free =
      case free of
        Pure a -> f r a
        Free fa -> foldl' go r fa
  {-# INLINE foldl' #-}
#endif

instance Foldable1 f => Foldable1 (Free f) where
  foldMap1 f = go where
    go (Pure a) = f a
    go (Free fa) = foldMap1 go fa
  {-# INLINE foldMap1 #-}

instance Traversable f => Traversable (Free f) where
  traverse f = go where
    go (Pure a) = Pure <$> f a
    go (Free fa) = Free <$> traverse go fa
  {-# INLINE traverse #-}

instance Traversable1 f => Traversable1 (Free f) where
  traverse1 f = go where
    go (Pure a) = Pure <$> f a
    go (Free fa) = Free <$> traverse1 go fa
  {-# INLINE traverse1 #-}

instance (Applicative m, MonadWriter e m) => MonadWriter e (Free m) where
  tell = lift . tell
  {-# INLINE tell #-}
  listen = lift . listen . retract
  {-# INLINE listen #-}
  pass = lift . pass . retract
  {-# INLINE pass #-}

instance (Applicative m, MonadReader e m) => MonadReader e (Free m) where
  ask = lift ask
  {-# INLINE ask #-}
  local f = lift . local f . retract
  {-# INLINE local #-}

instance (Applicative m, MonadState s m) => MonadState s (Free m) where
  get = lift get
  {-# INLINE get #-}
  put s = lift (put s)
  {-# INLINE put #-}

instance (Applicative m, MonadError e m) => MonadError e (Free m) where
  throwError = lift . throwError
  {-# INLINE throwError #-}
  catchError as f = lift (catchError (retract as) (retract . f))
  {-# INLINE catchError #-}

instance (Applicative m, MonadCont m) => MonadCont (Free m) where
  callCC f = lift (callCC (retract . f . liftM lift))
  {-# INLINE callCC #-}

instance Applicative f => MonadFree f (Free f) where
  wrap = Free
  {-# INLINE wrap #-}

-- |
-- 'retract' is the left inverse of 'lift' and 'liftF'
--
-- @
-- 'retract' . 'lift' = 'id'
-- 'retract' . 'liftF' = 'id'
-- @
retract :: (Applicative f, Monad f) => Free f a -> f a
retract = foldFree id

-- | Given an applicative homomorphism from @f@ to 'Identity', tear down a 'Free' 'Monad' using iteration.
iter :: Applicative f => (f a -> a) -> Free f a -> a
iter _ (Pure a) = a
iter phi (Free m) = phi (iter phi <$> m)

-- | Like 'iter' for applicative values.
iterA :: (Applicative p, Applicative f) => (f (p a) -> p a) -> Free f a -> p a
iterA _   (Pure x) = pure x
iterA phi (Free f) = phi (iterA phi <$> f)

-- | Like 'iter' for monadic values.
iterM :: (Applicative m, Monad m, Applicative f) => (f (m a) -> m a) -> Free f a -> m a
iterM _   (Pure x) = return x
iterM phi (Free f) = phi (iterM phi <$> f)

-- | Lift an applicative homomorphism from @f@ to @g@ into a monad homomorphism from @'Free' f@ to @'Free' g@.
hoistFree :: (Applicative f, Applicative g) => (forall a. f a -> g a) -> Free f b -> Free g b
hoistFree f = foldFree (liftF . f)

-- | Given an applicative homomorphism, you get a monad homomorphism.
foldFree :: (Applicative f, Applicative m, Monad m) => (forall x . f x -> m x) -> Free f a -> m a
foldFree _ (Pure a)  = return a
foldFree f (Free as) = f as >>= foldFree f

-- | Convert a 'Free' monad from "Control.Monad.Free.Ap" to a 'FreeT.FreeT' monad
-- from "Control.Monad.Trans.Free.Ap".
-- WARNING: This assumes that 'liftF' is an applicative homomorphism.
toFreeT :: (Applicative f, Applicative m, Monad m) => Free f a -> FreeT.FreeT f m a
toFreeT = foldFree liftF

-- | Cuts off a tree of computations at a given depth.
-- If the depth is 0 or less, no computation nor
-- monadic effects will take place.
--
-- Some examples (n ≥ 0):
--
-- prop> cutoff 0     _        == return Nothing
-- prop> cutoff (n+1) . return == return . Just
-- prop> cutoff (n+1) . lift   ==   lift . liftM Just
-- prop> cutoff (n+1) . wrap   ==  wrap . fmap (cutoff n)
--
-- Calling 'retract . cutoff n' is always terminating, provided each of the
-- steps in the iteration is terminating.
cutoff :: (Applicative f) => Integer -> Free f a -> Free f (Maybe a)
cutoff n _ | n <= 0 = return Nothing
cutoff n (Free f) = Free $ fmap (cutoff (n - 1)) f
cutoff _ m = Just <$> m

-- | Unfold a free monad from a seed.
unfold :: Applicative f => (b -> Either a (f b)) -> b -> Free f a
unfold f = f >>> either Pure (Free . fmap (unfold f))

-- | Unfold a free monad from a seed, monadically.
unfoldM :: (Applicative f, Traversable f, Applicative m, Monad m) => (b -> m (Either a (f b))) -> b -> m (Free f a)
unfoldM f = f >=> either (pure . pure) (fmap Free . traverse (unfoldM f))

-- | This is @Prism' (Free f a) a@ in disguise
--
-- >>> preview _Pure (Pure 3)
-- Just 3
--
-- >>> review _Pure 3 :: Free Maybe Int
-- Pure 3
_Pure :: forall f m a p. (Choice p, Applicative m)
      => p a (m a) -> p (Free f a) (m (Free f a))
_Pure = dimap impure (either pure (fmap Pure)) . right'
 where
  impure (Pure x) = Right x
  impure x        = Left x
  {-# INLINE impure #-}
{-# INLINE _Pure #-}

-- | This is @Prism' (Free f a) (f (Free f a))@ in disguise
--
-- >>> preview _Free (review _Free (Just (Pure 3)))
-- Just (Just (Pure 3))
--
-- >>> review _Free (Just (Pure 3))
-- Free (Just (Pure 3))
_Free :: forall f m a p. (Choice p, Applicative m)
      => p (f (Free f a)) (m (f (Free f a))) -> p (Free f a) (m (Free f a))
_Free = dimap unfree (either pure (fmap Free)) . right'
 where
  unfree (Free x) = Right x
  unfree x        = Left x
  {-# INLINE unfree #-}
{-# INLINE _Free #-}


#if __GLASGOW_HASKELL__ < 707
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
