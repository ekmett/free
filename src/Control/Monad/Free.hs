{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
#if __GLASGOW_HASKELL__ >= 707
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
#endif
#include "free-common.h"
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Free
-- Copyright   :  (C) 2008-2015 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  MPTCs, fundeps
--
-- Monads for free
----------------------------------------------------------------------------
module Control.Monad.Free
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
import qualified Control.Monad.Trans.Free as FreeT
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

-- | The 'Free' 'Monad' for a 'Functor' @f@.
--
-- /Formally/
--
-- A 'Monad' @n@ is a free 'Monad' for @f@ if every monad homomorphism
-- from @n@ to another monad @m@ is equivalent to a natural transformation
-- from @f@ to @m@.
--
-- /Why Free?/
--
-- Every \"free\" functor is left adjoint to some \"forgetful\" functor.
--
-- If we define a forgetful functor @U@ from the category of monads to the category of functors
-- that just forgets the 'Monad', leaving only the 'Functor'. i.e.
--
-- @U (M,'return','Control.Monad.join') = M@
--
-- then 'Free' is the left adjoint to @U@.
--
-- 'Free' being left adjoint to @U@ means that there is an isomorphism between
--
-- @'Free' f -> m@ in the category of monads and @f -> U m@ in the category of functors.
--
-- Morphisms in the category of monads are 'Monad' homomorphisms (natural transformations that respect 'return' and 'Control.Monad.join').
--
-- Morphisms in the category of functors are 'Functor' homomorphisms (natural transformations).
--
-- Given this isomorphism, every monad homomorphism from @'Free' f@ to @m@ is equivalent to a natural transformation from @f@ to @m@
--
-- Showing that this isomorphism holds is left as an exercise.
--
-- In practice, you can just view a @'Free' f a@ as many layers of @f@ wrapped around values of type @a@, where
-- @('>>=')@ performs substitution and grafts new layers of @f@ in for each of the free variables.
--
-- This can be very useful for modeling domain specific languages, trees, or other constructs.
--
-- This instance of 'MonadFree' is fairly naive about the encoding. For more efficient free monad implementation see "Control.Monad.Free.Church", in particular note the 'Control.Monad.Free.Church.improve' combinator.
-- You may also want to take a look at the @kan-extensions@ package (<http://hackage.haskell.org/package/kan-extensions>).
--
-- A number of common monads arise as free monads,
--
-- * Given @data Empty a@, @'Free' Empty@ is isomorphic to the 'Data.Functor.Identity' monad.
--
-- * @'Free' 'Maybe'@ can be used to model a partiality monad where each layer represents running the computation for a while longer.
data Free f a = Pure a | Free (f (Free f a))
#if __GLASGOW_HASKELL__ >= 707
  deriving (Typeable, Generic, Generic1)

deriving instance (Typeable f, Data (f (Free f a)), Data a) => Data (Free f a)
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

instance Functor f => Apply (Free f) where
  Pure a  <.> Pure b = Pure (a b)
  Pure a  <.> Free fb = Free $ fmap a <$> fb
  Free fa <.> b = Free $ (<.> b) <$> fa

instance Functor f => Applicative (Free f) where
  pure = Pure
  {-# INLINE pure #-}
  Pure a <*> Pure b = Pure $ a b
  Pure a <*> Free mb = Free $ fmap a <$> mb
  Free ma <*> b = Free $ (<*> b) <$> ma

instance Functor f => Bind (Free f) where
  Pure a >>- f = f a
  Free m >>- f = Free ((>>- f) <$> m)

instance Functor f => Monad (Free f) where
  return = pure
  {-# INLINE return #-}
  Pure a >>= f = f a
  Free m >>= f = Free ((>>= f) <$> m)

instance Functor f => MonadFix (Free f) where
  mfix f = a where a = f (impure a); impure (Pure x) = x; impure (Free _) = error "mfix (Free f): Free"

-- | This violates the Alternative laws, handle with care.
instance Alternative v => Alternative (Free v) where
  empty = Free empty
  {-# INLINE empty #-}
  a <|> b = Free (pure a <|> pure b)
  {-# INLINE (<|>) #-}

-- | This violates the MonadPlus laws, handle with care.
instance (Functor v, MonadPlus v) => MonadPlus (Free v) where
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

instance (Functor m, MonadWriter e m) => MonadWriter e (Free m) where
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

instance (Functor m, MonadState s m) => MonadState s (Free m) where
  get = lift get
  {-# INLINE get #-}
  put s = lift (put s)
  {-# INLINE put #-}

instance (Functor m, MonadError e m) => MonadError e (Free m) where
  throwError = lift . throwError
  {-# INLINE throwError #-}
  catchError as f = lift (catchError (retract as) (retract . f))
  {-# INLINE catchError #-}

instance (Functor m, MonadCont m) => MonadCont (Free m) where
  callCC f = lift (callCC (retract . f . liftM lift))
  {-# INLINE callCC #-}

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
retract :: Monad f => Free f a -> f a
retract (Pure a) = return a
retract (Free as) = as >>= retract

-- | Tear down a 'Free' 'Monad' using iteration.
iter :: Functor f => (f a -> a) -> Free f a -> a
iter _ (Pure a) = a
iter phi (Free m) = phi (iter phi <$> m)

-- | Like 'iter' for applicative values.
iterA :: (Applicative p, Functor f) => (f (p a) -> p a) -> Free f a -> p a
iterA _   (Pure x) = pure x
iterA phi (Free f) = phi (iterA phi <$> f)

-- | Like 'iter' for monadic values.
iterM :: (Monad m, Functor f) => (f (m a) -> m a) -> Free f a -> m a
iterM _   (Pure x) = return x
iterM phi (Free f) = phi (iterM phi <$> f)

-- | Lift a natural transformation from @f@ to @g@ into a natural transformation from @'Free' f@ to @'Free' g@.
hoistFree :: Functor g => (forall a. f a -> g a) -> Free f b -> Free g b
hoistFree _ (Pure a)  = Pure a
hoistFree f (Free as) = Free (hoistFree f <$> f as)

-- | The very definition of a free monad is that given a natural transformation you get a monad homomorphism.
foldFree :: Monad m => (forall x . f x -> m x) -> Free f a -> m a
foldFree _ (Pure a)  = return a
foldFree f (Free as) = f as >>= foldFree f

-- | Convert a 'Free' monad from "Control.Monad.Free" to a 'FreeT.FreeT' monad
-- from "Control.Monad.Trans.Free".
toFreeT :: (Functor f, Monad m) => Free f a -> FreeT.FreeT f m a
toFreeT (Pure a) = FreeT.FreeT (return (FreeT.Pure a))
toFreeT (Free f) = FreeT.FreeT (return (FreeT.Free (fmap toFreeT f)))

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
cutoff :: (Functor f) => Integer -> Free f a -> Free f (Maybe a)
cutoff n _ | n <= 0 = return Nothing
cutoff n (Free f) = Free $ fmap (cutoff (n - 1)) f
cutoff _ m = Just <$> m

-- | Unfold a free monad from a seed.
unfold :: Functor f => (b -> Either a (f b)) -> b -> Free f a
unfold f = f >>> either Pure (Free . fmap (unfold f))

-- | Unfold a free monad from a seed, monadically.
unfoldM :: (Traversable f, Applicative m, Monad m) => (b -> m (Either a (f b))) -> b -> m (Free f a)
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

-- | This is @Prism (Free f a) (Free g a) (f (Free f a)) (g (Free g a))@ in disguise
--
-- >>> preview _Free (review _Free (Just (Pure 3)))
-- Just (Just (Pure 3))
--
-- >>> review _Free (Just (Pure 3))
-- Free (Just (Pure 3))
_Free :: forall f g m a p. (Choice p, Applicative m)
      => p (f (Free f a)) (m (g (Free g a))) -> p (Free f a) (m (Free g a))
_Free = dimap unfree (either pure (fmap Free)) . right'
 where
  unfree (Free x) = Right x
  unfree (Pure x) = Left (Pure x)
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
