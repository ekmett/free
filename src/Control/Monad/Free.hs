{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE TupleSections #-}

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
  , after
  , before
  , weave
  , weaveMax
  , weaveMin
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
import Data.Functor.Classes
import Data.Functor.WithIndex
import Data.Foldable
import Data.Foldable.WithIndex
import Data.Profunctor
import Data.Traversable
import Data.Traversable.WithIndex
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import Data.Data
import GHC.Generics
import Prelude hiding (foldr)

-- $setup
-- >>> import Control.Applicative (Const (..))
-- >>> import Data.Functor.Identity (Identity (..))
-- >>> import Data.Monoid (First (..))
-- >>> import Data.Tagged (Tagged (..))
-- >>> let preview l x = getFirst (getConst (l (Const . First . Just) x))
-- >>> let review l x = runIdentity (unTagged (l (Tagged (Identity x))))

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
  deriving (Generic, Generic1)

deriving instance (Typeable f, Data (f (Free f a)), Data a) => Data (Free f a)

instance Eq1 f => Eq1 (Free f) where
  liftEq eq = go
    where
      go (Pure a)  (Pure b)  = eq a b
      go (Free fa) (Free fb) = liftEq go fa fb
      go _ _                 = False

instance (Eq1 f, Eq a) => Eq (Free f a) where
  (==) = eq1

instance Ord1 f => Ord1 (Free f) where
  liftCompare cmp = go
    where
      go (Pure a)  (Pure b)  = cmp a b
      go (Pure _)  (Free _)  = LT
      go (Free _)  (Pure _)  = GT
      go (Free fa) (Free fb) = liftCompare go fa fb

instance (Ord1 f, Ord a) => Ord (Free f a) where
  compare = compare1

instance Show1 f => Show1 (Free f) where
  liftShowsPrec sp sl = go
    where
      go d (Pure a) = showsUnaryWith sp "Pure" d a
      go d (Free fa) = showsUnaryWith (liftShowsPrec go (liftShowList sp sl)) "Free" d fa

instance (Show1 f, Show a) => Show (Free f a) where
  showsPrec = showsPrec1

instance Read1 f => Read1 (Free f) where
  liftReadsPrec rp rl = go
    where
      go = readsData $
        readsUnaryWith rp "Pure" Pure `mappend`
        readsUnaryWith (liftReadsPrec go (liftReadList rp rl)) "Free" Free

instance (Read1 f, Read a) => Read (Free f a) where
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
instance MonadPlus v => MonadPlus (Free v) where
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

  foldl' f = go where
    go r free =
      case free of
        Pure a -> f r a
        Free fa -> foldl' go r fa
  {-# INLINE foldl' #-}

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

instance FunctorWithIndex i f => FunctorWithIndex [i] (Free f) where
  imap f (Pure a) = Pure $ f [] a
  imap f (Free s) = Free $ imap (\i -> imap (f . (:) i)) s
  {-# INLINE imap #-}

instance FoldableWithIndex i f => FoldableWithIndex [i] (Free f) where
  ifoldMap f (Pure a) = f [] a
  ifoldMap f (Free s) = ifoldMap (\i -> ifoldMap (f . (:) i)) s
  {-# INLINE ifoldMap #-}

instance TraversableWithIndex i f => TraversableWithIndex [i] (Free f) where
  itraverse f (Pure a) = Pure <$> f [] a
  itraverse f (Free s) = Free <$> itraverse (\i -> itraverse (f . (:) i)) s
  {-# INLINE itraverse #-}

instance MonadWriter e m => MonadWriter e (Free m) where
  tell = lift . tell
  {-# INLINE tell #-}
  listen = lift . listen . retract
  {-# INLINE listen #-}
  pass = lift . pass . retract
  {-# INLINE pass #-}

instance MonadReader e m => MonadReader e (Free m) where
  ask = lift ask
  {-# INLINE ask #-}
  local f = lift . local f . retract
  {-# INLINE local #-}

instance MonadState s m => MonadState s (Free m) where
  get = lift get
  {-# INLINE get #-}
  put s = lift (put s)
  {-# INLINE put #-}

instance MonadError e m => MonadError e (Free m) where
  throwError = lift . throwError
  {-# INLINE throwError #-}
  catchError as f = lift (catchError (retract as) (retract . f))
  {-# INLINE catchError #-}

instance MonadCont m => MonadCont (Free m) where
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
-- Calling @'retract' '.' 'cutoff' n@ is always terminating, provided each of the
-- steps in the iteration is terminating.
cutoff :: (Functor f) => Integer -> Free f a -> Free f (Maybe a)
cutoff n _ | n <= 0 = return Nothing
cutoff n (Free f) = Free $ fmap (cutoff (n - 1)) f
cutoff _ m = Just <$> m

-- | Unfold a free monad from a seed.
unfold :: Functor f => (b -> Either a (f b)) -> b -> Free f a
unfold f = f >>> either Pure (Free . fmap (unfold f))

-- | Unfold a free monad from a seed, monadically.
unfoldM :: (Traversable f, Monad m) => (b -> m (Either a (f b))) -> b -> m (Free f a)
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

before :: Functor m => m () -> Free m a -> Free m a
before mu = go
  where
    go = iterM $ \mfa -> liftF mu *> wrap (fmap go mfa)

after :: Functor m => m () -> Free m a -> Free m a
after mu = go
  where
    go = iterM $ \mfa -> wrap $ flip fmap mfa $ \fa' -> liftF mu *> go fa'

weave
  :: forall f a b c
   . Functor f
  => (          a  ->           b  -> Free f c)
  -> (          a  -> f (Free f b) -> Free f c)
  -> (f (Free f a) ->           b  -> Free f c)
  -> Free f a
  -> Free f b
  -> Free f c
weave end endA endB = go
  where
    go fa fb = case (fa, fb) of
      (Free ma, Free mb) -> join $ liftA2 go (liftF ma) (liftF mb)
      (Pure  a, Pure  b) -> end   a  b
      (Pure  a, Free mb) -> endA  a mb
      (Free ma, Pure  b) -> endB ma  b

weaveMax :: Functor f => Free f a -> Free f b -> Free f (a,b)
weaveMax = weave
  (curry Pure)
  (\a fb -> fmap (a,) (Free fb))
  (\fa b -> fmap (,b) (Free fa))

weaveMin :: Functor f => Free f a -> Free f b -> Free f ()
weaveMin = weave stop stop stop
  where stop _ _ = pure ()
