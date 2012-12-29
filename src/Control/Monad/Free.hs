{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Free
-- Copyright   :  (C) 2008-2012 Edward Kmett
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
  , hoistFree
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
-- Being 'Free' being left adjoint to @U@ means that there is an isomorphism between
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
-- This instance of 'MonadFree' is fairly naive about the encoding. For more efficient free monad implementations that require additional
-- extensions and thus aren't included here, you may want to look at the @kan-extensions@ package.
--
-- A number of common monads arise as free monads,
--
-- * Given @data Empty a@, @'Free' Empty@ is isomorphic to the 'Data.Functor.Identity' monad.
--
-- * @'Free' 'Maybe'@ can be used to model a partiality monad where each layer represents running the computation for a while longer.
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
  fmap f = go where
    go (Pure a)  = Pure (f a)
    go (Free fa) = Free (go <$> fa)
  {-# INLINE go #-}

instance Functor f => Apply (Free f) where
  Pure a  <.> Pure b = Pure (a b)
  Pure a  <.> Free fb = Free $ fmap a <$> fb
  Free fa <.> b = Free $ (<.> b) <$> fa
  {-# INLINE (<.> #-}

instance Functor f => Applicative (Free f) where
  pure = Pure
  {-# INLINE pure #-}
  Pure a <*> Pure b = Pure $ a b
  Pure a <*> Free mb = Free $ fmap a <$> mb
  Free ma <*> b = Free $ (<*> b) <$> ma
  {-# INLINE (<*>) #-}

instance Functor f => Bind (Free f) where
  Pure a >>- f = f a
  Free m >>- f = Free ((>>- f) <$> m)

instance Functor f => Monad (Free f) where
  return = Pure
  {-# INLINE return #-}
  Pure a >>= f = f a
  Free m >>= f = Free ((>>= f) <$> m)

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
  {-# INLINE go #-}

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

-- | A version of 'lift' that can be used with just a 'Functor' for @f@.
liftF :: Functor f => f a -> Free f a
liftF = Free . fmap Pure
{-# INLINE liftF #-}

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

-- | Lift a natural transformation from @f@ to @g@ into a natural transformation from @'FreeT' f@ to @'FreeT' g@.
hoistFree :: Functor g => (forall a. f a -> g a) -> Free f b -> Free g b
hoistFree _ (Pure a)  = Pure a
hoistFree f (Free as) = Free (hoistFree f <$> f as)

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
