{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
#if __GLASGOW_HASKELL__ >= 707
{-# LANGUAGE DeriveDataTypeable #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Comonad.Cofree
-- Copyright   :  (C) 2008-2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  MPTCs, fundeps
--
-- Cofree comonads
--
----------------------------------------------------------------------------
module Control.Comonad.Cofree
  ( Cofree(..)
  , ComonadCofree(..)
  , section
  , coiter
  , unfold
  -- * Lenses into cofree comonads
  , _extract
  , _unwrap
  , telescoped
  ) where

import Control.Applicative
import Control.Comonad
import Control.Comonad.Trans.Class
import Control.Comonad.Cofree.Class
import Control.Comonad.Env.Class
import Control.Comonad.Store.Class as Class
import Control.Comonad.Traced.Class
import Control.Category
import Control.Monad(ap)
import Control.Monad.Zip
import Data.Functor.Bind
import Data.Functor.Extend
import Data.Distributive
import Data.Foldable
import Data.Semigroup
import Data.Traversable
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import Prelude hiding (id,(.))

#ifdef GHC_TYPEABLE
import Data.Data
#endif

infixr 5 :<

-- | The 'Cofree' 'Comonad' of a functor @f@.
--
-- /Formally/
--
-- A 'Comonad' @v@ is a cofree 'Comonad' for @f@ if every comonad homomorphism
-- another comonad @w@ to @v@ is equivalent to a natural transformation
-- from @w@ to @f@.
--
-- A 'cofree' functor is right adjoint to a forgetful functor.
--
-- Cofree is a functor from the category of functors to the category of comonads
-- that is right adjoint to the forgetful functor from the category of comonads
-- to the category of functors that forgets how to 'extract' and
-- 'duplicate', leaving you with only a 'Functor'.
--
-- In practice, cofree comonads are quite useful for annotating syntax trees,
-- or talking about streams.
--
-- A number of common comonads arise directly as cofree comonads.
--
-- For instance,
--
-- * @'Cofree' 'Maybe'@ forms the a comonad for a non-empty list.
--
-- * @'Cofree' ('Const' b)@ is a product.
--
-- * @'Cofree' 'Identity'@ forms an infinite stream.
--
-- * @'Cofree' ((->) b)'@ describes a Moore machine with states labeled with values of type a, and transitions on edges of type b.
--
data Cofree f a = a :< f (Cofree f a)
#if __GLASGOW_HASKELL__ >= 707
  deriving (Typeable)
#endif

-- | Use coiteration to generate a cofree comonad from a seed.
--
-- @'coiter' f = 'unfold' ('id' 'Control.Arrow.&&&' f)@
coiter :: Functor f => (a -> f a) -> a -> Cofree f a
coiter psi a = a :< (coiter psi <$> psi a)

-- | Unfold a cofree comonad from a seed.
unfold :: Functor f => (b -> (a, f b)) -> b -> Cofree f a
unfold f c = case f c of
  (x, d) -> x :< fmap (unfold f) d

instance Functor f => ComonadCofree f (Cofree f) where
  unwrap (_ :< as) = as
  {-# INLINE unwrap #-}

instance Distributive f => Distributive (Cofree f) where
  distribute w = fmap extract w :< fmap distribute (collect unwrap w)

instance Functor f => Functor (Cofree f) where
  fmap f (a :< as) = f a :< fmap (fmap f) as
  b <$ (_ :< as) = b :< fmap (b <$) as

instance Functor f => Extend (Cofree f) where
  extended = extend
  {-# INLINE extended #-}
  duplicated = duplicate
  {-# INLINE duplicated #-}

instance Functor f => Comonad (Cofree f) where
  extend f w = f w :< fmap (extend f) (unwrap w)
  duplicate w = w :< fmap duplicate (unwrap w)
  extract (a :< _) = a
  {-# INLINE extract #-}

-- | This is not a true 'Comonad' transformer, but this instance is convenient.
instance ComonadTrans Cofree where
  lower (_ :< as) = fmap extract as
  {-# INLINE lower #-}

instance Alternative f => Monad (Cofree f) where
  return x = x :< empty
  {-# INLINE return #-}
  (a :< m) >>= k = case k a of
                     b :< n -> b :< (n <|> fmap (>>= k) m)

instance (Alternative f, MonadZip f) => MonadZip (Cofree f) where
  mzip (a :< as) (b :< bs) = (a, b) :< fmap (uncurry mzip) (mzip as bs)

-- |
--
-- @'lower' . 'section' = 'id'@
section :: Comonad f => f a -> Cofree f a
section as = extract as :< extend section as

instance Apply f => Apply (Cofree f) where
  (f :< fs) <.> (a :< as) = f a :< ((<.>) <$> fs <.> as)
  {-# INLINE (<.>) #-}
  (f :< fs) <.  (_ :< as) = f :< ((<. ) <$> fs <.> as)
  {-# INLINE (<.) #-}
  (_ :< fs)  .> (a :< as) = a :< (( .>) <$> fs <.> as)
  {-# INLINE (.>) #-}

instance ComonadApply f => ComonadApply (Cofree f) where
  (f :< fs) <@> (a :< as) = f a :< ((<@>) <$> fs <@> as)
  {-# INLINE (<@>) #-}
  (f :< fs) <@  (_ :< as) = f :< ((<@ ) <$> fs <@> as)
  {-# INLINE (<@) #-}
  (_ :< fs)  @> (a :< as) = a :< (( @>) <$> fs <@> as)
  {-# INLINE (@>) #-}

instance Alternative f => Applicative (Cofree f) where
  pure = return
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance (Show (f (Cofree f a)), Show a) => Show (Cofree f a) where
  showsPrec d (a :< as) = showParen (d > 5) $
    showsPrec 6 a . showString " :< " . showsPrec 5 as

instance (Read (f (Cofree f a)), Read a) => Read (Cofree f a) where
  readsPrec d r = readParen (d > 5)
                          (\r' -> [(u :< v,w) |
                                  (u, s) <- readsPrec 6 r',
                                  (":<", t) <- lex s,
                                  (v, w) <- readsPrec 5 t]) r

instance (Eq (f (Cofree f a)), Eq a) => Eq (Cofree f a) where
  a :< as == b :< bs = a == b && as == bs

instance (Ord (f (Cofree f a)), Ord a) => Ord (Cofree f a) where
  compare (a :< as) (b :< bs) = case compare a b of
    LT -> LT
    EQ -> compare as bs
    GT -> GT

instance Foldable f => Foldable (Cofree f) where
  foldMap f = go where
    go (a :< as) = f a `mappend` foldMap go as
  {-# INLINE foldMap #-}

instance Foldable1 f => Foldable1 (Cofree f) where
  foldMap1 f = go where
    go (a :< as) = f a <> foldMap1 go as
  {-# INLINE foldMap1 #-}

instance Traversable f => Traversable (Cofree f) where
  traverse f = go where
    go (a :< as) = (:<) <$> f a <*> traverse go as
  {-# INLINE traverse #-}

instance Traversable1 f => Traversable1 (Cofree f) where
  traverse1 f = go where
    go (a :< as) = (:<) <$> f a <.> traverse1 go as
  {-# INLINE traverse1 #-}

#if defined(GHC_TYPEABLE) && __GLASGOW_HASKELL__ < 707
instance (Typeable1 f) => Typeable1 (Cofree f) where
  typeOf1 dfa = mkTyConApp cofreeTyCon [typeOf1 (f dfa)]
    where
      f :: Cofree f a -> f a
      f = undefined

instance (Typeable1 f, Typeable a) => Typeable (Cofree f a) where
  typeOf = typeOfDefault

cofreeTyCon :: TyCon
#if __GLASGOW_HASKELL__ < 704
cofreeTyCon = mkTyCon "Control.Comonad.Cofree.Cofree"
#else
cofreeTyCon = mkTyCon3 "free" "Control.Comonad.Cofree" "Cofree"
#endif
{-# NOINLINE cofreeTyCon #-}

instance
  ( Typeable1 f
  , Data (f (Cofree f a))
  , Data a
  ) => Data (Cofree f a) where
    gfoldl f z (a :< as) = z (:<) `f` a `f` as
    toConstr _ = cofreeConstr
    gunfold k z c = case constrIndex c of
        1 -> k (k (z (:<)))
        _ -> error "gunfold"
    dataTypeOf _ = cofreeDataType
    dataCast1 f = gcast1 f

cofreeConstr :: Constr
cofreeConstr = mkConstr cofreeDataType ":<" [] Infix
{-# NOINLINE cofreeConstr #-}

cofreeDataType :: DataType
cofreeDataType = mkDataType "Control.Comonad.Cofree.Cofree" [cofreeConstr]
{-# NOINLINE cofreeDataType #-}
#endif

instance ComonadEnv e w => ComonadEnv e (Cofree w) where
  ask = ask . lower
  {-# INLINE ask #-}

instance ComonadStore s w => ComonadStore s (Cofree w) where
  pos (_ :< as) = Class.pos as
  {-# INLINE pos #-}
  peek s (_ :< as) = extract (Class.peek s as)
  {-# INLINE peek #-}

instance ComonadTraced m w => ComonadTraced m (Cofree w) where
  trace m = trace m . lower
  {-# INLINE trace #-}

-- | This is a lens that can be used to read or write from the target of 'extract'.
--
-- Using (^.) from the @lens@ package:
--
-- @foo ^. '_extract' == 'extract' foo@
--
-- For more on lenses see the @lens@ package on hackage
--
-- @'_extract' :: Lens' ('Cofree' g a) a@
_extract :: Functor f => (a -> f a) -> Cofree g a -> f (Cofree g a)
_extract f (a :< as) = (:< as) <$> f a
{-# INLINE _extract #-}

-- | This is a lens that can be used to read or write to the tails of a 'Cofree' 'Comonad'.
--
-- Using (^.) from the @lens@ package:
--
-- @foo ^. '_unwrap' == 'unwrap' foo@
--
-- For more on lenses see the @lens@ package on hackage
--
-- @'_unwrap' :: Lens' ('Cofree' g a) (g ('Cofree' g a))@
_unwrap :: Functor f => (g (Cofree g a) -> f (g (Cofree g a))) -> Cofree g a -> f (Cofree g a)
_unwrap  f (a :< as) = (a :<) <$> f as
{-# INLINE _unwrap #-}

-- | Construct a @Lens@ into a @'Cofree' f@ given a list of lenses into the base functor.
--
-- For more on lenses see the 'lens' package on hackage.
--
-- @telescoped :: 'Functor' g => [Lens' ('Cofree' g a) (g ('Cofree' g a))] -> Lens' ('Cofree' g a) a@
telescoped :: (Functor f, Functor g) =>
             [(Cofree g a -> f (Cofree g a)) -> g (Cofree g a) -> f (g (Cofree g a))] ->
              (a -> f a) -> Cofree g a -> f (Cofree g a)
telescoped = Prelude.foldr (\l r -> _unwrap . l . r) _extract
{-# INLINE telescoped #-}
