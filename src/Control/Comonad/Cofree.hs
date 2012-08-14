{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Comonad.Cofree
-- Copyright   :  (C) 2008-2011 Edward Kmett,
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
  , section
  , unwrap
  , coiter
  , unfold
  -- * Lenses into cofree comonads
  , extracting
  , unwrapping
  , telescoping
  ) where

import Control.Applicative
import Control.Comonad
import Control.Comonad.Trans.Class
import Control.Comonad.Cofree.Class
import Control.Comonad.Env.Class
import Control.Comonad.Store.Class as Class
import Control.Comonad.Traced.Class
import Control.Category
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

data Cofree f a = a :< f (Cofree f a)

coiter :: Functor f => (a -> f a) -> a -> Cofree f a
coiter psi a = a :< (coiter psi <$> psi a)

unfold :: Functor f => (b -> (a, f b)) -> b -> Cofree f a
unfold f c = case f c of
  (x, d) -> x :< fmap (unfold f) d

instance Functor f => ComonadCofree f (Cofree f) where
  unwrap (_ :< as) = as

instance Distributive f => Distributive (Cofree f) where
  distribute w = fmap extract w :< fmap distribute (collect unwrap w)

instance Functor f => Functor (Cofree f) where
  fmap f (a :< as) = f a :< fmap (fmap f) as
  b <$ (_ :< as) = b :< fmap (b <$) as

instance Functor f => Extend (Cofree f) where
  extended = extend
  duplicated = duplicate

instance Functor f => Comonad (Cofree f) where
  extend f w = f w :< fmap (extend f) (unwrap w)
  duplicate w = w :< fmap duplicate (unwrap w)
  extract (a :< _) = a

instance ComonadTrans Cofree where
  lower (_ :< as) = fmap extract as

-- | lower . section = id
section :: Comonad f => f a -> Cofree f a
section as = extract as :< extend section as

instance Apply f => Apply (Cofree f) where
  (f :< fs) <.> (a :< as) = f a :< ((<.>) <$> fs <.> as)
  (f :< fs) <.  (_ :< as) = f :< ((<. ) <$> fs <.> as)
  (_ :< fs)  .> (a :< as) = a :< (( .>) <$> fs <.> as)

instance ComonadApply f => ComonadApply (Cofree f) where
  (f :< fs) <@> (a :< as) = f a :< ((<@>) <$> fs <@> as)
  (f :< fs) <@  (_ :< as) = f :< ((<@ ) <$> fs <@> as)
  (_ :< fs)  @> (a :< as) = a :< (( @>) <$> fs <@> as)

instance Applicative f => Applicative (Cofree f) where
  pure a = as where as = a :< pure as
  (f :< fs) <*> (a :< as) = f a :< ((<*>) <$> fs <*> as)
  (f :< fs) <*  (_ :< as) = f :< ((<* ) <$> fs <*> as)
  (_ :< fs)  *> (a :< as) = a :< (( *>) <$> fs <*> as)

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
  foldMap f (a :< as) = f a `mappend` foldMap (foldMap f) as

instance Foldable1 f => Foldable1 (Cofree f) where
  foldMap1 f (a :< as) = f a <> foldMap1 (foldMap1 f) as

instance Traversable f => Traversable (Cofree f) where
  traverse f (a :< as) = (:<) <$> f a <*> traverse (traverse f) as

instance Traversable1 f => Traversable1 (Cofree f) where
  traverse1 f (a :< as) = (:<) <$> f a <.> traverse1 (traverse1 f) as

#ifdef GHC_TYPEABLE
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

instance ComonadStore s w => ComonadStore s (Cofree w) where
  pos (_ :< as) = Class.pos as
  peek s (_ :< as) = extract (Class.peek s as)


instance ComonadTraced m w => ComonadTraced m (Cofree w) where
  trace m = trace m . lower

extracting :: Functor f => (a -> f a) -> Cofree g a -> f (Cofree g a)
extracting f (a :< as) = (:< as) <$> f a
{-# INLINE extracting #-}

unwrapping :: Functor f => (g (Cofree g a) -> f (g (Cofree g a))) -> Cofree g a -> f (Cofree g a)
unwrapping f (a :< as) = (a :<) <$> f as
{-# INLINE unwrapping #-}

telescoping :: (Functor f, Functor g) =>
             [(Cofree g a -> f (Cofree g a)) -> g (Cofree g a) -> f (g (Cofree g a))] ->
              (a -> f a) -> Cofree g a -> f (Cofree g a)
telescoping [] = extracting
telescoping (l:ls) = unwrapping . l . telescoping ls

-- newtype CofreeT f w x = CofreeT { runCofreeT :: w (x, f (CofreeT f w x)) }
