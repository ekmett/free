#include "free-common.h"
#ifdef LIFTED_FUNCTOR_CLASSES
module Data.Functor.Classes.Compat (
    mappend,
    module Data.Functor.Classes,
    ) where

import Data.Functor.Classes

#if !(MIN_VERSION_base(4,8,0))
import Data.Monoid (mappend)
#endif
#else
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Data.Functor.Classes.Compat (
    Lift1 (..),
    on,
    module Data.Functor.Classes,
    ) where

-------------------------------------------------------------------------------
-- transformers-0.4 helpers, copied from prelude-extras
-------------------------------------------------------------------------------

# if !(MIN_VERSION_base(4,8,0))
import Data.Foldable
import Data.Traversable
# endif
import Data.Functor.Classes
import Data.Function (on)

-- If Show1 and Read1 are ever derived by the same mechanism as
-- Show and Read, rather than GND, that will change their behavior
-- here.
newtype Lift1 f a = Lift1 { lower1 :: f a }
  deriving (Functor, Foldable, Traversable, Eq1, Ord1, Show1, Read1)

instance (Eq1 f, Eq a) => Eq (Lift1 f a)       where (==) = eq1
instance (Ord1 f, Ord a) => Ord (Lift1 f a)    where compare = compare1
instance (Show1 f, Show a) => Show (Lift1 f a) where showsPrec = showsPrec1
instance (Read1 f, Read a) => Read (Lift1 f a) where readsPrec = readsPrec1
#endif
