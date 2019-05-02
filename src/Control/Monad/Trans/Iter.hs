{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE DeriveDataTypeable #-}
#include "free-common.h"

-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Trans.Iter
-- Copyright   :  (C) 2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  MPTCs, fundeps
--
-- Based on <http://www.ioc.ee/~tarmo/tday-veskisilla/uustalu-slides.pdf Capretta's Iterative Monad Transformer>
--
-- Unlike 'Free', this is a true monad transformer.
----------------------------------------------------------------------------
module Control.Monad.Trans.Iter
  (
  -- |
  -- Functions in Haskell are meant to be pure. For example, if an expression
  -- has type Int, there should exist a value of the type such that the expression
  -- can be replaced by that value in any context without changing the meaning
  -- of the program.
  --
  -- Some computations may perform side effects (@unsafePerformIO@), throw an
  -- exception (using @error@); or not terminate
  -- (@let infinity = 1 + infinity in infinity@).
  --
  -- While the 'IO' monad encapsulates side-effects, and the 'Either'
  -- monad encapsulates errors, the 'Iter' monad encapsulates
  -- non-termination. The 'IterT' transformer generalizes non-termination to any monadic
  -- computation.
  --
  -- Computations in 'IterT' (or 'Iter') can be composed in two ways:
  --
  -- * /Sequential:/ Using the 'Monad' instance, the result of a computation
  --   can be fed into the next.
  --
  -- * /Parallel:/ Using the 'MonadPlus' instance, several computations can be
  --   executed concurrently, and the first to finish will prevail.
  --   See also the <examples/Cabbage.lhs cabbage example>.

  -- * The iterative monad transformer
    IterT(..)
  -- * Capretta's iterative monad
  , Iter, iter, runIter
  -- * Combinators
  , delay
  , hoistIterT
  , liftIter
  , cutoff
  , never
  , untilJust
  , interleave, interleave_
  -- * Consuming iterative monads
  , retract
  , fold
  , foldM
  -- * IterT ~ FreeT Identity
  , MonadFree(..)
  -- * Examples
  -- $examples
  ) where

import Control.Applicative
import Control.Monad.Catch (MonadCatch(..), MonadThrow(..))
import Control.Monad (ap, liftM, MonadPlus(..), join)
import Control.Monad.Fix
import Control.Monad.Trans.Class
import qualified Control.Monad.Fail as Fail
import Control.Monad.Free.Class
import Control.Monad.State.Class
import Control.Monad.Error.Class
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class
import Control.Monad.Cont.Class
import Control.Monad.IO.Class
import Data.Bifunctor
import Data.Bitraversable
import Data.Either
import Data.Functor.Bind hiding (join)
import Data.Functor.Classes.Compat
import Data.Functor.Identity
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import Data.Typeable
import Data.Data

#if !(MIN_VERSION_base(4,8,0))
import Data.Foldable hiding (fold)
import Data.Traversable hiding (mapM)
#endif

#if !(MIN_VERSION_base(4,11,0))
import Data.Semigroup
#endif

-- | The monad supporting iteration based over a base monad @m@.
--
-- @
-- 'IterT' ~ 'FreeT' 'Identity'
-- @
newtype IterT m a = IterT { runIterT :: m (Either a (IterT m a)) }
#if __GLASGOW_HASKELL__ >= 707
  deriving (Typeable)
#endif

-- | Plain iterative computations.
type Iter = IterT Identity

-- | Builds an iterative computation from one first step.
--
-- prop> runIter . iter == id
iter :: Either a (Iter a) -> Iter a
iter = IterT . Identity
{-# INLINE iter #-}

-- | Executes the first step of an iterative computation
--
-- prop> iter . runIter == id
runIter :: Iter a -> Either a (Iter a)
runIter = runIdentity . runIterT
{-# INLINE runIter #-}

#ifdef LIFTED_FUNCTOR_CLASSES
instance (Eq1 m) => Eq1 (IterT m) where
  liftEq eq = go
    where
      go (IterT x) (IterT y) = liftEq (liftEq2 eq go) x y
#else
instance (Functor m, Eq1 m) => Eq1 (IterT m) where
  eq1 = on eq1 (fmap (fmap Lift1) . runIterT)
#endif

#ifdef LIFTED_FUNCTOR_CLASSES
instance (Eq1 m, Eq a) => Eq (IterT m a) where
#else
instance (Functor m, Eq1 m, Eq a) => Eq (IterT m a) where
#endif
  (==) = eq1

#ifdef LIFTED_FUNCTOR_CLASSES
instance (Ord1 m) => Ord1 (IterT m) where
  liftCompare cmp = go
    where
      go (IterT x) (IterT y) = liftCompare (liftCompare2 cmp go) x y
#else
instance (Functor m, Ord1 m) => Ord1 (IterT m) where
  compare1 = on compare1 (fmap (fmap Lift1) . runIterT)
#endif

#ifdef LIFTED_FUNCTOR_CLASSES
instance (Ord1 m, Ord a) => Ord (IterT m a) where
#else
instance (Functor m, Ord1 m, Ord a) => Ord (IterT m a) where
#endif
  compare = compare1

#ifdef LIFTED_FUNCTOR_CLASSES
instance (Show1 m) => Show1 (IterT m) where
  liftShowsPrec sp sl = go
    where
      goList = liftShowList sp sl
      go d (IterT x) = showsUnaryWith
        (liftShowsPrec (liftShowsPrec2 sp sl go goList) (liftShowList2 sp sl go goList))
        "IterT" d x
#else
instance (Functor m, Show1 m) => Show1 (IterT m) where
  showsPrec1 d (IterT m) = showParen (d > 10) $
    showString "IterT " . showsPrec1 11 (fmap (fmap Lift1) m)
#endif

#ifdef LIFTED_FUNCTOR_CLASSES
instance (Show1 m, Show a) => Show (IterT m a) where
#else
instance (Functor m, Show1 m, Show a) => Show (IterT m a) where
#endif
  showsPrec = showsPrec1

#ifdef LIFTED_FUNCTOR_CLASSES
instance (Read1 m) => Read1 (IterT m) where
  liftReadsPrec rp rl = go
    where
      goList = liftReadList rp rl
      go = readsData $ readsUnaryWith
        (liftReadsPrec (liftReadsPrec2 rp rl go goList) (liftReadList2 rp rl go goList))
        "IterT" IterT
#else
instance (Functor m, Read1 m) => Read1 (IterT m) where
  readsPrec1 d =  readParen (d > 10) $ \r ->
    [ (IterT (fmap (fmap lower1) m),t) | ("IterT",s) <- lex r, (m,t) <- readsPrec1 11 s]
#endif

#ifdef LIFTED_FUNCTOR_CLASSES
instance (Read1 m, Read a) => Read (IterT m a) where
#else
instance (Functor m, Read1 m, Read a) => Read (IterT m a) where
#endif
  readsPrec = readsPrec1

instance Monad m => Functor (IterT m) where
  fmap f = IterT . liftM (bimap f (fmap f)) . runIterT
  {-# INLINE fmap #-}

instance Monad m => Applicative (IterT m) where
  pure = IterT . return . Left
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad m => Monad (IterT m) where
  return = pure
  {-# INLINE return #-}
  IterT m >>= k = IterT $ m >>= either (runIterT . k) (return . Right . (>>= k))
  {-# INLINE (>>=) #-}
#if !MIN_VERSION_base(4,13,0)
  fail = Fail.fail
  {-# INLINE fail #-}
#endif

instance Monad m => Fail.MonadFail (IterT m) where
  fail _ = never
  {-# INLINE fail #-}

instance Monad m => Apply (IterT m) where
  (<.>) = ap
  {-# INLINE (<.>) #-}

instance Monad m => Bind (IterT m) where
  (>>-) = (>>=)
  {-# INLINE (>>-) #-}

instance MonadFix m => MonadFix (IterT m) where
  mfix f = IterT $ mfix $ runIterT . f . either id (error "mfix (IterT m): Right")
  {-# INLINE mfix #-}

instance Monad m => Alternative (IterT m) where
  empty = mzero
  {-# INLINE empty #-}
  (<|>) = mplus
  {-# INLINE (<|>) #-}

-- | Capretta's 'race' combinator. Satisfies left catch.
instance Monad m => MonadPlus (IterT m) where
  mzero = never
  {-# INLINE mzero #-}
  (IterT x) `mplus` (IterT y) = IterT $ x >>= either
                                (return . Left)
                                (flip liftM y . second . mplus)
  {-# INLINE mplus #-}

instance MonadTrans IterT where
  lift = IterT . liftM Left
  {-# INLINE lift #-}

instance Foldable m => Foldable (IterT m) where
  foldMap f = foldMap (either f (foldMap f)) . runIterT
  {-# INLINE foldMap #-}

instance Foldable1 m => Foldable1 (IterT m) where
  foldMap1 f = foldMap1 (either f (foldMap1 f)) . runIterT
  {-# INLINE foldMap1 #-}

instance (Monad m, Traversable m) => Traversable (IterT m) where
  traverse f (IterT m) = IterT <$> traverse (bitraverse f (traverse f)) m
  {-# INLINE traverse #-}

instance (Monad m, Traversable1 m) => Traversable1 (IterT m) where
  traverse1 f (IterT m) = IterT <$> traverse1 go m where
    go (Left a) = Left <$> f a
    go (Right a) = Right <$> traverse1 f a
  {-# INLINE traverse1 #-}

instance MonadReader e m => MonadReader e (IterT m) where
  ask = lift ask
  {-# INLINE ask #-}
  local f = hoistIterT (local f)
  {-# INLINE local #-}

instance MonadWriter w m => MonadWriter w (IterT m) where
  tell = lift . tell
  {-# INLINE tell #-}
  listen (IterT m) = IterT $ liftM concat' $ listen (fmap listen `liftM` m)
    where
      concat' (Left  x, w) = Left (x, w)
      concat' (Right y, w) = Right $ second (w `mappend`) <$> y
  pass m = IterT . pass' . runIterT . hoistIterT clean $ listen m
    where
      clean = pass . liftM (\x -> (x, const mempty))
      pass' = join . liftM g
      g (Left  ((x, f), w)) = tell (f w) >> return (Left x)
      g (Right f)           = return . Right . IterT . pass' . runIterT $ f
#if MIN_VERSION_mtl(2,1,1)
  writer w = lift (writer w)
  {-# INLINE writer #-}
#endif

instance MonadState s m => MonadState s (IterT m) where
  get = lift get
  {-# INLINE get #-}
  put s = lift (put s)
  {-# INLINE put #-}
#if MIN_VERSION_mtl(2,1,1)
  state f = lift (state f)
  {-# INLINE state #-}
#endif

instance MonadError e m => MonadError e (IterT m) where
  throwError = lift . throwError
  {-# INLINE throwError #-}
  IterT m `catchError` f = IterT $ liftM (fmap (`catchError` f)) m `catchError` (runIterT . f)

instance MonadIO m => MonadIO (IterT m) where
  liftIO = lift . liftIO

instance MonadCont m => MonadCont (IterT m) where
  callCC f = IterT $ callCC (\k -> runIterT $ f (lift . k . Left))

instance Monad m => MonadFree Identity (IterT m) where
  wrap = IterT . return . Right . runIdentity
  {-# INLINE wrap #-}

instance MonadThrow m => MonadThrow (IterT m) where
  throwM = lift . throwM
  {-# INLINE throwM #-}

instance MonadCatch m => MonadCatch (IterT m) where
  catch (IterT m) f = IterT $ liftM (fmap (`Control.Monad.Catch.catch` f)) m `Control.Monad.Catch.catch` (runIterT . f)
  {-# INLINE catch #-}

-- | Adds an extra layer to a free monad value.
--
-- In particular, for the iterative monad 'Iter', this makes the
-- computation require one more step, without changing its final
-- result.
--
-- prop> runIter (delay ma) == Right ma
delay :: (Monad f, MonadFree f m) => m a -> m a
delay = wrap . return
{-# INLINE delay #-}

-- |
-- 'retract' is the left inverse of 'lift'
--
-- @
-- 'retract' . 'lift' = 'id'
-- @
retract :: Monad m => IterT m a -> m a
retract m = runIterT m >>= either return retract

-- | Tear down a 'Free' 'Monad' using iteration.
fold :: Monad m => (m a -> a) -> IterT m a -> a
fold phi (IterT m) = phi (either id (fold phi) `liftM` m)

-- | Like 'fold' with monadic result.
foldM :: (Monad m, Monad n) => (m (n a) -> n a) -> IterT m a -> n a
foldM phi (IterT m) = phi (either return (foldM phi) `liftM` m)

-- | Lift a monad homomorphism from @m@ to @n@ into a Monad homomorphism from @'IterT' m@ to @'IterT' n@.
hoistIterT :: Monad n => (forall a. m a -> n a) -> IterT m b -> IterT n b
hoistIterT f (IterT as) = IterT (fmap (hoistIterT f) `liftM` f as)

-- | Lifts a plain, non-terminating computation into a richer environment.
-- 'liftIter' is a 'Monad' homomorphism.
liftIter :: (Monad m) => Iter a -> IterT m a
liftIter = hoistIterT (return . runIdentity)

-- | A computation that never terminates
never :: (Monad f, MonadFree f m) => m a
never = delay never

-- | Repeatedly run a computation until it produces a 'Just' value.
-- This can be useful when paired with a monad that has side effects.
--
-- For example, we may have @genId :: IO (Maybe Id)@ that uses a random
-- number generator to allocate ids, but fails if it finds a collision.
-- We can repeatedly run this with
--
-- @
-- 'retract' ('untilJust' genId) :: IO Id
-- @
untilJust :: (Monad m) => m (Maybe a) -> IterT m a
untilJust f = maybe (delay (untilJust f)) return =<< lift f
{-# INLINE untilJust #-}

-- | Cuts off an iterative computation after a given number of
-- steps. If the number of steps is 0 or less, no computation nor
-- monadic effects will take place.
--
-- The step where the final value is produced also counts towards the limit.
--
-- Some examples (@n ≥ 0@):
--
-- @
-- 'cutoff' 0     _        ≡ 'return' 'Nothing'
-- 'cutoff' (n+1) '.' 'return' ≡ 'return' '.' 'Just'
-- 'cutoff' (n+1) '.' 'lift'   ≡ 'lift' '.' 'liftM' 'Just'
-- 'cutoff' (n+1) '.' 'delay'  ≡ 'delay' . 'cutoff' n
-- 'cutoff' n     'never'    ≡ 'iterate' 'delay' ('return' 'Nothing') '!!' n
-- @
--
-- Calling @'retract' '.' 'cutoff' n@ is always terminating, provided each of the
-- steps in the iteration is terminating.
cutoff :: (Monad m) => Integer -> IterT m a -> IterT m (Maybe a)
cutoff n | n <= 0 = const $ return Nothing
cutoff n          = IterT . liftM (either (Left . Just)
                                       (Right . cutoff (n - 1))) . runIterT

-- | Interleaves the steps of a finite list of iterative computations, and
--   collects their results.
--
--   The resulting computation has as many steps as the longest computation
--   in the list.
interleave :: Monad m => [IterT m a] -> IterT m [a]
interleave ms = IterT $ do
  xs <- mapM runIterT ms
  if null (rights xs)
     then return . Left $ lefts xs
     else return . Right . interleave $ map (either return id) xs
{-# INLINE interleave #-}

-- | Interleaves the steps of a finite list of computations, and discards their
--   results.
--
--   The resulting computation has as many steps as the longest computation
--   in the list.
--
--   Equivalent to @'void' '.' 'interleave'@.
interleave_ :: (Monad m) => [IterT m a] -> IterT m ()
interleave_ [] = return ()
interleave_ xs = IterT $ liftM (Right . interleave_ . rights) $ mapM runIterT xs
{-# INLINE interleave_ #-}

instance (Monad m, Semigroup a, Monoid a) => Monoid (IterT m a) where
  mempty = return mempty
  mappend = (<>)
  mconcat = mconcat' . map Right
    where
      mconcat' :: (Monad m, Monoid a) => [Either a (IterT m a)] -> IterT m a
      mconcat' ms = IterT $ do
        xs <- mapM (either (return . Left) runIterT) ms
        case compact xs of
          [l@(Left _)] -> return l
          xs' -> return . Right $ mconcat' xs'
      {-# INLINE mconcat' #-}

      compact :: (Monoid a) => [Either a b] -> [Either a b]
      compact []               = []
      compact (r@(Right _):xs) = r:(compact xs)
      compact (   Left a  :xs)  = compact' a xs

      compact' a []               = [Left a]
      compact' a (r@(Right _):xs) = (Left a):(r:(compact xs))
      compact' a (  (Left a'):xs) = compact' (a `mappend` a') xs

instance (Monad m, Semigroup a) => Semigroup (IterT m a) where
  x <> y = IterT $ do
    x' <- runIterT x
    y' <- runIterT y
    case (x', y') of
      ( Left a, Left b)  -> return . Left  $ a <> b
      ( Left a, Right b) -> return . Right $ liftM (a <>) b
      (Right a, Left b)  -> return . Right $ liftM (<> b) a
      (Right a, Right b) -> return . Right $ a <> b

#if __GLASGOW_HASKELL__ < 707
instance Typeable1 m => Typeable1 (IterT m) where
  typeOf1 t = mkTyConApp freeTyCon [typeOf1 (f t)] where
    f :: IterT m a -> m a
    f = undefined

freeTyCon :: TyCon
#if __GLASGOW_HASKELL__ < 704
freeTyCon = mkTyCon "Control.Monad.Iter.IterT"
#else
freeTyCon = mkTyCon3 "free" "Control.Monad.Iter" "IterT"
#endif
{-# NOINLINE freeTyCon #-}

#else
#define Typeable1 Typeable
#endif

instance
  ( Typeable1 m, Typeable a
  , Data (m (Either a (IterT m a)))
  , Data a
  ) => Data (IterT m a) where
    gfoldl f z (IterT as) = z IterT `f` as
    toConstr IterT{} = iterConstr
    gunfold k z c = case constrIndex c of
        1 -> k (z IterT)
        _ -> error "gunfold"
    dataTypeOf _ = iterDataType
    dataCast1 f  = gcast1 f

iterConstr :: Constr
iterConstr = mkConstr iterDataType "IterT" [] Prefix
{-# NOINLINE iterConstr #-}

iterDataType :: DataType
iterDataType = mkDataType "Control.Monad.Iter.IterT" [iterConstr]
{-# NOINLINE iterDataType #-}

{- $examples

* <examples/MandelbrotIter.lhs Rendering the Mandelbrot set>

* <examples/Cabbage.lhs The wolf, the sheep and the cabbage>

-}
