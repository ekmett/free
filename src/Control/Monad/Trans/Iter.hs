{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE DeriveDataTypeable #-}

#ifndef MIN_VERSION_MTL
#define MIN_VERSION_MTL(x,y,z) 1
#endif

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

  -- * The iterative monad transformer
    IterT(..)
  -- * Capretta's iterative monad
  , Iter, iter, runIter
  -- * Combinators
  , delay
  , hoistIterT
  , liftIter
  , cut
  , never
  -- * Consuming iterative monads
  , retract
  , fold
  , foldM
  -- * IterT ~ FreeT Identity
  , MonadFree(..)
  -- * Example
  -- $example
  ) where

import Control.Applicative
import Control.Monad (ap, liftM, MonadPlus(..))
import Control.Monad.Fix
import Control.Monad.Trans.Class
import Control.Monad.Free.Class
import Control.Monad.State.Class
import Control.Monad.Error.Class
import Control.Monad.Reader.Class
import Control.Monad.Cont.Class
import Control.Monad.IO.Class
import Data.Bifunctor
import Data.Bitraversable
import Data.Functor.Bind
import Data.Functor.Identity
import Data.Foldable hiding (fold)
import Data.Traversable
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import Data.Typeable

#ifdef GHC_TYPEABLE
import Data.Data
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

instance Eq (m (Either a (IterT m a))) => Eq (IterT m a) where
  IterT m == IterT n = m == n

instance Ord (m (Either a (IterT m a))) => Ord (IterT m a) where
  compare (IterT m) (IterT n) = compare m n

instance Show (m (Either a (IterT m a))) => Show (IterT m a) where
  showsPrec d (IterT m) = showParen (d > 10) $
    showString "IterT " . showsPrec 11 m

instance Read (m (Either a (IterT m a))) => Read (IterT m a) where
  readsPrec d =  readParen (d > 10) $ \r ->
    [ (IterT m,t) | ("IterT",s) <- lex r, (m,t) <- readsPrec 11 s]

instance Monad m => Functor (IterT m) where
  fmap f = IterT . liftM (bimap f (fmap f)) . runIterT
  {-# INLINE fmap #-}

instance Monad m => Applicative (IterT m) where
  pure = IterT . return . Left
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad m => Monad (IterT m) where
  return = IterT . return . Left
  {-# INLINE return #-}
  IterT m >>= k = IterT $ m >>= either (runIterT . k) (return . Right . (>>= k))
  {-# INLINE (>>=) #-}
  fail = IterT . fail
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

instance MonadPlus m => Alternative (IterT m) where
  empty = IterT mzero
  {-# INLINE empty #-}
  IterT a <|> IterT b = IterT (mplus a b)
  {-# INLINE (<|>) #-}

instance MonadPlus m => MonadPlus (IterT m) where
  mzero = IterT mzero
  {-# INLINE mzero #-}
  IterT a `mplus` IterT b = IterT (mplus a b)
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

instance (Functor m, MonadReader e m) => MonadReader e (IterT m) where
  ask = lift ask
  {-# INLINE ask #-}
  local f = hoistIterT (local f)
  {-# INLINE local #-}

instance (Functor m, MonadState s m) => MonadState s (IterT m) where
  get = lift get
  {-# INLINE get #-}
  put s = lift (put s)
  {-# INLINE put #-}
#if MIN_VERSION_mtl(2,1,1)
  state f = lift (state f)
  {-# INLINE state #-}
#endif

instance (Functor m, MonadError e m) => MonadError e (IterT m) where
  throwError = lift . throwError
  {-# INLINE throwError #-}
  IterT m `catchError` f = IterT $ (liftM (fmap (`catchError` f)) m) `catchError` (runIterT . f)

instance (Functor m, MonadIO m) => MonadIO (IterT m) where
  liftIO = lift . liftIO

instance (MonadCont m) => MonadCont (IterT m) where
  callCC f = IterT $ callCC (\k -> runIterT $ f (lift . k . Left))

instance Monad m => MonadFree Identity (IterT m) where
  wrap = IterT . return . Right . runIdentity
  {-# INLINE wrap #-}

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

-- | Cuts off an iterative computation after a given number of
-- steps. If the number of steps is 0 or less, no computation nor
-- monadic effects will take place.
--
-- The step where the final value is produced also counts towards the limit.
--
-- Some examples (n ≥ 0):
--
-- prop> cut 0     _        == return Nothing
-- prop> cut (n+1) . return == return . Just
-- prop> cut (n+1) . lift   ==   lift . liftM Just
-- prop> cut (n+1) . delay  ==  delay . cut n
-- prop> cut n     never    == iterate delay (return Nothing) !! n
--
-- Calling 'retract . cut n' is always terminating, provided each of the
-- steps in the iteration is terminating.
cut :: (Monad m) => Integer -> IterT m a -> IterT m (Maybe a)
cut n | n <= 0 = const $ return Nothing
cut n          = IterT . liftM (either (Left . Just)
                                       (Right . cut (n - 1))) . runIterT

#if defined(GHC_TYPEABLE) && __GLASGOW_HASKELL__ < 707
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

#endif

-- BEGIN MandelbrotIter.lhs
{- $example
This is literate Haskell! To run the example, open the source and copy
this comment block into a new file with '.lhs' extension. Compiling to an executable
file with the @-O2@ optimization level is recomended.

For example: @ghc -o 'mandelbrot_iter' -O2 MandelbrotIter.lhs ; ./mandelbrot_iter@

@ \{\-\# LANGUAGE PackageImports \#\-\} @

> {-# LANGUAGE PackageImports #-}

> import Control.Arrow
> import Control.Monad.Trans.Iter
> import "mtl" Control.Monad.Reader
> import "mtl" Control.Monad.List
> import "mtl" Control.Monad.Identity
> import Control.Monad.IO.Class
> import Data.Complex 
> import Graphics.HGL (runGraphics, Window, withPen,
>                      line, RGB (RGB), RedrawMode (Unbuffered, DoubleBuffered), openWindowEx,
>                      drawInWindow, mkPen, Style (Solid))

Some fractals can be defined by infinite sequences of complex numbers. For example,
to render the <https://en.wikipedia.org/wiki/Mandelbrot_set Mandelbrot set>,
the following sequence is generated for each point @c@ in the complex plane:

  z₀ = c     

  z₁ = z₀² + c     

  z₂ = z₁² + c     

  …     

If, after some iterations, |z_i| ≥ 2, the point is not in the set. We
can compute if a point is not in the Mandelbrot set this way:

@
 escaped :: Complex Double -> Int
 escaped c = loop 0 0 where
   loop z n = if (magnitude z) >= 2 then n
                                    else loop (z*z + c) (n+1)
@

If @c@ is not in the Mandelbrot set, we get the number of iterations required to
prove that fact. But, if @c@ is in the mandelbrot set, 'escaped' will
run forever.

We can use the 'Iter' monad to delimit this effect. By applying
'delay' before the recursive call, we decompose the computation into
terminating steps.

> escaped :: Complex Double -> Iter Int
> escaped c = loop 0 0 where
>   loop z n = if (magnitude z) >= 2 then return n
>                                    else delay $ loop (z*z + c) (n+1)
>

If we draw each point on a canvas after it escapes, we can get a _negative_
image of the Mandelbrot set. Drawing pixels is a side-effect, so it
should happen inside the IO monad. Also, we want to have an
environment to store the size of the canvas, and the target window.

By using 'IterT', we can add all these behaviours to our non-terminating
computation.

> data Canvas = Canvas { width :: Int, height :: Int, window :: Window }
> 
> type FractalM a = IterT (ReaderT Canvas IO) a

Any simple, non-terminating computation can be lifted into a richer environment.

> escaped' :: Complex Double -> IterT (ReaderT Canvas IO) Int
> escaped' = liftIter . escaped

Then, to draw a point, we can just retrieve the number of iterations until it
finishes, and draw it. The color will depend on the number of iterations.

> mandelbrotPoint :: (Int, Int) -> FractalM ()
> mandelbrotPoint p = do
>   c <- scale p
>   n <- escaped' c
>   let color =  if (even n) then RGB   0   0 255 -- Blue
>                            else RGB   0   0 127 -- Darker blue
>   drawPoint color p

The pixels on the screen don't match the region in the complex plane where the
fractal is; we need to map them first. The region we are interested in is
Im z = [-1,1], Re z = [-2,1].

> scale :: (Int, Int) -> FractalM (Complex Double)
> scale (xi,yi) = do
>   (w,h) <- asks $ (fromIntegral . width) &&& (fromIntegral . height)
>   let (x,y) = (fromIntegral xi, fromIntegral yi)
>   let im = (-y + h / 2     ) / (h/2)
>   let re = ( x - w * 2 / 3 ) / (h/2) 
>   return $ re :+ im

Drawing a point is equivalent to drawing a line of length one.

> drawPoint :: RGB -> (Int,Int) -> FractalM ()
> drawPoint color p@(x,y) = do
>   w <- asks window
>   let point = line (x,y) (x+1, y+1)
>   liftIO $ drawInWindow w $ mkPen Solid 1 color (flip withPen point)


We may want to draw more than one point. However, if we just sequence the computations
monadically, the first point that is not a member of the set will block the whole
process. We need advance all the points at the same pace.

> iterForM_ :: (Monad m) => [a] -> (a -> IterT m ()) -> IterT m ()
> iterForM_ as f = exhaust $ map f as
>   where
>     exhaust :: (Monad m) => [IterT m ()] -> IterT m ()
>     exhaust [] = return ()
>     exhaust xs = IterT $ do
>       l <- mapM runIterT xs
>       return $ Right $ exhaust $ l >>= (either (const []) (:[]))

With this combinator in place, drawing the complete set is just drawing each
of the possible points:

> drawMandelbrot :: FractalM ()
> drawMandelbrot = do
>   (w,h) <- asks $ width &&& height
>   let ps = [(x,y) | x <- [0 .. (w-1)], y <- [0 .. (h-1)]]
>   iterForM_ ps mandelbrotPoint

To run this computation, we can just use @retract@, which will run indefinitely:

> runFractalM :: Canvas -> FractalM a -> IO a
> runFractalM canvas  = flip runReaderT canvas . retract

Or, we can trade non-termination for getting an incomplete result,
by cutting off after a certain number of steps.

> runFractalM' :: Integer -> Canvas -> FractalM a -> IO (Maybe a)
> runFractalM' n canvas  = flip runReaderT canvas . retract . cut n

Thanks to the 'IterT' transformer, we can separate timeout concerns from
computational concerns.

> main :: IO ()
> main = do
>   let windowWidth = 800
>   let windowHeight = 480
>   runGraphics $ do
>     w <- openWindowEx "Mandelbrot" Nothing (windowWidth, windowHeight) DoubleBuffered (Just 1)
>     let canvas = Canvas windowWidth windowHeight w
>     runFractalM' 100 canvas drawMandelbrot
>     putStrLn $ "Fin"

-}
-- END MandelbrotIter.lhs
