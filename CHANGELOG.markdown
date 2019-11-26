5.1.3 [2019.11.26]
------------------
* Allow building with `template-haskell-2.16` (GHC 8.10).
* Add `Eq{1,2}`, `Ord{1,2}`, `Read{1,2}`, and `Show{1,2}` instances for
  `CofreeF`.

5.1.2 [2019.08.27]
------------------
* Implement more performant versions of `some` and `many` in the `Alternative`
  instance for the final `Alt` encoding.

5.1.1 [2019.05.02]
------------------
* Allow building with `base-4.13` (GHC 8.8).

5.1 [2018.07.03]
----------------
* Generalize the type of `_Free`.
* Allow building with `containers-0.6`.
* Avoid incurring some dependencies when using recent GHCs.

5.0.2 [2018.04.25]
------------------
* Add `Generic` and `Generic1` instances where possible.

5.0.1 [2018.03.07]
------------------
* Fix the build on old GHCs with `transformers-0.4`.

5 [2018.01.28]
--------------
* Add a `Semigroup` instance for `IterT`.
* Add `MonadFail` instances for `IterT` and `FreeT`.
* Add a `Comonad` instance for the free `Applicative`, `Ap`.
* Add `Control.Monad.Free.Ap` and `Control.Monad.Trans.Free.Ap` modules, based
  on the "Applicative Effects in Free Monads" series of articles by Will
  Fancher.
* Derive `Data` instances for `Free` and `Cofree`.
* `Control.Monad.Free.TH` now properly supports `template-haskell-2.11.0.0`. In
  particular, it now supports `GadtC` and `RecGadtC`, which are new
  `template-haskell` forms for representing GADTs.
* Add `telescoped_`, `shoots`, and `leaves` to `Control.Comonad.Cofree`
* Add the `Control.Applicative.Free.Fast` module, based on Dave Menendez's
  article "Free Applicative Functors in Haskell"
* Add `foldFreeT` to `Control.Monad.Trans.Free`
* Improve the `foldMap` and `cutoff` functions for
  `Control.Monad.Free.Church.F`, and add a `Traversable`
* Add a `MonadBase` instance for `FreeT`
* Add a performance test comparing Free and Church interpreters
* The use of `prelude-extras` has been removed. `free` now uses the
  `Data.Functor.Classes` module to give `free`'s datatypes instances of `Eq1`,
  `Ord1`, `Read1`, and `Show1`. Their `Eq`, `Ord`, `Read`, and `Show` instances
  have also been modified to incorporate these classes. For example, what
  previously existed as:

  ```haskell
  instance (Eq (f (Free f a)), Eq a) => Eq (Free f a) where
  ```

  has now been changed to:

  ```haskell
  instance (Eq1 f, Eq a) => Eq (Free f a) where
  ```
* Remove redundant `Functor` constraints from `Control.Alternative.Free`

4.12.4
------
* Removed a number of spurious class constraints.
* Support GHC 8

4.12.3
------
* Support `comonad` 5

4.12.2
------
* Add instances for `ExceptT`: like `ErrorT`, but without an `Error` constraint.
* Support `containers`
* Support `transformers` 0.5


4.12.1
------
* Support GHC 7.4

4.12
----
* Add instances of `MonadCatch` and `MonadThrow` from `exceptions` to `FT`, `FreeT` and `IterT`.
* `semigroupoids` 5, `profunctors` 5, and `bifunctors` 5 support.

4.11
-----
* Pass Monad[FreeT].fail into underlying monad
* Add `retractT`.
* Added `cutoff` for the church encoded free monad.
* `cutoff` now accepts negative numbers.
* Added `intersperseT` and `intercalateT`.
* Added `foldFree` and `foldF`.
* Added some new `template-haskell` toys.

4.10.0.1
------
* Fix for very old `cabal` versions where the `MIN_VERSION_foo` macros aren't negation friendly.

4.10
----
* Redefine `Alternative` and `MonadPlus` instances of `IterT` so that they apply to any underlying `Monad`.
  `mplus` or `<|>` is Capretta's `race` combinator; `mzero` or `empty` is a non-terminating computation.
* Redefine `fail s` for `IterT` as `mzero`, for any string `s`.
* Added `Control.Monad.Trans.Iter.untilJust`, which repeatedly retries a `m (Maybe a)` computation until
  it produces `Just` a value.
* Fix things so that we can build with GHC 7.10, which also uses the name `Alt` in `Data.Monoid`, and which exports `Monoid` from `Prelude`.

4.9
---
* Remove `either` support. Why? It dragged in a large number of dependencies we otherwise don't support, and so is probably best inverted.

4.8.0.1
-------
* Allow complation with older versions of `base`. (Foldable didn't add foldl' until base 4.6)

4.8
-----
* Added a `MonadFree` instance for `EitherT` (frrom the `either` package).
* Support for `transformers` 0.4

4.7.1
-----
* Added more versions of `cutoff`.

4.7
---
* Added `prelude-extras` support. This makes it possible to work without `UndecidableInstances` for most operations.
* Removed the `GHC_TYPEABLE` flag.

4.6.1
-----
* Added `hoistF`

4.6
---
* Víctor López Juan and Fabian Ruch added many documentation improvements and a whole host of proofs of correctness.
* Improvements in the template haskell code generator.
* Added instances for `MonadWriter` and `MonadCont` where appropriate, thanks to Nickolay Kudasov.
* Added `cutoff`, `iterTM`, and `never`.
* Made modifications to some `Typeable` and `Data` instances to work correctly on both GHC 7.8.1rc1 and 7.8.1rc2.
* Removed `Control.MonadPlus.Free`. Use `FreeT f []` instead and the result will be law-abiding.
* Replaced `Control.Alternative.Free` with a new approach that is law-abiding for left-distributive Alternatives.

4.5
-----
* Added `Control.Monad.Free.TH` with `makeFree` to make it easier to write free monads.
* Added missing instances for `MonadFix` and `MonadCont` where appropriate.

4.2
-----
* Added `Control.Monad.Trans.Iter` and `Control.Comonad.Trans.Coiter`.

4.1.1
-----
* Added a default signature to `wrap`, based on a construction by @fizruk.

4.0
---
* Updated to work with `semigroupoids` and `comonad` 4.0
* `instance ComonadCofree Maybe NonEmpty`
* `instance ComonadCofree (Const b) ((,) b)`

3.4.2
-----
* Generalized `liftF`.
* Added `iterM`

3.4.1
-----
* Added support for GHC 7.7's polykinded `Typeable`

3.4
---
* Added instance `MonadFree f (ContT r m)`

3.3.1
-----
* Refactored build system
* Removed upper bounds on my own intra-package dependencies

3.3
---
* Added `Control.Alternative.Free` and `Control.MonadPlus.Free`

3.2
---
* Added `Control.Free.Applicative`
* Moved `Control.Monad.Free.Church` from `kan-extensions` into this package.
