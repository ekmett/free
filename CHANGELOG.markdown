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
