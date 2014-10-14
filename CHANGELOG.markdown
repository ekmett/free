5.0
---
* Redefine `Alternative` and `MonadPlus` instances of `IterT` so that they apply to any underlying `Monad`.
  `mplus` or `<|>` is Capretta's `race` combinator; `mzero` or `empty` is a non-terminating computation.
* Redefine `fail s` for `IterT` as `mzero`, for any string `s`.

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
