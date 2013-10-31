4.1.2
-----
* Added `Control.Monad.Iter`

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
