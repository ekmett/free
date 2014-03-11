MonadZip instance for Cofree
============================

For every functor `f` with `Alternative` and `MonadZip` instances,
`Cofree f` is an instance of `MonadZip`.

The claim follows as a corollary from the [`MonadZip` instance theorem
for `CofreeT`](../Trans/Cofree/instance-MonadZip-CofreeT.md) when `m` is
set to be `Identity`, which obviously has an instance of `MonadZip`.
