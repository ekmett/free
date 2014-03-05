MonadTrans instance for CofreeT
===============================

If the ```Functor f``` is an instance of ```Plus``` (or of ```Alternative```)
then CofreeT is a monad transformer.

## Lift `return`

```haskell
lift (return x)

== {- definition lift -}

C $ (liftM (:< empty) (return x))

== {- definition liftM -}

C $ (return x) >>= (\a -> return $ a :< empty)

== {- monad left identity -}

C $ return $ x :< empty

== {- definition -}

return x
```

## Lift distributes over `bind`

```haskell
lift (m >>= f)

== {- definition lift -}

C $ (liftM (:< empty) (m >>= f))

== {- definition liftM -}

C $ (m >>= f) >>= (\a -> return $ a :< empty)

== {- α-equivalence  -}

C $ m >>= f >>= (\b -> return $ b :< empty)

== {- η-equivalence  -}

C $  m                     >>= \a ->
     f a                   >>= \b ->
     return $ b :< empty

== {- empty invariant under fmap, empty identity  -}

C $  m                     >>= \a ->
     f a                   >>= \b ->
     return $ b :< (empty <|> fmap (>>= …) empty)

== {- left identity -}

C $  m                     >>= \a ->
     return (a :< empty)   >>= \a :< n ->
     f a                   >>= \b ->
     return (b :< empty)   >>= \b :< m ->
     return $ b :< (n <|> fmap (>>= …) m)


== {- associativity of >>= -}

C $ (m >>= (\a -> return $ a :< empty)) >>= \a :< n ->
    ((f a) >>= (\b -> return $ b :< empty)) >>= \b :< m ->
    return $ b :< (n <|> fmap (>>= …) m)

== {- pattern matching on CofreeF -}

(C (m >>= (\a -> return $ a :< empty)) >>= (\x -> C ((f x) >>= (\b -> return b :< empty)))

== {- definition lift -}

(C (m >>= (\a -> return $ a :< empty)) >>= (\x -> lift (f x))

== {- definition lift -}

lift m >>= (lift . f)
```




