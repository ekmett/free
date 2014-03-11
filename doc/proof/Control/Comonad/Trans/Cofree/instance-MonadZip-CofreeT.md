MonadZip instance for CofreeT
=============================

For every monad `m` with a `MonadZip` instance and functor `f` with
`Alternative` and `MonadZip` instances, `CofreeT f m` is an instance of
`MonadZip`.

```haskell
instance (Alternative f, MonadZip f, MonadZip m) => MonadZip (CofreeT f m) where
  mzip (CofreeT ma) (CofreeT mb) = CofreeT $ do
    (a :< fa, b :< fb) <- mzip ma mb
    return $ (a, b) :< (uncurry mzip <$> mzip fa fb)
```

This definition is equivalent to that of the `Cofree` module if `m` is
chosen to be the `Identity` monad.

The claim follows directly from the two lemmata below, which establish
the `MonadZip` laws for naturality and information preservation
respectively, and the [`Monad` instance theorem for
`CofreeT`](instance-Monad-CofreeT.md).

In the following, the tokens `CofreeT` and `runCofreeT` are abbreviated
as `C` and `unC` respectively.

## Naturality

```haskell
liftM (f *** g) (mzip ma mb) == mzip (liftM f ma) (liftM g mb)
```

### Proof.

```haskell
   liftM (f *** g) (mzip ma mb)

== {- Definition of `liftM` -}

   mzip ma mb >>= return . (f *** g)

== {- Definition of `mzip` -}

   C $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
           return $ (a, b) :< (uncurry mzip <$> mzip fa fb)
   >>= return . (f *** g)

== {- Definition of `(>>=)` -}

   C $ do  c  :< m  <- do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
                           return $ (a, b) :< (uncurry mzip <$> mzip fa fb)
           d  :< n  <- unC $ return $ (f *** g) c
           return $ d :< (n <|> fmap (>>= return . f *** g) m)

== {- `Monad` law `m >>= (\x -> k x >>= h) == (m >>= k) >>= h` -}

   C $ do  a  :< fa  <- unC ma
           c  :< m   <- do  b :< fb <- unC mb
                            return $ (a, b) :< (uncurry mzip <$> mzip fa fb)
           d  :< n   <- unC $ return $ (f *** g) c
           return $ d :< (n <|> fmap (>>= return . f *** g) m)

== {- `Monad` law `m >>= (\x -> k x >>= h) == (m >>= k) >>= h` -}

   C $ do  a  :< fa  <- unC ma
           b  :< fb  <- unC mb
           c  :< m   <- return $ (a, b) :< (uncurry mzip <$> mzip fa fb)
           d  :< n   <- unC $ return $ (f *** g) c
           return $ d :< (n <|> fmap (>>= return . f *** g) m)

== {- `Monad` law `return a >>= k == k a` -}

   C $ do  a  :< fa  <- unC ma
           b  :< fb  <- unC mb
           d  :< n   <- unC $ return $ (f *** g) (a, b)
           return $ d :< (n <|> fmap (>>= return . f *** g) (uncurry mzip <$> mzip fa fb))

== {- Definition of `return` -}

   C $ do  a  :< fa  <- unC ma
           b  :< fb  <- unC mb
           d  :< n   <- unC $ C $ return $ (f *** g) (a, b) :< empty
           return $ d :< (n <|> fmap (>>= return . f *** g) (uncurry mzip <$> mzip fa fb))

== {- Unpack -}

   C $ do  a  :< fa  <- unC ma
           b  :< fb  <- unC mb
           d  :< n   <- return $ (f *** g) (a, b) :< empty
           return $ d :< (n <|> fmap (>>= return . f *** g) (uncurry mzip <$> mzip fa fb))

== {- `Monad` law `return a >>= k == k a` -}

   C $ do  a  :< fa  <- unC ma
           b  :< fb  <- unC mb
           return $ (f *** g) (a, b) :< (empty <|> fmap (>>= return . f *** g) (uncurry mzip <$> mzip fa fb))

== {- Identity of `<|>` -}

   C $ do  a  :< fa  <- unC ma
           b  :< fb  <- unC mb
           return $ (f *** g) (a, b) :< fmap (>>= return . f *** g) (uncurry mzip <$> mzip fa fb)

== {- Definition of `liftM` -}

   C $ do  a  :< fa  <- unC ma
           b  :< fb  <- unC mb
           return $ (f *** g) (a, b) :< fmap (liftM (f *** g)) (uncurry mzip <$> mzip fa fb)

== {- Definition of `<$>` -}

   C $ do  a  :< fa  <- unC ma
           b  :< fb  <- unC mb
           return $ (f *** g) (a, b) :< fmap (liftM (f *** g)) (fmap (uncurry mzip) $ mzip fa fb)

== {- `Functor` composition -}

   C $ do  a  :< fa  <- unC ma
           b  :< fb  <- unC mb
           return $ (f *** g) (a, b) :< fmap (liftM (f *** g) . uncurry mzip) $ mzip fa fb

== {- Coinduction hypothesis -}

   C $ do  a  :< fa  <- unC ma
           b  :< fb  <- unC mb
           return $ (f *** g) (a, b) :< fmap (uncurry mzip . liftM f *** liftM g) $ mzip fa fb

== {- `Functor` composition -}

   C $ do  c  :< m   <- unC ma
           k  :< o   <- unC mb
           return $ (f c, g k) :< fmap (uncurry mzip) $ fmap (liftM f *** liftM g) $ mzip m o

== {- `MonadZip` naturality -}

   C $ do  c  :< m   <- unC ma
           k  :< o   <- unC mb
           return $ (f c, g k) :< fmap (uncurry mzip) $ mzip (fmap (liftM f) m) (fmap (liftM g) o))

== {- Definition of `<$>` -}

   C $ do  c  :< m   <- unC ma
           k  :< o   <- unC mb
           return $ (f c, g k) :< (uncurry mzip <$> mzip (fmap (liftM f) m) (fmap (liftM g) o))

== {- Definition of `liftM` -}

   C $ do  c  :< m   <- unC ma
           k  :< o   <- unC mb
           return $ (f c, g k) :< (uncurry mzip <$> mzip (fmap (>>= return . f) m) (fmap (>>= return . g) o))

== {- `Monad` law `return a >>= k == k a` -}

   C $ do  c  :< m   <- unC ma
           a  :< fa  <- return $ f c :< fmap (>>= return . f) m
           k  :< o   <- unC mb
           b  :< fb  <- return $ g k :< fmap (>>= return . g) o
           return $ (a, b) :< (uncurry mzip <$> mzip fa fb)

== {- `Alternative` identity -}

   C $ do  c  :< m   <- unC ma
           a  :< fa  <- return $ f c :< (empty <|> fmap (>>= return . f) m)
           k  :< o   <- unC mb
           b  :< fb  <- return $ g k :< (empty <|> fmap (>>= return . g) o)
           return $ (a, b) :< (uncurry mzip <$> mzip fa fb)

== {- `Monad` law `return a >>= k == k a` -}

   C $ do  c  :< m   <- unC ma
           d  :< n   <- return $ f c :< empty
           a  :< fa  <- return $ d :< (n <|> fmap (>>= return . f) m)
           k  :< o   <- unC mb
           l  :< p   <- return $ g k :< empty
           b  :< fb  <- return $ l :< (p <|> fmap (>>= return . g) o)
           return $ (a, b) :< (uncurry mzip <$> mzip fa fb)

== {- Unpack -}

   C $ do  c  :< m   <- unC ma
           d  :< n   <- unC $ C $ return $ f c :< empty
           a  :< fa  <- unC $ C $ return $ d :< (n <|> fmap (>>= return . f) m)
           k  :< o   <- unC mb
           l  :< p   <- unC $ C $ return $ g k :< empty
           b  :< fb  <- unC $ C $ return $ l :< (p <|> fmap (>>= return . g) o)
           return $ (a, b) :< (uncurry mzip <$> mzip fa fb)

== {- Definition of `return` -}

   C $ do  c  :< m   <- unC ma
           d  :< n   <- unC $ return $ f c
           a  :< fa  <- unC $ C $ return $ d :< (n <|> fmap (>>= return . f) m)
           k  :< o   <- unC mb
           l  :< p   <- unC $ return $ g k
           b  :< fb  <- unC $ C $ return $ l :< (p <|> fmap (>>= return . g) o)
           return $ (a, b) :< (uncurry mzip <$> mzip fa fb)

== {- `Monad` law `m >>= (\x -> k x >>= h) == (m >>= k) >>= h` -}

   C $ do  c  :< m   <- unC ma
           a  :< fa  <- unC $ C $ do  d :< n <- unC $ return $ return $ f c
                                      return $ d :< (n <|> fmap (>>= return . f) m)
           k  :< o   <- unC mb
           b  :< fb  <- unC $ C $ do  l :< p <- unC $ return $ return g k
                                      return $ l :< (p <|> fmap (>>= return . g) o)
           return $ (a, b) :< (uncurry mzip <$> mzip fa fb)

== {- `Monad` law `m >>= (\x -> k x >>= h) == (m >>= k) >>= h` -}

   C $ do  a  :< fa  <- unC $ C $ do  c  :< m  <- unC ma
                                      d  :< n  <- unC $ return $ f c
                                      return $ d :< (n <|> fmap (>>= return . f) m)
           b  :< fb  <- unC $ C $ do  k  :< o  <- unC mb
                                      l  :< p  <- unC $ return $ g k
                                      return $ l :< (p <|> fmap (>>= return . g) o)
           return $ (a, b) :< (uncurry mzip <$> mzip fa fb)

== {- Definition of `(>>=)` -}

   C $ do  a  :< fa  <- unC $ ma >>= return . f
           b  :< fb  <- unC $ mb >>= return . g
           return $ (a, b) :< (uncurry mzip <$> mzip fa fb)

== {- Definition of `liftM` -}

   C $ do  a  :< fa  <- unC $ liftM f ma
           b  :< fb  <- unC $ liftM g mb
           return $ (a, b) :< (uncurry mzip <$> mzip fa fb)

== {- Definition of `mzip` -}

   mzip (liftM f ma) (liftM g mb)

.
```

## Information Preservation

```haskell
liftM (const ()) ma == liftM (const ()) mb --> munzip (mzip ma mb) == (ma, mb)
```

### Proof.

```haskell
   munzip (mzip ma mb)

== {- Definition of `munzip` -}

   (,)
   (liftM fst  $ mzip ma mb)
   (liftM snd  $ mzip ma mb)

== {- Definition of `mzip` -}

   (,)
   (liftM fst  $ C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
                          return $ (a, b) :< fmap (uncurry mzip) $ mzip fa fb)
   (liftM snd  $ C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
                          return $ (a, b) :< fmap (uncurry mzip) $ mzip fa fb)

== {- Definition of `liftM` -}

   (,)
   (C $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
            return $ (a, b) :< fmap (uncurry mzip) $ mzip fa fb
    >>= return . fst)
   (C $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
            return $ (a, b) :< fmap (uncurry mzip) $ mzip fa fb
    >>= return . snd)

== {- Definition of `(>>=)` -}

   (,)
   (C  $ do  c  :< fc  <- do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
                              return $ (a, b) :< fmap (uncurry mzip) $ mzip fa fb
             d  :< fd  <- unC $ return $ fst c
             return $ d :< $ fd <|> fmap (>>= return . fst) fc)
   (C  $ do  c  :< fc  <- do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
                              return $ (a, b) :< fmap (uncurry mzip) $ mzip fa fb
             d  :< fd  <- unC $ return $ snd c
             return $ d :< $ fd <|> fmap (>>= return . snd) fc)

== {- `Monad` law `m >>= (\x -> k x >>= h) == (m >>= k) >>= h` -}

   (,)
   (C  $ do  (a :< fa, b :< fb)  <- mzip (unC ma) (unC mb)
             c  :< fc            <- return $ (a, b) :< fmap (uncurry mzip) $ mzip fa fb
             d  :< fd            <- unC $ return $ fst c
             return $ d :< $ fd <|> fmap (>>= return . fst) fc)
   (C  $ do  (a :< fa, b :< fb)  <- mzip (unC ma) (unC mb)
             c  :< fc            <- return $ (a, b) :< fmap (uncurry mzip) $ mzip fa fb
             d  :< fd            <- unC $ return $ snd c
             return $ d :< $ fd <|> fmap (>>= return . snd) fc)

== {- `Monad` law `return a >>= k == k a` -}

   (,)
   (C  $ do  (a :< fa, b :< fb)  <- mzip (unC ma) (unC mb)
             d  :< fd            <- unC $ return $ fst (a, b)
             return $ d :< $ fd <|> fmap (>>= return . fst) $ fmap (uncurry mzip) $ mzip fa fb)
   (C  $ do  (a :< fa, b :< fb)  <- mzip (unC ma) (unC mb)
             d  :< fd            <- unC $ return $ snd (a, b)
             return $ d :< $ fd <|> fmap (>>= return . snd) $ fmap (uncurry mzip) $ mzip fa fb)

== {- Definition of `return` -}

   (,)
   (C  $ do  (a :< fa, b :< fb)  <- mzip (unC ma) (unC mb)
             d  :< fd            <- unC $ C $ return $ fst (a, b) :< empty
             return $ d :< $ fd <|> fmap (>>= return . fst) $ fmap (uncurry mzip) $ mzip fa fb)
   (C  $ do  (a :< fa, b :< fb)  <- mzip (unC ma) (unC mb)
             d  :< fd            <- unC $ C $ return $ snd (a, b) :< empty
             return $ d :< $ fd <|> fmap (>>= return . snd) $ fmap (uncurry mzip) $ mzip fa fb)

== {- Unpack -}

   (,)
   (C  $ do  (a :< fa, b :< fb)  <- mzip (unC ma) (unC mb)
             d  :< fd            <- return $ fst (a, b) :< empty
             return $ d :< $ fd <|> fmap (>>= return . fst) $ fmap (uncurry mzip) $ mzip fa fb)
   (C  $ do  (a :< fa, b :< fb)  <- mzip (unC ma) (unC mb)
             d  :< fd            <- return $ snd (a, b) :< empty
             return $ d :< $ fd <|> fmap (>>= return . snd) $ fmap (uncurry mzip) $ mzip fa fb)

== {- `Monad` law `return a >>= k == k a` -}

   (,)
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ fst (a, b) :< $ empty <|> fmap (>>= return . fst) $ fmap (uncurry mzip) $ mzip fa fb)
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ snd (a, b) :< $ empty <|> fmap (>>= return . snd) $ fmap (uncurry mzip) $ mzip fa fb)

== {- `Alternative` identity -}

   (,)
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ fst (a, b) :< fmap (>>= return . fst) $ fmap (uncurry mzip) $ mzip fa fb)
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ snd (a, b) :< fmap (>>= return . snd) $ fmap (uncurry mzip) $ mzip fa fb)

== {- Definition of `fst` -}

   (,)
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ a :< fmap (>>= return . fst) $ fmap (uncurry mzip) $ mzip fa fb)
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ b :< fmap (>>= return . snd) $ fmap (uncurry mzip) $ mzip fa fb)

== {- Definition of `liftM` -}

   (,)
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ a :< fmap (liftM fst) $ fmap (uncurry mzip) $ mzip fa fb)
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ b :< fmap (liftM snd) $ fmap (uncurry mzip) $ mzip fa fb)

== {- `Functor` composition -}

   (,)
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ a :< fmap (liftM fst . uncurry mzip) $ mzip fa fb)
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ b :< fmap (liftM snd . uncurry mzip) $ mzip fa fb)

== {- Definition of `unzip` -}

   (,)
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ a :< fmap (fst . unzip . uncurry mzip) $ mzip fa fb)
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ b :< fmap (snd . unzip . uncurry mzip) $ mzip fa fb)

== {- Coinduction hypothesis -}

   (,)
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ a :< fmap fst $ mzip fa fb)
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ b :< fmap snd $ mzip fa fb)

== {- `Monad` law `fmap f m == m >>= return . f` and definition of `liftM` -}

   (,)
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ a :< liftM fst $ mzip fa fb)
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ b :< liftM snd $ mzip fa fb)

== {- Definition of `unzip` -}

   (,)
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ a :< fst $ unzip $ mzip fa fb)
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ b :< snd $ unzip $ mzip fa fb)

== {- `MonadZip` information preservation -}

   (,)
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ a :< fst (fa, fb))
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ b :< snd (fa, fb))

== {- Definition of `fst` and `snd` -}

   (,)
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ a :< fa)
   (C  $ do  (a :< fa, b :< fb) <- mzip (unC ma) (unC mb)
             return $ b :< fb)

== {- Definition of `fst` and `snd` -}

   (,)
   (C  $ mzip (unC ma) (unC mb)  >>= return . fst)
   (C  $ mzip (unC ma) (unC mb)  >>= return . snd)

== {- Definition of `liftM` -}

   (,)
   (C  $ liftM fst  $ mzip (unC ma) (unC mb))
   (C  $ liftM snd  $ mzip (unC ma) (unC mb))

== {- Definition of `unzip` -}

   (,)
   (C  $ fst  $ unzip  $ mzip (unC ma) (unC mb))
   (C  $ snd  $ unzip  $ mzip (unC ma) (unC mb))

== {- `MonadZip` information preservation -}

   (,)
   (C  $ fst  $ (unC ma, unC mb))
   (C  $ snd  $ (unC ma, unC mb))

== {- Definition of `fst` and `snd` -}

   (,)
   (C  $ unC ma)
   (C  $ unC mb)

== {- Pack -}

   (ma, mb)

.
```
