Applicative instance for CofreeT
================================

If the underlying functor f is an instance of Alternative, then CofreeT is also
an applicative functor.

Note that the only required properties of Alternative are associativity and
existence of an identity element, so one could also use functors that are
instances of Plus (semigroupoid package).

```haskell
instance (Alternative f, Applicative w) =>
         Applicative (CofreeT f w) where
  pure = CofreeT . pure . (:< empty)
  
  (CofreeT wf) <*> aa@(CofreeT wa) = CofreeT $
    ( \(f :< t) -> 
      \(a)      ->  
      let (b :< n) = bimap f (fmap f) a in 
      b :< (n <|> fmap (<*> aa) t)) <$> wf <*> wa
```


## Identity

```haskell

  pure id <*> (C wa)

== {- definition of <*> -}

   C $
     ( \(f :< t) -> 
       \(a)      ->  
       let (b :< n) = bimap f (fmap f) a in 
       b :< (n <|> fmap (<*> C wa) t)) <$> (pure $ id :< empty) <*> wa

== {- w is Applicative -}
  
  C $
       \(a)      ->  
       let (b :< n) = bimap id (fmap id) a in 
       b :< (n <|> fmap (<*> C wa) empty)) <$> wa

== {- functor preserves identity -}

  C $
       \(a)      ->  
       let (b :< n) = bimap id id a in 
       b :< (n <|> fmap (<*> C wa) empty)) <$> wa

== {- bifunctors preserve identity -}

  C $
       \(a)      ->  
       let (b :< n) = a in 
       b :< (n <|> fmap (<*> C wa) empty)) <$> wa

== {- empty is invariant under fmap -}
 
  C $
       \(a)      ->  
       let (b :< n) = a in 
       b :< (n <|> empty) <$> wa

== {- empty is identity, β-reduction -}

  C $ id <$> wa

== {- functor preserves identity -}

  C wa

```


## Composition

First, we rewrite the definition of the (<*>) into something simpler:

```haskell

  (C wf) <*> (C wa)

== {- definition of <*> -}

  C $
      ( \(f :< t) -> 
        \(a)      ->  
        let (b :< n) = bimap f (fmap f) a in 
        b :< (n <|> fmap (<*> C wa) t)) <$> wf <*> wa

== {- pattern match on CofreeF -}

  C $
      ( \(f :< t) -> 
        \(a :< m)      ->  
        let (b :< n) = bimap f (fmap f) (a :< m) in 
        b :< (n <|> fmap (<*> C wa) t)) <$> wf <*> wa

== {- definition of bimap -}

  C $
      ( \(f :< t) -> 
        \(a :< m)      ->  
        let (b :< n) = f a :< fmap (fmap f) m in 
        b :< (n <|> fmap (<*> C wa) t)) <$> wf <*> wa

== {- β-equivalence -}

  C $
      ( \(f :< t) -> 
        \(a :< m) ->  
        (f a) :< (fmap (fmap f) m <|> fmap (<*> C wa) t)) <$> wf <*> wa

== {- define star(C wa) ≡ ( \(f :< t) -> … (<*> C wa) … ) -}

  C $ star(C wa) <$> wf <*> wa

== {- fmap for w Applicative -}

  C (pure star(C wa) <*> wf <*> wa)

```

Now, we can prove the law of composition:

```haskell

   pure (.) <*> C u <*> C v <*> C w

== {- definition of <*> -}

   C (pure star(C u) <*> pure ((.) :< empty) <*> u ) <*> C v <*> C w  

== {- definition of <*> -}

   C (pure star(C v) <*> 
       (pure star(C u) <*> pure ((.) :< empty) <*> u ) <*> 
       v
     ) <*> 
     C w

== {- definition of <*> -}

   C (pure star(C w) <*>
       (pure star(C v) <*>
         (pure star(C u) <*> pure ((.) :< empty) <*> u ) <*>
        v) <*>
      w)


== {- see lemma 1 -}

     C $ (\a :< m -> \b :< n -> c :< p ->
            (a (b c)) :< (fmap (fmap (a . b)) p <|>
                          fmap (\x -> pure (.) <*> pure a <*> x <*> C w) n) <|>
                          fmap (\x -> pure (.) <*> x    <*> C v <*> C w) m))) ==




== {- coinduction on recursive definition (“produce 1, consume 1”) -}

    
     C $ (\a :< m -> b :< n -> c :< p ->
          (a (b c) :< (fmap (fmap (a . b)) p) <|>
                      (fmap (\x -> pure a <*> (x <*> C w)) n) <|>
                      (fmap (\x -> x<*> (C v <*> C w))    m) )  


== {- see lemma 2 -}

  C (pure star(C v <*> C w) <*>
     u <*>
     (pure star(C w) <*>
        v <*>
        w))
   
== {- definition of <*> -}

  C (pure star(C v <*> C w) <*> u <*> unC (C v <*> C w))

== {- definition of <*> -}

   C u <*> (C v <*> C w)
```

### Lemma 1

To make reasoning easier, we'll use a shortand notation.

```
U               ≡ star(C v)
V               ≡ star(C u)
W               ≡ star(C w)
!               ≡ (.) :< empty
p               ≡ pure
<concatenation> ≡ function application 
.               ≡ (.)
```

By repeteadly applying the Applicative laws for the underlying functor, we
get:

```haskell
   
pW <*> (pV <*> (pU <*> p! <*> u) <*> v ) <*> w ==

pW <*> (pV <*> (p(U!) <*> u) <*> v ) <*> w ==

pW <*> (p. <*> pV <*> p(U!) <*> u <*> v ) <*> w ==

pW <*> ( p(.V)(U!) <*> u <*> v ) <*> w ==

p. <*> pW <*> ( p(.V)(U!) <*> u ) <*> v <*> w ==

p(.W) <*> (p(.V)(U!) <*> u) <*> v <*> w ==

p. <*> p(.W) <*> p(.V)(U!) <*> u <*> v <*> w ==

p.(.W)((.V)(U!)) <*> u <*> v <*> w 

```

Undoing the shorthand notation and simplifying:

```haskell

!  == (.) :< empty
U! == \(a :< m) -> (. a) :< fmap (fmap (.)) m
V  == \(f :< t) -> \(b :< n) -> (f b) :< (fmap (fmap f) n <|> 
                                          fmap (<*> C v) t)


. V (U!) == \(a :< m) -> V ((. a) :< fmap (fmap (.)) m) ==
         == \(a :< m) -> \(b :< n) ->
	          (a . b) :< (fmap (fmap (. a) n) <|>
                         fmap (<*> C v) ( fmap (fmap (.)) m)

W  == \(f :< t) -> \(c :< p) ->
          (f c) :< (fmap (fmap f) p <|> fmap (<*> C w) t)

.W == \g -> (\x -> W (g x))


   .(.W)(.V(U!))

== \s -> (.W)((.V(U!)) s) ==

== \a :< m -> (.W) ((.V(U!)) a :< m) ==

== \a :< m -> (.W) (\(b :< n) ->
                       (a . b) :< (fmap (fmap (. a) n) <|>
                                   fmap (<*> C v) ( fmap (fmap (.)) m))) ==

== \a :< m -> \b :< n ->
               W ( (a . b) :< (fmap (fmap (. a) n) <|>
                               fmap (<*> C v) ( fmap (fmap (.)) m))) ==

== \a :< m -> \b :< n -> c :< p ->
   (a (b c)) :< (fmap (fmap (a . b)) p <|>
                 fmap (<*> C w)
		        ((fmap (fmap (. a) n) <|>
                     fmap (<*> C v) (fmap (fmap (.)) m)))) ==

== \a :< m -> \b :< n -> c :< p ->
   (a (b c)) :< (fmap (fmap (a . b)) p <|>
                 fmap (<*> C w) (fmap (fmap (. a)) n) <|>
                 fmap (<*> C w) (fmap (<*> C v) ( fmap (fmap (.)) m))) ==

== \a :< m -> \b :< n -> c :< p ->
   (a (b c)) :< (fmap (fmap (a . b)) p <|>
                 fmap (\x -> pure (.) <*> pure a <*> x <*> C w) n) <|>
                 fmap (\x -> pure (.) <*> x    <*> C v <*> C w) m))) 
```

### Lemma 2

We use the following shorthands to make reasoning more readable.

```
W               ≡ star(C w)
Y               ≡ star(C v <*> C w)
p               ≡ pure
<concatenation> ≡ function application 
.               ≡ (.)
$W              ≡ ($ star(C w))
```

By repeteadly applying composition law for w, we get:

```haskell
  
pY <*> u <*> (pW <*> v <*> w) ==

p. <*> (pY <*> u) <*> (pW <*> v) <*> w ==

p. <*> p. <*> pY <*> u <*> (pW <*> v) <*> w ==

p. <*> (p. <*> p. <*> pY <*> u) <*> pW <*> v <*> w ==

p. <*> (p..Y <*> u) <*> pW <*> v <*> w ==

p. <*> p. <*> p..Y <*> u <*> pW <*> v <*> w ==

p..(..Y) <*> u <*> pW <*> v <*> w ==

p($W) <*> (p..(..Y) <*> u) <*> v <*> w ==

p.($W)(..(..Y)) <*> u <*> v <*> w


(.)  == \f -> \g -> \x -> f (g x)

($W) == \g -> g W

($W) . (..(..Y)) == \s -> (\g -> g W) ((..(..Y)) s)
                 == \s -> (..(..Y)) s W

(. . (..Y)) == (\s -> . ((..Y) s))

∴ ($W) . (..(..Y)) == \s -> ((..Y) s) . W

(..Y) == (\y -> (.) (Y y))

∴ ($W) . (..(..Y)) ==  \s -> ((.) (Y s)) . W

                   ==  \s -> \t -> ((.) (Y s)) (W t)
                   
                   ==  \s -> \t -> (Y s) . (W t)

                   ==  \s -> \t -> u -> (Y s (W t u))
```

Undoing shorthands and α-converting, we get:

```haskell
.($W)(..(..Y)) ==

\a :< m -> b :< n -> c :< p -> (Y (a :< m) (W (b :<n) (c :< p))) ==

\a :< m -> b :< n -> c :< p ->
   (Y (a :< m) (b c :< (fmap (fmap b) p) <|>
                       (fmap (<*> C w) n)))     ==

\a :< m -> b :< n -> c :< p ->
   (Y (a :< m) (b c :< (fmap (fmap b) p) <|>
                       (fmap (<*> C w) n)))     ==

\a :< m -> b :< n -> c :< p ->
   (a (b c) :< (fmap (fmap a) ((fmap (fmap b) p) <|>
	                              (fmap (<*> C w) n)))
               <|>
               (fmap (<*> (C v <*> C w)) m))
               
== {- fmap distributes over <|>, fmap respects composition -}
               
\a :< m -> b :< n -> c :< p ->
   (a (b c) :< (fmap (fmap (a . b)) p) <|>
               (fmap ((fmap a) . (<*> C w)) n) <|>
               (fmap (<*> (C v <*> C w)) m))  

== 

\a :< m -> b :< n -> c :< p ->
   (a (b c) :< (fmap (fmap (a . b)) p) <|>
               (fmap (\x -> pure a <*> (x <*> C w)) n) <|>
               (fmap (\x -> x<*> (C v <*> C w))    m) )  
```

## Homomorphism

```haskell

  pure f <*> pure x

== {- definition of <*> -}

  C $
    ( \(f :< t) -> 
      \(a)      ->  
      let (b :< n) = bimap f (fmap f) a in 
      b :< (n <|> fmap (<*> pure x) t)) <$>
        pure (f :< empty) <*> pure (x :< empty)

== {- homomorphism law for w, twice -}

  C $ pure $
      let (b :< n) = bimap f (fmap f) (x :< empty) in 
      b :< (n <|> fmap (<*> pure x) empty)) 

== {- bimap -}

  C $ pure $
      let (b :< n) = (f x :< (fmap f empty)) in 
      b :< (n <|> fmap (<*> pure x) empty)) 

== {- empty invariant under fmap -}
  
  C $ pure $ (f x) :< (empty <|> empty) 

== {- definition -}

  pure (f x)

```

## Interchange

```haskell

   u <*> pure y

== {- definition of <*>, pure -}

   C $     
     ( \(f :< t) ->
       \(a)      ->                                 
       let (b :< n) = bimap f (fmap f) a in
       b :< (n <|> fmap (<*> (pure y)) t)) <$> u <*> (pure (y :< empty))

== {- interchange law for w -}

   C $
      pure ($ y :< empty) <*>
      (pure
        ( \(f :< t) ->
          \(a)      ->                                 
          let (b :< n) = bimap f (fmap f) a in
          b :< (n <|> fmap (<*> (pure y)) t))) <*> u)

== {- composition -}

   C $
      pure (.) <*>
      pure ($ y :< empty) <*>
      pure
         ( \(f :< t) ->
           \(a)      ->                                 
           let (b :< n) = bimap f (fmap f) a in
           b :< (n <|> fmap (<*> (pure y)) t))

        <*> u)

== {- homomorphism -}

   C $
      pure (($ y :< empty) .) <*>
      pure
         ( \(f :< t) ->
           \(a)      ->                                 
           let (b :< n) = bimap f (fmap f) a in
           b :< (n <|> fmap (<*> (pure y)) t))

        <*> u)

== {- homomorphism -}

   C $
      pure (($ y :< empty) . 
         ( \(f :< t) ->
           \(a)      ->                                 
           let (b :< n) = bimap f (fmap f) a in
           b :< (n <|> fmap (<*> (pure y)) t))
        <*> u)

== {- β-reduction -}

   C $
      pure (
         ( \(f :< t) ->
           let (b :< n) = bimap f (fmap f) (y :< empty) in
           b :< (n <|> fmap (<*> (pure y)) t))
        <*> u)

== {- bimap, β-reduction -}

   C $
      pure (
         ( \(f :< t) -> f y :< (empty <|> fmap (<*> (pure y)) t))
        <*> u)

== {- fmap -}

   C $ (\(f :< t) -> f y :< (fmap (<*> pure y) t)) <$> u   

== {- coinduction (consume 1, produce 1) -}
   
   C $ (\(f :< t) -> f y :< (fmap ($ y) t)) <$> u
   
== {- def. $ -}

   C $ (\(f :< t) -> ($ y) f :< (fmap ($ y) t)) <$> u

== {- def. bimap -}

    C $ bimap ($ y) (fmap ($ y)) <$> u

== {- β,η-expansion -}

    C $     
     ( 
       \(a)      ->                                 
       let (b :< n) = bimap ($ y) (fmap ($ y)) a in
       b :< n) <$> u

== {- empty inviariant under fmap -}

    C $     
     ( 
       \(a)      ->                                 
       let (b :< n) = bimap ($ y) (fmap ($ y)) a in
       b :< (n <|> fmap (<*> u) empty)) <$> u

== {- fmap over pure -} 

   C $     
     ( \(f :< t) ->
       \(a)      ->                                 
       let (b :< n) = bimap f (fmap f) a in
       b :< (n <|> fmap (<*> u) t)) <$> (pure (($ y) :< empty)) <*> u

== {- definition -}

pure ($ y) <*> u
```

## Consistency with Monad definition

```haskell
instance (Alternative f, Monad w) => Monad (CofreeT f w) where
  return = CofreeT . return . (:< empty)
  (CofreeT cx) >>= f = CofreeT $ do
    (a :< m) <- cx
    (b :< n) <- runCofreeT $ f a
    return $ b :< (n <|> fmap (>>= f) m)
```

If w is also a monad, then ```(<*>) == ap```.
 
The proof uses coinduction for the case “produce one, consume one”.
 
_Remark:_ If ```g = (\f -> (CofreeT wa) >>= (\a -> return $ f a))```, then
        ```(`ap` a) == (>>= g)```.

```haskell

(C wf) `ap` (C wa)

== {- definition -}

(C wf) >>= (\f -> (C wa) >>= (\a -> f a))

== {- definition -}

                                  wf >>= \(f :< t) ->
 unC (C wa >>= (\a -> return $ f a)) >>= \(b :< n) ->
                              return $ b :< (n <|> fmap (>>= g) t)

== {- coinductive step -}

                                  wf >>= \(f :< t) ->
 unC (C wa >>= (\a -> return $ f a)) >>= \(b :< n) ->
                              return $ b :< (n <|> fmap (<*> C wa) t)
== {- definition of fmap for monads -}


                                  wf >>= \(f :< t) ->
                 unC (fmap f (C wa)) >>= \(b :< n) ->
                              return $ b :< (n <|> fmap (<*> C wa) t)

== {- definition of fmap for C -}

                                            wf >>= \(f :< t) ->
                    fmap (bimap f (fmap f)) wa >>= \(b :< n) ->
                              return $ b :< (n <|> fmap (<*> C wa) t)
      
== {- definition of fmap for monads -}

                                            wf >>= \(f :< t) ->
   (wa >>= (\a -> return (bimap f (fmap f) a)  >>= \(b :< n) ->
                              return $ b :< (n <|> fmap (<*> C wa) t)

== {- associativity of monads -}

                                  wf >>= \(f :< t) ->
                                  wa >>= \a        ->
       (return (bimap f (fmap f a))) >>= \(b :< n) -> 
                          return $ b :< (n <|> fmap (<*> a) m)

== {- Left identity of monads -}

                                  wf >>= \(f :< t) ->
                                  wa >>= \(a       ->
                          let b :< n = bimap f (fmap f a)) in
                          return $ b :< (n <|> fmap (<*> a) m))

== {- Equivalence of (>>=) and (<*>) for monad w. -}

                                         \(f :< t) ->
                                         \(a       ->
                          let b :< n = bimap f (fmap f a)) in
                          return $ b :< (n <|> fmap (<*> a) m)))

== {- definition of (<*>) -}

(CofreeT wf) <*> (CofreeT wa)

```
 

