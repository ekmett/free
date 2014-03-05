Monad instance for CofreeT
==========================

If the underlying functor f is an instance of Alternative, then CofreeT is also
a Monad.

Note that the only required properties of Alternative are associativity and
identity element, so one could also use functors that are instances of Plus
(semigroupoid package).

```haskell
instance (Alternative f, Monad w) => Monad (CofreeT f w) where
  return = CofreeT . return . (:< empty)
  (CofreeT cx) >>= f = CofreeT $ do
    (a :< m) <- cx
    (b :< n) <- runCofreeT $ f a
    return $ b :< (n <|> fmap (>>= f) m)
```

This definition is equivalent to that of the Cofree module if 'w' is
identity. 

The tokens `CofreeT` and `runCofreeT` are abreviated as `C` and `unC`, 
respectively, for readability.

## Left identity

```haskell
return x >>= f

== {- definition of return -}

C (return (x :< empty)) >>= f

== {- definition of bind -}

C $ (return (x :< empty)) >>= (\a :< m ->
                unC (f a) >>= (\b :< n ->
                return $ b :< (n <|> fmap (>>= f) m)

== {- Left identity for 'w' -}

            C $ unC (f x) >>= (\b :< n ->
                return $ b :< (n <|> fmap (>>= f) empty)

== {- fmap over empty -}

            C $ unC (f x) >>= (\b :< n ->
                return $ b :< (n <|> fmap (>>= f) empty)

== {- empty is identity for <|> -} == 

            C $ unC (f x) >>= (\b :< n ->
                return $ b :< n
  
== {- η-reduction, right identity for w -}

            C $ unC (f x)
==

f x
```

## Right identity 

```haskell

  (C wx) >>= return

== {- definition of return -}

  (C wx) >>= (\x -> C $ return $ (x :< empty))

== {- definition of bind -}

  C $ wx >>= (\a :< m -> unC (C $ return $ a :< empty)
         >>= (\b :< n -> return $ b :< (n <|> fmap (>>= return) m)

== {- coinduction (“produce 1, consume 1”) -}

  C $ wx >>= (\a :< m -> unC (C $ return $ a :< empty)
         >>= (\b :< n -> return $ b :< (n <|> fmap id m)

== {- fmap id == id -}

  C $                            wx >>= (\a :< m ->
      unC (C $ return $ a :< empty) >>= (\b :< n ->
                           return $ b :< (n <|> m)

== {- unC . C == id, left identity for w -}

  C $ wx >>= (\a :< m ->
      let b :< n = a :< empty in
      return $ b :< (n <|> m)

== {- β-equivalence -}

  C $ wx >>= (\a :< m -> return $ a :< (empty <|> m))

== {- empty is identity for <|> -}

  C $ wx >>= (\a :< m -> return $ a :< m))

== {- right identity for w -}

  C wx
```

## Associativity

```haskell
  (C wa  >>= g) >>= h
  
== {- definition -}
  
  C $ do
        unC (C wa >>= g) >>= \(c :< o) ->
         unC $ h c       >>= \(d :< p) _>
         return $ d :< (p <|> fmap (>>= h) o)
  
== {- definition -}
  
  C $ do
       (wa             >>=   \(a :< m) ->
        unC (g a)        >>= \(b :< n) ->
        return $ b :< (m <|> fmap (>>= g) n)
                       ) >>= \(c :< o) ->
         unC $ h c       >>= \(d :< p) _>
         return $ d :< (p <|> fmap (>>= h) o)
  
== {- associativity of 'w' -}
  
  C $ do
                                     wa  >>= \(a :< m) ->
                               unC (g a) >>= \(b :< n) ->
   return $ b :< (m <|> fmap (>>= g) m)  >>= \(c :< o) ->
                         unC $ h c       >>= \(d :< p) _>
         return $ d :< (p <|> fmap (>>= h) o)
  
== {- left identity -}
  C $ do
                                     wa  >>= \(a :< m) ->
                               unC (g a) >>= \(b :< n) ->
                               unC (h b) >>= \(d :< p) _>
         return $ d :< (p <|> fmap (>>= h) (n <|> fmap (>>= g) m))
  
== {- fmap distributes over (<|>), <|> is associative -}
  
  C $ do
              wa     >>= \(a :< m) ->
       unC (g a)     >>= \(b :< n) ->
       unC (h b)     >>= \(d :< p) 
    return $ d :< (p <|> (fmap (>>= h) n) <|> fmap (>>= h) (fmap (>>= g)  m))
  
== {- ∀f ∀g . fmap (f . g) == fmap f . fmap g -}
  C $ do
              wa     >>= \(a :< m) ->
       unC (g a)     >>= \(b :< n) ->
       unC (h b)     >>= \(d :< p) 
    return $ d :< (p <|> (fmap (>>= h) n) <|> fmap ((>>= h) . (>>= g))  m)
  
== {- coinduction -}
   
  C $ do
              wa     >>= \(a :< m) ->
       unC (g a)     >>= \(b :< n) ->
       unC (h b)     >>= \(d :< p) 
    return $ d :< (p <|> (fmap (>>= h) n) <|> fmap (>>= (\x -> g x >>= h)) m)
  
== {- associativity of <|> -}
  
  c $ do
              wa     >>= \(a :< m) ->
       unC (g a)     >>= \(b :< n) ->
       unC (h b)     >>= \(d :< p) 
    return $ d :< ((p <|> fmap (>>=h) n) <|> fmap (>>= (\x -> g x >>= h)) m
  
== {- associativity, right identity for monads -}
  c $ do
              (wa    >>= \(a :< m) ->
       unC (g a)     >>= \(b :< n) ->
       unC (h b)     >>= \(d :< p) 
       return (d :< (p <|> (fmap >>= h) n))) >>= \(c :< o) ->
    return $ c :< (o <|> fmap (>>= (\x -> g x >>= h)) m
	
== {- definition of bind -}

  C $ do
         wa          >>= \(a :< m) ->
    unC (g a >>= h)  >>= \(c :< o) ->
    return $ c :< (o <|> fmap (>>= (\x -> g x >>= h)) m)
	
== {- definition of bind -}

  (C wa) >>= (\x -> g x >>= h)
```

## Consistency with Applicative definition

See [proof for applicative instance](instance-Applicative-CofreeT.md#consistency-with-monad-definition).
