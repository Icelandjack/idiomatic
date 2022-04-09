Deriving Applicative sums... Idiomatically!
==================================

`Idiomatically` is used with `DerivingVia` to derive `Applicative` for
sum types. It takes as an argument a list of sum constructors that it
uses to tweak the generic representation of a type.

```haskell
{-# Language DataKinds          #-}
{-# Language DeriveGeneric      #-}
{-# Language DerivingStrategies #-}
{-# Language DerivingVia        #-}

import Generic.Applicative

data Maybe a = Nothing | Just a
  deriving
  stock Generic1

  deriving (Functor, Applicative)
  via Idiomatically Maybe '[RightBias Terminal]
```

This comes with two tagged newtypes over
[`Sum`](https://hackage.haskell.org/package/base/docs/Data-Functor-Sum.html)
that are biased toward the left and right constructor.

```haskell
newtype LeftBias  tag l r a = LeftBias  (Sum l r a)
newtype RightBias tag l r a = RightBias (Sum l r a)
```

```haskell
  pure = LeftBias  . InL . pure @l
  pure = RightBias . InR . pure @r
```

and an extensible language for type-level _applicative morphisms_
(`Idiom`) used to map away from the `pure` constructor.

```haskell
-- Applicative morphisms preserve the `Applicative` operations
--
--   idiom (pure @f a)           = pure @g a
--   idiom (liftA2 @f (·) as bs) = liftA2 @g (·) (idiom as) (idiom bs)
--
type  Idiom :: t -> (Type -> Type) -> (Type -> Type) -> Constraint
class (Applicative f, Applicative g) => Idiom tag f g where
  idiom :: f ~> g
```

This means for `LeftBias tag l r` we map from the left-to-right and
that for `RightBias tag l r` we map from right-to-left.

```haskell
instance Idiom tag l r => Applicative (LeftBias  tag l r)
instance Idiom tag r l => Applicative (RightBias tag l r)
```

For example, the identity applicative morphism

```haskell
data Id
instance f ~ g => Idiom Id f g where
  idiom :: f ~> f
  idiom = id
```

can be used to derive two different instances for the same datatype by
either defecting from the the left constructor (`LPure`) or from the
right constructor (`RPure`).

```haskell
-- >> pure @L True
-- LPure True
-- >> liftA2 (+) (LPure 1) (L 100)
-- L 101
data L a = LPure a | L a
  deriving stock (Show, Generic1)

  deriving (Functor, Applicative)
  via Idiomatically L '[LeftBias Id]

-- >> pure @R False
-- RPure False
-- >> liftA2 (+) (RPure 1) (R 100)
-- R 101
data R a = R a | RPure a
  deriving stock (Show, Generic1)

  deriving (Functor, Applicative) 
  via Idiomatically R '[RightBias Id]
```

More compliated descriptions are possible where we mediate between
multiple constructors:

```haskell
-- >> pure @Ok 10
-- Ok1 10
-- >> liftA2 (+) (Ok1 10) (Ok5 20)
-- Ok3 [Just 30]
-- >> liftA2 (+) (Ok2 [1..4]) (Ok5 20)
-- Ok3 [Just 21,Just 22,Just 23,Just 24]
-- >> liftA2 (+) (Ok2 [1..4]) (Ok4 Nothing)
-- Ok3 [Nothing,Nothing,Nothing,Nothing]
data Ok a = Ok1 a | Ok2 [a] | Ok3 [Maybe a] | Ok4 (Maybe a) | Ok5 a
  deriving
  stock (Show, Generic1)

  deriving (Functor, Applicative) 
  via Idiomatically Ok
    '[ LeftBias Initial       -- Ok1 to Ok2: pure
     , LeftBias Inner         -- Ok2 to Ok3: fmap pure
     , RightBias Outer        -- Ok4 to Ok3: pure
     , RightBias Initial      -- Ok5 to Ok4: pure
     ]
```

Relationship to `Generically1`
-----------

`Generically1` was recently introduced to `GHC.Generics` (_base
4.17.0.0_) with the ability to derive `Applicative` for generic type
constructors, among other things. Before it was added to _base_ it was
found in the
[_generic-data_](https://hackage.haskell.org/package/generic-data-0.9.2.1/docs/Generic-Data-Internal-Generically.html#t:Generically1)
package.

For `Applicative` in particular it uses the underlying generic
representation of a type; if that representation has an `Applicative`
instance then `Applicative` can be derived.

```haskell
import GHC.Generics (Generically1(..))

data F a = F a String a a [[[a]]] (Int -> Maybe a)
  deriving stock Generic1

  deriving (Functor, Applicative) via Generically1 F
```

This works well for product types but it does not work for sum types
since there is no `Appliative (Sum f g)` or `Applicative (f :+: g)`
instance.

In this sense, `Generically1` can be recovered by passing an empty
list of sums to `Idiomatically`:

```haskell
  Generically1  F
= Idiomatically F '[]
```

`Idiomatically` is also defined in terms of `Generically1`:

```haskell
type Idiomatically :: (k -> Type) -> [SumKind k] -> (k -> Type)
type Idiomatically f sums = Generically1 (NewSums (Served sums) f)
```

The argument to `Generically1` is less important, what is basically
happening is that `NewSums` modifies the generic behaviour of `f`: it
traverses the generic representation `Rep1 f` and replace every sum
with an `Applicative` sum from type-level list.

This means we can define `Idiomatically` in terms of
`Generically1`. There is an `Applicative` instance for `Generically1`
if its representation is `Applicative`, by tweaking the representation
of its argument we have thus managed to configure `Generically1` even
though it has no configuration parameter!

