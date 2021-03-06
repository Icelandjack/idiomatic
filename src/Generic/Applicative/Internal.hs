{-# Options_GHC -Wno-name-shadowing #-}

{-# Language AllowAmbiguousTypes        #-}
{-# Language CPP                        #-}
{-# Language ConstraintKinds            #-}
{-# Language DataKinds                  #-}
{-# Language DefaultSignatures          #-}
{-# Language DerivingStrategies         #-}
{-# Language EmptyCase                  #-}
{-# Language FlexibleContexts           #-}
{-# Language FlexibleInstances          #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language InstanceSigs               #-}
{-# Language LambdaCase                 #-}
{-# Language MultiParamTypeClasses      #-}
{-# Language PolyKinds                  #-}
{-# Language RankNTypes                 #-}
{-# Language ScopedTypeVariables        #-}
{-# Language StandaloneKindSignatures   #-}
{-# Language TypeApplications           #-}
{-# Language TypeFamilies               #-}
{-# Language TypeOperators              #-}
{-# Language UndecidableInstances       #-}

module Generic.Applicative.Internal where

import Control.Applicative
import Data.Coerce
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Sum
import Data.Kind
import Data.Proxy
import Data.Void
import GHC.Generics
import Unsafe.Coerce

#if MIN_VERSION_base(4,17,0)
#define HAS_GENERICALLY
#endif

-- | The kind of a lifted binary type constructor.
--
-- @
-- Sum     :: SumKind k
-- Product :: SumKind k
--
-- (:+:)   :: SumKind k
-- (:*:)   :: SumKind k
-- @
--
-- Definition:
--
-- @
-- type SumKind :: Type -> Type
-- type SumKind k = (k -> Type) -> (k -> Type) -> (k -> Type)
-- @
type SumKind :: Type -> Type
type SumKind k = (k -> Type) -> (k -> Type) -> (k -> Type)

-- | A polymorphic function / natural transformation.
--
-- Used for /Applicative homomorphisms/ ('Idiom'):
--
-- @
-- idiom @_ @tag :: Idiom tag l r => l ~> r
-- @
--
-- Definition:
--
-- @
-- type (~>) :: (k -> Type) -> (k -> Type) -> Type
-- type f ~> g = forall x. f x -> g x
-- @
type (~>) :: (k -> Type) -> (k -> Type) -> Type
type f ~> g = forall x. f x -> g x

-- | 'Data.Void.absurd' for @Const Void@.
--
-- @
-- absurdZero :: Const Void a -> b
-- absurdZero (Const void) = absurd void
-- @
absurdZero :: Const Void a -> b
absurdZero (Const void) = absurd void

-- | 'Data.Void.absurd' for 'V1'.
--
-- @
-- absurdV1 :: V1 a -> b
-- absurdV1 = \case
-- @
absurdV1 :: V1 a -> b
absurdV1 = \case

-- This is following a couple of requirements:
--
--  1. I want to use the more user-facing Data.Functor vocabulary
--     rather than GHC.Generics.
--
--  2. I want to get rid of nested functors
--
--       (Par1 :*: Par1) :*: (Par1 :*: Par1)
--
--     intead I want
--
--       Product (Product Identity Identity) (Product Identity Identity)
--
--  3. I don't want to terminate the sums or products with @Const
--     Void@ or @Const ()@.
--
--  4. The sums should be replaced by a type-level list of sums, such
--     that the user can override its Applicative behaviour.
--
-- 'ConvSum' (1. and 2.) translates to Sum, Product and Compose and
-- flattens the representation, but this results in terminating
-- functors @Const Void@ and @Const ()@.
--
-- 'ConvB??Sum' (3.) removes terminating @Const Void@ and @Const ()@.
--
-- @ReplaceSums [sum1, sum2, ..] rep1@ replaces the sums of a
-- representation @rep1@.

-- | The first thing I do is to convert
type  ConvSum :: (k -> Type) -> Constraint
class ConvSum (rep1 :: k -> Type) where
  type ToSum (rep1 :: k -> Type) (end :: k -> Type) :: k -> Type

  convToSum     :: Proxy end -> rep1 ~> ToSum rep1 end
  convToSumSkip :: end ~> ToSum rep1 end
  convFromSum :: ToSum rep1 end a -> (rep1 a -> res) -> (end a -> res) -> res

instance (ConvSum rep1, ConvSum rep1') => ConvSum (rep1 :+: rep1') where
  type ToSum (rep1 :+: rep1') end = ToSum rep1 (ToSum rep1' end)

  convToSum :: forall end. Proxy end -> (rep1 :+: rep1') ~> ToSum rep1 (ToSum rep1' end)
  convToSum end (L1 l1) = convToSum @_ @_ @(ToSum rep1' end) (asToSum end) l1 where

    asToSum :: Proxy end -> Proxy (ToSum rep1' end)
    asToSum = mempty

  convToSum end (R1 r1) = convToSumSkip @_ @rep1 @(ToSum rep1' end)
    (convToSum end r1)

  convToSumSkip :: end ~> ToSum rep1 (ToSum rep1' end)
  convToSumSkip end = convToSumSkip @_ @rep1
    (convToSumSkip @_ @rep1' end)

  convFromSum :: forall end res a. ToSum rep1 (ToSum rep1' end) a -> ((rep1 :+: rep1') a -> res) -> (end a -> res) -> res
  convFromSum sum fromSum fromEnd =
    convFromSum sum (fromSum . L1) $ \sum' ->
      convFromSum sum' (fromSum . R1) fromEnd

instance ConvSum V1 where
  type ToSum V1 end = end

  convToSum :: Proxy end -> V1 ~> end
  convToSum _ = absurdV1

  convToSumSkip :: end ~> end
  convToSumSkip = id

  convFromSum :: end a -> (rep1 a -> res) -> (end a -> res) -> res
  convFromSum end _ fromEnd = fromEnd end

instance ConvSum rep1 => ConvSum (D1 meta rep1) where
  type ToSum (D1 meta rep1) end = ToSum rep1 end

  convToSum :: Proxy end -> D1 meta rep1 ~> ToSum rep1 end
  convToSum end (M1 d1) = convToSum end d1

  convToSumSkip :: end ~> ToSum rep1 end
  convToSumSkip = convToSumSkip @_ @rep1

  convFromSum :: ToSum rep1 end a -> (D1 meta rep1 a -> res) -> (end a -> res) -> res
  convFromSum sum fromD1 = convFromSum sum (fromD1 . M1)

instance ConvProduct rep1 => ConvSum (C1 meta rep1) where
  type ToSum (C1 meta rep1) end = Sum (ToProduct rep1 (Const ())) end

  convToSum :: forall end. Proxy end -> C1 meta rep1 ~> Sum (ToProduct rep1 (Const ())) end
  convToSum Proxy (M1 c1) = InL
    (convToProduct @_ @rep1 c1 (Const ()))

  convToSumSkip :: end ~> Sum (ToProduct rep1 (Const ())) end
  convToSumSkip = InR

  convFromSum :: Sum (ToProduct rep1 (Const ())) end a -> (C1 meta rep1 a -> res) -> (end a -> res) -> res
  convFromSum (InL prod) fromC1 _       = convFromProduct @_ @rep1 @(Const ()) prod $ \r _ -> fromC1 (M1 r)
  convFromSum (InR end)  _      fromEnd = fromEnd end

-- ??

type ConvProduct :: (k -> Type) -> Constraint

class ConvProduct (rep1 :: k -> Type) where
  type ToProduct (rep1 :: k -> Type) (end :: k -> Type) :: k -> Type

  convToProduct :: rep1 a -> end a -> ToProduct rep1 end a

  convFromProduct :: ToProduct rep1 end a -> (rep1 a -> end a -> res) -> res

instance (ConvProduct rep1, ConvProduct rep1') => ConvProduct (rep1 :*: rep1') where
  type ToProduct (rep1 :*: rep1') end = ToProduct rep1 (ToProduct rep1' end)

  convToProduct :: (rep1 :*: rep1') a -> end a -> ToProduct rep1 (ToProduct rep1' end) a
  convToProduct (r :*: r') end = convToProduct r (convToProduct r' end)

  convFromProduct :: ToProduct rep1 (ToProduct rep1' end) a
                  -> ((rep1 :*: rep1') a -> end a -> res) -> res
  convFromProduct prod next =
    convFromProduct prod $ \r end ->
      convFromProduct end $ \r' end' ->
        next (r :*: r') end'

instance ConvProduct U1 where
  type ToProduct U1 end = end

  convToProduct :: U1 a -> end a -> end a
  convToProduct U1 = id

  convFromProduct :: end a -> (U1 a -> end a -> res) -> res
  convFromProduct end fromU1 = fromU1 U1 end

instance ConvField rep1 => ConvProduct (S1 meta rep1) where
  type ToProduct (S1 meta rep1) end = Product (ToField rep1) end

  convToProduct :: S1 meta rep1 a -> end a -> Product (ToField rep1) end a
  convToProduct (M1 s1) end = Pair (convToField s1) end

  convFromProduct :: Product (ToField rep1) end a -> (S1 meta rep1 a -> end a -> res) -> res
  convFromProduct (Pair field end) next =
    next (M1 (convFromField field)) end

type  ConvField :: (k -> Type) -> Constraint
class ConvField (rep1 :: k -> Type) where
  type ToField (rep1 :: k -> Type) :: (k -> Type)
  convToField :: rep1 ~> ToField rep1
  default
    convToField :: Coercible (rep1 a) (ToField rep1 a) => rep1 a -> ToField rep1 a
  convToField = coerce

  convFromField :: ToField rep1 ~> rep1
  default
    convFromField :: Coercible (ToField rep1 a) (rep1 a) => ToField rep1 a -> rep1 a
  convFromField = coerce

instance ConvField (K1 tag a) where
  type ToField (K1 tag a) = Const a

instance ConvField (Rec1 f) where
  type ToField (Rec1 f) = f

instance ConvField Par1 where
  type ToField Par1 = Identity

instance (Functor rep1, ConvField rep1') => ConvField (rep1 :.: rep1') where
  type ToField (rep1 :.: rep1') = Compose rep1 (ToField rep1')

  convToField :: (rep1 :.: rep1') ~> Compose rep1 (ToField rep1')
  convToField (Comp1 rs) = Compose (convToField <$> rs)

  convFromField :: Compose rep1 (ToField rep1') ~> (rep1 :.: rep1')
  convFromField (Compose rs) = Comp1 (convFromField <$> rs)

-- B?? +
type SumTag :: Type
data SumTag = RightZero | NormalSum | NotSum

type
  CheckSum :: (k -> Type) -> SumTag
type family
  CheckSum rep1 where
  CheckSum (Sum rep1 (Const Void)) = 'RightZero
  CheckSum (Sum rep1 rep')         = 'NormalSum
  CheckSum rep                     = 'NotSum

type B??Sum :: (k -> Type) -> (k -> Type)
type B??Sum rep1 = B??Sum_ (CheckSum rep1) rep1

type ConvB??Sum :: (k -> Type) -> Constraint
type ConvB??Sum rep1 = ConvB??Sum_ (CheckSum rep1) rep1

type
  ConvB??Sum_ :: SumTag -> (k -> Type) -> Constraint
class CheckSum rep1 ~ tag
   => ConvB??Sum_ tag (rep1 :: k -> Type) where
  type B??Sum_ tag (rep1 :: k -> Type) :: k -> Type
  convB??Sum :: rep1 ~> B??Sum rep1
  convH??Sum :: B??Sum rep1 ~> rep1

instance (ConvB??Product rep1, CheckSum (Sum rep1 (Const Void)) ~ 'RightZero, void ~ Void) => ConvB??Sum_ 'RightZero (Sum rep1 (Const void)) where
  type B??Sum_ 'RightZero (Sum rep1 (Const void)) = B??Product rep1
  convB??Sum :: Sum rep1 (Const Void) ~> B??Product rep1
  convB??Sum = \case
    InL r  -> convB??Product r
    InR v1 -> absurdZero v1

  convH??Sum :: B??Product rep1 ~> Sum rep1 (Const Void)
  convH??Sum b??Prod = InL (convH??Product b??Prod)

instance ( CheckSum (Sum rep1 rep1') ~ 'NormalSum
         , ConvB??Product rep1
         , ConvB??Sum rep1' )
      => ConvB??Sum_ 'NormalSum (Sum rep1 rep1') where
  type B??Sum_ 'NormalSum (Sum rep1 rep1') = Sum (B??Product rep1) (B??Sum rep1')
  convB??Sum :: Sum rep1 rep1' ~> Sum (B??Product rep1) (B??Sum rep1')
  convB??Sum = \case
   InL r  -> InL (convB??Product r)
   InR r' -> InR (convB??Sum r')

  convH??Sum :: Sum (B??Product rep1) (B??Sum rep1') ~> Sum rep1 rep1'
  convH??Sum (InL b??Prod) = InL (convH??Product b??Prod)
  convH??Sum (InR b??Sum)  = InR (convH??Sum b??Sum)

instance CheckSum rep1 ~ 'NotSum
      => ConvB??Sum_ 'NotSum rep1 where
  type B??Sum_ 'NotSum rep1 = rep1
  convB??Sum :: rep1 ~> rep1
  convH??Sum :: rep1 ~> rep1
  convB??Sum = id
  convH??Sum = id

-- B?? ??

type ProductTag :: Type
data ProductTag = RightOne | NormalProduct | NotProduct

type
  CheckProduct :: (k -> Type) -> ProductTag
type family
  CheckProduct rep1 where
  CheckProduct (Product rep1 (Const ())) = 'RightOne
  CheckProduct (Product rep1 rep')       = 'NormalProduct
  CheckProduct rep                       = 'NotProduct

type B??Product :: (k -> Type) -> (k -> Type)
type B??Product rep1 = B??Product_ (CheckProduct rep1) rep1

type ConvB??Product :: (k -> Type) -> Constraint
type ConvB??Product rep1 = ConvB??Product_ (CheckProduct rep1) rep1

type ConvB??Product_ :: ProductTag -> (k -> Type) -> Constraint

class tag ~ CheckProduct rep1
   => ConvB??Product_ tag (rep1 :: k -> Type) where
  type B??Product_ tag (rep1 :: k -> Type) :: k -> Type
  convB??Product :: rep1 ~> B??Product rep1
  convH??Product :: B??Product rep1 ~> rep1

instance unit ~ () => ConvB??Product_ 'RightOne (Product rep1 (Const unit)) where
  type B??Product_ 'RightOne (Product rep1 (Const unit)) = rep1

  convB??Product :: Product rep1 (Const ()) ~> rep1
  convB??Product (Pair r (Const ())) = r

  convH??Product :: rep1 ~> Product rep1 (Const ())
  convH??Product r = Pair r (Const ())

instance ( CheckProduct (Product rep1 rep1') ~ 'NormalProduct
         , ConvB??Product rep1'
         )
      => ConvB??Product_ 'NormalProduct (Product rep1 rep1') where
  type B??Product_ 'NormalProduct (Product rep1 rep1') = Product rep1 (B??Product rep1')
  convB??Product :: Product rep1 rep1' ~> Product rep1 (B??Product rep1')
  convB??Product (Pair r r') = Pair r (convB??Product r')

  convH??Product :: Product rep1 (B??Product rep1') ~> Product rep1 rep1'
  convH??Product (Pair r b??Prod) = Pair r (convH??Product b??Prod)

instance CheckProduct rep1 ~ 'NotProduct
      => ConvB??Product_ 'NotProduct rep1 where
  type B??Product_ 'NotProduct rep1 = rep1

  convH??Product :: rep1 ~> rep1
  convB??Product :: rep1 ~> rep1
  convH??Product = id
  convB??Product = id

type Flatten :: (k -> Type) -> (k -> Type)
type Flatten rep1 = ToSum rep1 (Const Void)

-- | Flattens a generic representation.
--
-- Afaik GHC is free to nest the generic representation however it
-- fancies. The representation of @data A a = A a a a a@ is for
-- example
--
-- @
-- Rep1 A = (Par1 :+: Par1) :+: (Par1 :+: Par1)   -- without metadata
---
-- This nesting making it trickier to cleanly replace the sums and
-- specify 'Idiom's to match the products.
--
-- In addition it converts representations that use the @GHC.Generics@
-- polynomial vocabulary into @Data.Functor@. So this should m
--
-- It also strips metadata.
--
-- @
-- flatten :: Rep1 A
--         ~> Flatten (Rep1 A)
--
-- flatten :: ((Par1 :+: Par1) :+: (Par1 :+: Par1))
--         ~> Sum (Product Identity (Product Identity (Product Identity (Product Identity (Const ()))))) (Const Void)
-- @
--
-- but it makes all the sums 0-terminated (0 = @Const Void@ = @V1@)
-- and all the products 1-terminated (1 = @Const ()@ = @U1@).
flatten :: ConvSum rep1 => rep1 ~> Flatten rep1
flatten = convToSum (Proxy @(Const Void))

nest :: ConvSum rep1 => Flatten rep1 a -> rep1 a
nest flat = convFromSum flat id absurdZero

-- NewSums
type
  ReplaceSums :: [SumKind k] -> (k -> Type) -> (k -> Type)
type family
  ReplaceSums sums rep1 where
  ReplaceSums (sum:sums) (Sum rep1 rep1') = rep1 `sum` ReplaceSums sums rep1'
  ReplaceSums '[]        rep1             = rep1

-- | This is actually not safe and causes a segfault.
replaceSums :: forall sums rep1. rep1 ~> ReplaceSums sums rep1
replaceSums = unsafeCoerce

placeSums :: forall sums rep1. ReplaceSums sums rep1 ~> rep1
placeSums = unsafeCoerce

type    NewSums :: [SumKind k] -> (k -> Type) -> (k -> Type)
newtype NewSums sums f a = NewSums { reduce :: f a }

instance (Generic1 f, ConvB??Sum_ (CheckSum (ToSum (Rep1 f) (Const Void))) (ToSum (Rep1 f) (Const Void)), ConvSum (Rep1 f)) => Generic1 @k (NewSums @k sums f) where
  type Rep1 (NewSums sums f) = ReplaceSums sums (B??Sum_ (CheckSum (ToSum (Rep1 f) (Const Void))) (ToSum (Rep1 f) (Const Void)))

  from1 :: NewSums sums f ~> ReplaceSums sums (B??Sum_ (CheckSum (ToSum (Rep1 f) (Const Void))) (ToSum (Rep1 f) (Const Void)))
  from1 = replaceSums @sums . convB??Sum . flatten . from1 . reduce

  to1 :: ReplaceSums sums (B??Sum_ (CheckSum (ToSum (Rep1 f) (Const Void))) (ToSum (Rep1 f) (Const Void))) ~> NewSums sums f
  to1 = NewSums . to1 . nest . convH??Sum . placeSums @sums

#ifndef HAS_GENERICALLY
-- | This exists in versions that don't have 'Generically1',
-- i.e. before base 4.17.0.0.
type    Generically1 :: forall k. (k -> Type) -> (k -> Type)
newtype Generically1 f a = Generically1 (f a)
  deriving newtype Generic1

instance (Generic1 f, Functor (Rep1 f)) => Functor (Generically1 f) where
  fmap :: (a -> a') -> (Generically1 f a -> Generically1 f a')
  fmap f (Generically1 as) = Generically1
    (to1 (fmap f (from1 as)))

  (<$) :: a -> Generically1 f b -> Generically1 f a
  a <$ Generically1 as = Generically1
    (to1 (a <$ from1 as))

instance (Generic1 f, Applicative (Rep1 f)) => Applicative (Generically1 f) where
  pure :: a -> Generically1 f a
  pure a = Generically1
    (to1 (pure a))

  (<*>) :: Generically1 f (a1 -> a2) -> Generically1 f a1 -> Generically1 f a2
  Generically1 fs <*> Generically1 as = Generically1
    (to1 (from1 fs <*> from1 as))

  liftA2 :: (a1 -> a2 -> a3)
         -> (Generically1 f a1 -> Generically1 f a2 -> Generically1 f a3)
  liftA2 (??) (Generically1 as) (Generically1 bs) = Generically1
    (to1 (liftA2 (??) (from1 as) (from1 bs)))
#endif
