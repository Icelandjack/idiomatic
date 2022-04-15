{-# Language AllowAmbiguousTypes      #-}
{-# Language DataKinds                #-}
{-# Language DeriveFunctor            #-}
{-# Language DerivingStrategies       #-}
{-# Language EmptyDataDecls           #-}
{-# Language FlexibleInstances        #-}
{-# Language InstanceSigs             #-}
{-# Language MultiParamTypeClasses    #-}
{-# Language PolyKinds                #-}
{-# Language ScopedTypeVariables      #-}
{-# Language StandaloneKindSignatures #-}
{-# Language TypeApplications         #-}
{-# Language TypeFamilies             #-}
{-# Language TypeOperators            #-}
{-# Language UndecidableInstances     #-}

module Generic.Applicative.Idiom where

import Control.Applicative
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.Kind
import Data.Proxy

import Generic.Applicative.Internal

-- | An 'Idiom' captures an "applicative homomorphism" between two
-- applicatives, indexed by a @tag@.
--
-- An appliative homomorphism is a polymorphic function between two
-- applicative functors that preserves the `Applicative` structure.
-- 
-- @
-- idiom (pure a) = pure a
--
-- idiom (liftA2 (·) as bs) = liftA2 (·) (idiom as) (idiom bs)
-- @
--
-- Based on:
-- <http://ekmett.github.io/reader/2012/abstracting-with-applicatives/index.html Abstracting with Applicatives>.
type  Idiom :: tagKind -> (Type -> Type) -> (Type -> Type) -> Constraint
class (Applicative f, Applicative g) => Idiom tag f g where
 idiom :: f ~> g

-- | The identity applicative morphism.
--
-- @
-- idiom :: f ~> f
-- idiom = id
-- @
data Id 
instance (Applicative f, f ~ g) => Idiom Id f g where
 idiom :: f ~> g
 idiom = id

-- | The left-to-right composition of applicative morphisms.
data Comp tag1 tag2
instance (Idiom tag1 f g, Idiom tag2 g h) => Idiom (Comp tag1 tag2) f h where
 idiom :: f ~> h
 idiom = idiom @_ @tag2 @g @h . idiom @_ @tag1 @f @g

-- | The initial applicative morphism.
--
-- It turns 'Identity' into any 'Applicative' functor.
-- 
-- @
-- idiom :: Identity ~> f
-- idiom (Identity a) = pure a
-- @
data Initial
instance (Identity ~ id, Applicative f) => Idiom Initial id f where
  idiom :: Identity ~> f
  idiom (Identity a) = pure a

-- | The terminal applicative morphism.
-- 
-- It turns any applicative into @'Const' m@, or 'Proxy'
--
-- @
-- idiom :: f ~> Const m
-- idiom _ = Const mempty
--
-- idiom :: f ~> Proxy
-- idiom _ = Proxy
-- @
data Terminal
instance (Applicative f, Monoid m) => Idiom Terminal f (Const m) where
  idiom :: f ~> Const m
  idiom = mempty
instance (Applicative f) => Idiom Terminal f Proxy where
  idiom :: f ~> Proxy
  idiom = mempty

-- Data.Functor.Compose

-- | This applicative morphism composes a functor on the _inside_.
--
-- @
-- idiom :: f ~> Compose f inner
-- idiom = Compose . fmap pure
-- @
data Inner
instance (Applicative f, Applicative inner, comp ~ Compose f inner) => Idiom Inner f comp where
  idiom :: f ~> Compose f inner
  idiom = Compose . fmap pure

-- | This applicative morphism composes a functor on the _outside_.
--
-- @
-- idiom :: f ~> Compose outer f
-- idiom = Compose . pure
-- @
data Outer
instance (Applicative outer, Applicative f, comp ~ Compose outer f) => Idiom Outer f comp where
  idiom :: f ~> Compose outer f
  idiom = Compose . pure

-- Data.Functor.Product
type family
  CheckIdiomDup f where
  CheckIdiomDup (Product _ _) = 'True
  CheckIdiomDup _             = 'False

-- | This applicative morphism duplicates a functor any number of times.
-- 
-- @
-- idiom :: f ~> f
-- idiom = id
-- 
-- idiom :: f ~> Product f f
-- idiom as = Pair as as
--
-- idiom :: f ~> Product f (Product f f)
-- idiom as = Pair as (Pair as as)
-- @
data Dup
instance (Applicative f, Applicative g, IdiomDup (CheckIdiomDup g) f g) => Idiom Dup f g where
  idiom :: f ~> g
  idiom = idiomDup

class (CheckIdiomDup g ~ tag, Applicative f, Applicative g) => IdiomDup tag f g where
  idiomDup :: f ~> g
  idiomDup = undefined

instance (Applicative f, CheckIdiomDup f ~ 'False, f ~ f') => IdiomDup 'False f f' where
  idiomDup :: f ~> f
  idiomDup = id

instance (f ~ g, IdiomDup (CheckIdiomDup g') g g') => IdiomDup 'True f (Product g g') where
  idiomDup :: f ~> Product g g'
  idiomDup as = Pair as (idiomDup as)

-- | An applicative functor for constructing a product.
-- 
-- @
-- idiom :: f ~> Product g h
-- idiom as = Pair (idiom as) (idiom as)
-- @
data tag1 &&& tag2
instance (Idiom tag1 f g, Idiom tag2 f h) => Idiom (tag1 &&& tag2) f (Product g h) where
  idiom :: f ~> Product g h
  idiom as = Pair (idiom @_ @tag1 as) (idiom @_ @tag2 as)

-- | The applicative functor that gets the first component of a
-- product.
-- 
-- @
-- idiom :: Product f g ~> f
-- idiom (Pair as _) = as
-- @
data Fst
instance (Applicative f, Applicative g) => Idiom Fst (Product f g) f where
  idiom :: Product f g ~> f
  idiom (Pair as _) = as

-- | The applicative functor that gets the second component of a
-- product.
-- 
-- @
-- idiom :: Product f g ~> g
-- idiom (Pair _ bs) = bs
-- @
data Snd
instance (Applicative f, Applicative g) => Idiom Snd (Product f g) g where
  idiom :: Product f g ~> g
  idiom (Pair _ bs) = bs
