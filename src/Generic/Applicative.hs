{-# LANGUAGE DerivingVia #-}

{-# Language DataKinds                  #-}
{-# Language DeriveGeneric              #-}
{-# Language DerivingStrategies         #-}
{-# Language FlexibleInstances          #-}
{-# Language GeneralizedNewtypeDeriving #-}
{-# Language InstanceSigs               #-}
{-# Language MultiParamTypeClasses      #-}
{-# Language PolyKinds                  #-}
{-# Language ScopedTypeVariables        #-}
{-# Language StandaloneDeriving         #-}
{-# Language TypeApplications           #-}
{-# Language TypeFamilies               #-}
{-# Language TypeOperators              #-}
{-# Language UndecidableInstances       #-}
{-# Language EmptyDataDecls             #-}
{-# Language StandaloneKindSignatures   #-}

module Generic.Applicative 
  ( Idiomatically
  , Generically1(..)
  , NewSums(..)
  , module Generic.Applicative.Idiom
  ) where

import Control.Applicative
import Data.Functor.Sum
import Data.Kind

import Generic.Applicative.Internal
import Generic.Applicative.Idiom

type    LeftBias :: tagKind -> (k -> Type) -> (k -> Type) -> (k -> Type)
newtype LeftBias tag f g a = LeftBias (Sum f g a)
 deriving newtype Functor

-- | An applicative instance of 'Data.Functor.Sum.Sum' biased to the
-- left.
--
-- It injects 'pure' into the 'InL' constructor:
--
-- @
--   pure = LeftBias . InL . pure
-- @
instance Idiom tag f g => Applicative (LeftBias tag f g) where
 pure :: a -> LeftBias tag f g a
 pure = LeftBias . InL . pure

 liftA2 :: (a -> b -> c) -> (LeftBias tag f g a -> LeftBias tag f g b -> LeftBias tag f g c)
 liftA2 (·) (LeftBias (InL as)) (LeftBias (InL bs)) = LeftBias $ InL $ liftA2 (·) as bs
 liftA2 (·) (LeftBias (InL as)) (LeftBias (InR bs)) = LeftBias $ InR $ liftA2 (·) (idiom @_ @tag as) bs
 liftA2 (·) (LeftBias (InR as)) (LeftBias (InL bs)) = LeftBias $ InR $ liftA2 (·) as (idiom @_ @tag bs)
 liftA2 (·) (LeftBias (InR as)) (LeftBias (InR bs)) = LeftBias $ InR $ liftA2 (·) as bs

-- | An applicative instance of 'Data.Functor.Sum.Sum' biased to the
-- right.
--
-- It injects 'pure' into the 'InR' constructor:
--
-- @
--   pure = LeftBias . InR . pure
-- @
type    RightBias :: tagKind -> (k -> Type) -> (k -> Type) -> (k -> Type)
newtype RightBias tag f g a = RightBias (Sum f g a)
 -- deriving newtype Generic1
 deriving newtype Functor

instance Idiom tag g f => Applicative (RightBias tag f g) where
 pure :: a -> RightBias tag f g a
 pure a = RightBias (InR (pure a))

 liftA2 :: (a -> b -> c) -> (RightBias tag f g a -> RightBias tag f g b -> RightBias tag f g c)
 liftA2 (·) (RightBias (InL as)) (RightBias (InL bs)) = RightBias $ InL $ liftA2 (·) as bs
 liftA2 (·) (RightBias (InL as)) (RightBias (InR bs)) = RightBias $ InL $ liftA2 (·) as (idiom @_ @tag bs)
 liftA2 (·) (RightBias (InR as)) (RightBias (InL bs)) = RightBias $ InL $ liftA2 (·) (idiom @_ @tag as) bs
 liftA2 (·) (RightBias (InR as)) (RightBias (InR bs)) = RightBias $ InR $ liftA2 (·) as bs

--

data Serve tag
instance (Idiom tag l l', Idiom tag' l' r') => Idiom (Serve tag) l (LeftBias tag' l' r') where
  idiom :: l ~> LeftBias tag' l' r'
  idiom = LeftBias . InL . idiom @_ @tag 
instance (Idiom tag l l', Idiom tag' r' l') => Idiom (Serve tag) l (RightBias tag' l' r') where
  idiom :: l ~> RightBias tag' l' r'
  idiom = RightBias . InL . idiom @_ @tag 
instance (Applicative r, Idiom tag l' r, Idiom tag' r' l') => Idiom (Serve tag) (RightBias tag' l' r') r where
  idiom :: RightBias tag' l' r' ~> r
  idiom (RightBias (InL ls')) = idiom @_ @tag @l' @r ls'
  idiom (RightBias (InR rs')) = idiom @_ @tag @l' @r (idiom @_ @tag' rs')

type
  Served :: [SumKind k] -> [SumKind k]
type family
  Served sums where
  Served '[]                  = '[]
  Served '[sum]               = '[sum]
  Served (LeftBias  tag:sums) = LeftBias  (Serve tag):Served sums
  Served (RightBias tag:sums) = RightBias (Serve tag):Served sums
  Served (sum:sums)           = sum:Served sums

-- | A modifier that is used to generically derive 'Applicative' for
-- sum types. 
-- 
-- Types with a single constructor can derive 'Applicative' using
-- @Generically1@ from @GHC.Generics@:
--
-- @
-- Generically1 f = Idiomatically f '[]
-- @
-- 
-- A datatype with multiple constructors requires more input from the
-- user: what constructor should be 'pure' and how to map between two
-- different constructors in a law-abiding way.
-- 
-- This is done by specifying the /appliative morphisms/ ('Idiom')
-- between each constructor.
-- 
-- 'Applicative' for 'Maybe' can be derived via the @Terminal@
-- applicative morphism, biased to the right. @RightBias Terminal@
-- means that when we lift over @Nothing@ and @Just@ it will result in
-- @Nothing@.
--
-- @
-- data Maybe a = Nothing | Just a
--   deriving 
--   stock Generic1
-- 
--   deriving (Functor, Applicative) 
--   via Idiomatically Maybe '[RightBias Terminal] 
-- @
--
-- The same description derives 'Applicative' for @ZipList@:
-- 
-- @
-- type ZipList :: Type -> Type
-- data ZipList a = ZNil | a ::: ZipList
--   deriving 
--   stock Generic1 
-- 
--   deriving (Functor, Applicative)
--   via Idiomatically ZipList '[RightBias Terminal]
-- @
type Idiomatically :: (k -> Type) -> [SumKind k] -> (k -> Type)
type Idiomatically f sums = Generically1 (NewSums (Served sums) f)
