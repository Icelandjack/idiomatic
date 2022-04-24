{-# Language DataKinds                #-}
{-# Language DeriveGeneric            #-}
{-# Language DerivingStrategies       #-}
{-# Language DerivingVia              #-}
{-# Language StandaloneKindSignatures #-}
{-# Language TypeApplications         #-}

module Main where

import Data.Kind
import GHC.Generics
import Control.Applicative hiding (ZipList(..))
import Generic.Applicative 

infixr 5 :::

type ZipList :: Type -> Type
data ZipList a = Nil | a ::: ZipList a
  deriving 
  stock (Eq, Show, Generic1)

  deriving (Functor, Applicative)
  via Idiomatically ZipList 
    '[RightBias Terminal]

takeZipList :: Int -> ZipList a -> ZipList a
takeZipList 0 _        = Nil
takeZipList n Nil      = Nil
takeZipList n (a:::as) = a:::takeZipList (n-1) as

main :: IO ()
main = do
  print (takeZipList 6 (pure @ZipList 5))

  let as :: ZipList Int
      as = 1 ::: 2 ::: 3 ::: 4 ::: Nil

  print (liftA2 (+) as (pure 100))
