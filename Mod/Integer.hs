{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-} -- Ver que hace
{-# LANGUAGE TypeFamilies #-} -- Ver que hace

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Mod.Integer where

import Data.Proxy (Proxy(..))
import GHC.TypeLits
import qualified GHC.TypeLits as N
import Algebra.AlgebraicHierarchy hiding (rem, signum, quot)

newtype IntegerMod (n :: Nat) = Mod {unMod :: Integer} deriving (Eq, Ord)

toMod :: forall m. KnownNat m => Integer -> IntegerMod m
toMod n = Mod $ n `mod` (natVal (Proxy :: Proxy m))

reifyInteger :: Integer -> (forall n. KnownNat n => Proxy n -> w) -> w
reifyInteger 0 f = f (Proxy :: Proxy 0)
reifyInteger n f
  | n < 0 = error "reifyInteger: Only integers >= 0"
  | even n = reifyInteger (n `quot` 2) (\(Proxy :: Proxy n) -> f (Proxy :: Proxy (n N.* 2)))
  | otherwise = reifyInteger (n - 1) (\(Proxy :: Proxy n) -> f (Proxy :: Proxy (n + 1)))

getMod :: forall m. KnownNat m => IntegerMod m -> Integer
getMod _ = natVal (Proxy :: Proxy m)

-- Polymorphic modular values

withModProxy :: forall m. KnownNat m
             => (forall n. (KnownNat n) => IntegerMod n) -> Proxy m -> Integer
withModProxy k modProxy = (unMod (k :: IntegerMod m)) `mod` (natVal modProxy)

withMod :: Integer -> (forall m. (KnownNat m) => IntegerMod m) -> Integer
withMod k m = reifyInteger k (withModProxy m)

instance forall n. KnownNat n => Show (IntegerMod n) where
  show (Mod i) = show (i `mod` natVal (Proxy :: Proxy n))

instance (KnownNat n) => Num (IntegerMod n) where
  (Mod x) + (Mod y) = Mod $ (x + y) `mod` natVal (Proxy :: Proxy n)
  (Mod x) * (Mod y) = Mod $ (x * y) `mod` natVal (Proxy :: Proxy n)
  abs (Mod x) = Mod $ x `mod` natVal (Proxy :: Proxy n)
  signum (Mod x) = Mod 1
  negate (Mod x) = Mod $ (negate x) `mod` natVal (Proxy :: Proxy n)
  fromInteger x = toMod x

instance (KnownNat n) => Ring (IntegerMod n) where
  (<+>) = (+)
  (<->) = (-)
  (<.>) = (*)
  one = 1
  zero = 0

instance (KnownNat n) => CommRing (IntegerMod n)


