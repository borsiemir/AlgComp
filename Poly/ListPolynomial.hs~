{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Poly.ListPolynomial where

import Prelude
import Data.Sequence hiding (zipWith)
import qualified Data.Sequence as S
import Algebra.AlgebraicHierarchy hiding (rem)
import Mod.Integer
import Mod.PrimeField
import GHC.TypeLits
import Data.Proxy

newtype PolSeq = PolSeq (Seq Integer)
  deriving (Eq, Show)

-- Polynomials with one variable module X^r - 1 in Zn

modSum :: Integer -> Integer -> Integer -> Integer
modSum n x y = (x + y) `rem` n

modMul :: Integer -> Integer -> Integer -> Integer
modMul n x y = (x * y) `rem` n

shiftL :: Seq a -> Seq a
shiftL (x :<| l) = l :|> x

shiftR :: Seq a -> Seq a
shiftR (l :|> x) = x :<| l

mkProd :: Integer -> Seq Integer -> Seq Integer -> Seq Integer -> Seq Integer
mkProd n r _ Empty = r
mkProd n r l (k :<| ks) = S.zipWith (modSum n) r $ mkProd n ((modMul n k) <$> l) (shiftR l) ks

varMod :: Integer -> PolSeq
varMod r = PolSeq (0 :<| 1 :<| S.replicate (fromIntegral $ r - 2) 0)

consP :: Integer -> Integer -> Integer -> PolSeq
consP r n c = PolSeq (c `rem` n :<| S.replicate (fromIntegral $ r - 1) zero)

varPow :: Integer -> Integer -> PolSeq
varPow r k = PolSeq $ (prefix |> one) >< suffix
  where
    m = k `rem` r
    prefix :: Seq Integer
    prefix = S.replicate (fromIntegral $ m) 0
    suffix :: Seq Integer
    suffix = S.replicate (fromIntegral $ r-m - 1) 0

--- More general
{-
newtype PolSeq (r :: Nat) a = PolSeq (Seq a)
  deriving (Eq, Show)

-- Polynomials with one variable module X^r - 1

shiftL :: Seq a -> Seq a
shiftL (x :<| l) = l :|> x

shiftR :: Seq a -> Seq a
shiftR (l :|> x) = x :<| l

mkProd :: Ring a => Seq a -> Seq a -> Seq a -> Seq a
mkProd r _ Empty = r
mkProd r l (k :<| ks) = S.zipWith (<+>) r $ mkProd ((k <.>) <$> l) (shiftR l) ks

instance forall a n. (KnownNat n, Ring a) => Ring (PolSeq n a) where
  one = PolSeq (S.fromList [one])
  zero = PolSeq (S.fromList [zero])
  (PolSeq xs) <+> (PolSeq ys) = PolSeq $ S.zipWith (<+>) xs ys
  (PolSeq xs) <.> (PolSeq ys) = PolSeq $ mkProd r xs ys
    where
      nnat = natVal (Proxy :: Proxy n)
      r = S.replicate (fromIntegral $ nnat) zero

var :: forall a n. (KnownNat n, Ring a) => PolSeq n a
var = PolSeq (zero :<| one :<| S.replicate (nval - 2) zero)
  where
    nval :: Int
    nval = fromIntegral $ natVal (Proxy :: Proxy n)

consP :: forall a n. (KnownNat n, Ring a) => a -> PolSeq n a
consP c = PolSeq (c :<| S.replicate (nval - 1) zero)
  where
    nval :: Int
    nval = fromIntegral $ natVal (Proxy :: Proxy n)

varPow :: forall a n. (KnownNat n, Ring a) => Integer -> PolSeq n a
varPow k = PolSeq $ (prefix |> one) >< suffix
  where
    nval = natVal (Proxy :: Proxy n)
    m = k `rem` nval
    prefix :: Seq a
    prefix = S.replicate (fromIntegral $ m) zero
    suffix :: Seq a
    suffix = S.replicate (fromIntegral $ nval-m - 1) zero

-}
