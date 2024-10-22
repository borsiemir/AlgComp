{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}


{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- Not Supported, go to AKSimproved

module AKS.AKS where

import Prelude hiding (gcd, rem)
import Algebra.AlgebraicHierarchy hiding (quot)
import EuclideanAlgorithm.Euclid
import Mod.Integer
import GHC.Natural
import GHC.TypeLits
import Data.Proxy
import Poly.Polynomial hiding (X)
import Poly.MonomialOrder (GradedLex)
import Poly.PolDivision
import Poly.Term
import Poly.Monomial

-- First We make an algorithm for detecting when a number is a power

existsBase :: Integer -> Integer -> Bool -- given n and b exists a s.t. n = a^b
existsBase n b = aux n b 2 n -- The last two arguments is for recording where
                 -- are we looking for (we are doing a Binary Search)
  where
    aux :: Integer -> Integer -> Integer -> Integer -> Bool
    aux n b amin amax
      | amax - amin < 0 = False
      | aprox < n = aux n b amin (pivot - 1)
      | aprox > n = aux n b (pivot + 1) amax
      | otherwise = True
        where
          pivot :: Integer
          pivot = (amin + amax) `quot` 2
          aprox = pivot <^^> b

isPerfectPower :: Integer -> Bool
isPerfectPower n -- can n be written as a^b with b > 1
  | n <= 1 = error "isPerfectPower: Integer should be greater than 1"
  | otherwise = or [ existsBase n b | b <- [2..bmax] ]
    where
      ndouble :: Double
      ndouble = fromInteger n
      bmax :: Integer
      bmax = floor $ logBase 2 ndouble

-- Next we find the smallest r s.t. ord_r(n) > (log_2 n)^2  and gcd(r,n) = 1

ord :: Integer -> Integer -> Integer
ord n i = head [b | b <- [2..n], withMod n (modi <^^> b) == 1]
  where
    modi :: (forall m. KnownNat m => IntegerMod m)
    modi = toMod i

aks_r :: Integer -> Integer
aks_r n = head [ r | r <- [2..], let k = ord r n, gcd r n == 1 && k > lowerbound]
  where
    lowerbound = ceiling $ (logBase 2 (fromInteger n)) ^ 2

-- Now we check that between 2 and min(r,n-1) n hasn't any divisors

hasDivisors :: Integer -> Integer -> Bool
hasDivisors n r = or [rem n x == 0 | x <- [2..(min r (n-1))]]
-- Note that if hasDivisor n (aks_r n) gives True, aks n should give False
-- (because n hasDivisors)

-- Euler totient function with divisor sum property

-- IMPROVE THIS BY FAR

eulerTotient :: Integer -> Integer
eulerTotient n = sum [1 | x <- [1..n], gcd x n == 1]

len :: Integer -> Integer
len n
  | n == 0 = 1
  | otherwise = (floor $ logBase 2 (fromInteger $ abs n)) + 1


-- Final part with polynomials

mapCoeff :: (Ord v, Ring b, Eq b, Ord (Monomial v o))
         => (a -> b) -> Polynomial a v o -> Polynomial b v o
mapCoeff _ (P []) = P []
mapCoeff f (P ((T c m) : xs))
  | f c == zero = mapCoeff f (P xs)
  | otherwise = P [T (f c) m] <+> mapCoeff f (P xs)

withModPolProxy :: forall n v o. (KnownNat n, Ord v, Ord (Monomial v o))
                  => (forall m. KnownNat m => Polynomial (IntegerMod m) v o)
                  -> Proxy n -> Polynomial Integer v o
withModPolProxy p modProxy =
  mapCoeff (\k -> (unMod (k :: IntegerMod n)) `mod` (natVal modProxy))
           (p :: Polynomial (IntegerMod n) v o)

withModPol :: forall v o. (Ord v, Ord (Monomial v o))
           => Integer
           -> (forall m. KnownNat m => Polynomial (IntegerMod m) v o)
           -> Polynomial Integer v o
withModPol k p = reifyInteger k (withModPolProxy p)

modularExp :: (Ord v,Ring a,Eq a,Ord (Monomial v o),OnlyOne v)
           => Polynomial a v o -> Integer -> Polynomial a v o -> Polynomial a v o
modularExp p 1 q = p `remMonic` q
modularExp p n q
  | even n = auxpol <.> auxpol `remMonic` q
  | odd n =  (p <.> auxpol <.> auxpol) `remMonic` q
    where
      e = degree q
      auxpol = modularExp p (n `div` 2) q

polynomialPart :: Integer -> Integer -> Bool
polynomialPart n r = or [withModPol n (p1 a) /= withModPol n (p2 a) | a <- [1..upperBound]]
  where
    upperBound :: Integer
    upperBound = 2 * (len n) * (floor $ sqrt (fromInteger r :: Float) ) + 1
    p :: forall m. KnownNat m =>  Polynomial (IntegerMod m) X GradedLex
    p = (variable X <^^> r) <-> one
    p1 :: Integer -> (forall m. KnownNat m => Polynomial (IntegerMod m) X GradedLex)
    p1 a = (modularExp (variable X <-> constant (toMod a)) n p) `remMonic` p
    p2 :: Integer -> (forall m. KnownNat m => Polynomial (IntegerMod m) X GradedLex)
    p2 a = ((modularExp (variable X) n p) <-> constant (toMod a)) `remMonic` p

-- AKS

aks :: Integer -> Bool
aks n
  | n <= 1 = error "aks: Input must be greater than 1"
  | otherwise = if isPerfectPower n then False
                else if hasDivisors n r then False
                else if n <= r then True
                else if polynomialPart n r then False
                else True
    where
      r = aks_r n

primesBetween :: Integer -> Integer -> [(Integer,Bool)]
primesBetween n m =  [(p,aks p) | p <- [n..m]]

isprime :: Integer -> Bool
isprime n = and [ gcd x n == 1 | x <- [1..(floor $ sqrt (fromInteger n))]]
