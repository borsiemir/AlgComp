{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}

module AKS.AKSimproved where

import Algebra.AlgebraicHierarchy hiding (quot, powMod, gcd, rem)
import Mod.Integer2 (toMod)
import Data.Sequence hiding (filter, take, length)
import qualified Data.Sequence as S

existsBase :: forall a. (Integral a) => a -> a -> Bool -- given n and b exists a s.t. n = a^b
existsBase n b = aux n b 2 n -- The last two arguments is for recording where
                 -- are we looking for (we are doing a Binary Search)
  where
    aux :: a -> a -> a -> a -> Bool
    aux n b amin amax
      | amax - amin < 0 = False
      | aprox < n = aux n b amin (pivot - 1)
      | aprox > n = aux n b (pivot + 1) amax
      | otherwise = True
        where
          pivot :: a
          pivot = (amin + amax) `quot` 2
          aprox = pivot ^ b

isPerfectPower :: forall a. (Integral a) => a -> Bool
isPerfectPower n -- can n be written as a^b with b > 1
  | n <= 1 = error "isPerfectPower: Integer should be greater than 1"
  | otherwise = or [ existsBase n b | b <- [2..bmax] ]
    where
      ndouble :: Double
      ndouble = fromIntegral n
      bmax :: a
      bmax = fromInteger $ floor $ logBase 2 ndouble

-- Next we find the smallest r s.t. ord_r(n) > (log_2 n)^2  and gcd(r,n) = 1

ord :: forall a. (Integral a) => a -> a -> a
ord n i = head [b | b <- [2..n], (toMod i n) <^^>  b == one]

aks_r :: forall a. (Integral a) => a -> a
aks_r n = head [ r | r <- [2..], let k = ord r n, gcd r n == 1 && k > lowerbound]
  where
    lowerbound = floor $ (logBase 2 (fromIntegral n)) * (logBase 2 (fromIntegral n)) + 1

-- Has divisors

hasDivisors :: forall a. (Integral a) => a -> a -> Bool
hasDivisors n r = or [rem n x == 0 | x <- [2..(min r (n-1))]]

eulerTotient :: forall a. (Integral a) => a -> a
eulerTotient r = sum [1 | x <- [1..r], gcd x r == 1]

-- Polynomial part

-- We define univariate polynomials modulo X^r-1

data PolMod a i = PolMod {coef :: Seq a, modInt :: Maybe i, modPol :: Maybe i} deriving (Show)

multX :: forall a. Seq a -> Seq a
multX l = a :<| left
  where
    left :|> a = l

addMod :: forall a. (Integral a) => a -> a -> a -> a
addMod n x y = (x + y) `mod` n

mulMod :: forall a. (Integral a) => a -> a -> a -> a
mulMod n x y = (x * y) `mod` n


mkProd :: forall a. (Integral a) => a -> Seq a -> Seq a -> Seq a
mkProd n s s' = aux n (S.replicate (fromIntegral $ S.length s) 0) s s'
  where
    aux :: forall a. (Integral a) => a -> Seq a -> Seq a -> Seq a -> Seq a
    aux n acum s Empty = acum
    aux n acum s (k :<| ks) = S.zipWith (addMod n) acum $ aux n (mulMod n k <$> s) (multX s) ks


mkPow :: forall a i. (Integral a, Integral i) => a -> Seq a -> i -> Seq a
mkPow n s e
  | e == 1 = s
  | even e = mkPow n news (e `quot` 2)
  | odd e = mkProd n s (mkPow n news (e `quot` 2))
    where
      news = mkProd n s s

instance forall a. (Integral a) => Eq (PolMod a a) where
  (PolMod s (Just n) (Just r)) == (PolMod s' (Just n') (Just r'))
    | n == n' && r == r' = s == s'
    | otherwise = error "==: Modules don't match"
  _ == _ = error "==: Not implemented in generic elements"

polynomialPart :: forall a. (Integral a) => a -> a -> Bool
polynomialPart n r = and [pol1 j == pol2 j | j <- [1..upperBound]]
  where
    pol1 :: a -> PolMod a a
    pol1 j =
      (PolMod (mkPow n (j `mod` n :<| 1 :<| S.replicate (fromIntegral $ r-2) 0) n) (Just n) (Just r))

    pol2 :: a -> PolMod a a
    pol2 j = PolMod (((j + x) `mod` n) :<| right) (Just n) (Just r)
      where
        d = n `mod` r
        xs = (S.replicate (fromIntegral d) 0 >< (1 :<| S.replicate (fromIntegral $  r - d - 1) 0)) 
        x :<| right = xs

    upperBound = floor $ (sqrt $ fromIntegral $ eulerTotient r) * (logBase 2 (fromIntegral n))

-- AKS

aks :: forall a. (Integral a) => a -> Bool
aks n
  | n <= 1 = error "aks: Input must be greater than 1"
  | otherwise = if isPerfectPower n then False
                else if hasDivisors n r then False
                else if n <= r then True
                else polynomialPart n r
    where
      r = aks_r n
