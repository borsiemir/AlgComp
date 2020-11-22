{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module EuclideanAlgorithm.Euclid where

import Prelude hiding (quot,rem, quotRem,gcd)
import Algebra.AlgebraicHierarchy
import Data.Array

-- THINGS TO IMPROVE:
-- Remake the algorithms with dinamic programming for efficiency
-- Make that extendedEuclid returns gcd in normal form but that it stills gives
-- good Bezout Cofficients
-- Make individual functions for gcd, first coefficient and snd coefficient in
-- extended euclid

euclid :: (Eq a, Euclidean a) => a -> a -> a
euclid x0 y0 = aux x0 y0
  where
    aux x y
      | y == zero = x
      | otherwise = euclid y (rem x y)

extendedEuclid :: (Eq a, Euclidean a) => a -> a -> (a , a , a)
extendedEuclid x0 y0 = aux (x0 , one , zero) (y0 , zero , one)
  where -- paso1 is stricly before paso 2
    aux :: (Eq a, Euclidean a) => (a , a , a) -> (a ,a , a) -> (a , a , a)
    aux paso1@(r , s , t) paso2@(r', s', t')
      | r' == zero = paso1
      | otherwise  = aux paso2 (rem r r', s <-> (q <.> s'), t <-> (q <.> t'))
      where
        q = quot r r'

-- With this we can prove that integers are a GcdDomain

instance GcdDomain Integer where
  gcd x y = abs $ euclid x y
