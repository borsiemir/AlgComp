{-# LANGUAGE DataKinds #-}

module Poly.Pruebas where

import Prelude hiding (rem)
import Poly.Monomial
import Poly.Polynomial hiding (X,Y,Z,f)
import Algebra.AlgebraicHierarchy
import Mod.Integer
import Poly.Term
import Poly.MonomialOrder
import Poly.PolDivision hiding (X)
import Mod.PrimeField

a = 5 :: IntegerMod 23455

b = 5 :: Integer 

termMulMod :: (Ord v)
           => Term Integer v GradedLex
           -> Polynomial Integer v GradedLex
           -> Integer -> Polynomial Integer v GradedLex
termMulMod t (P xs) n = P $ aux t xs
  where
    aux _ [] = []
    aux t@(T c m) ((T c1 m1) : xs)
      | coef == zero = aux t xs
      | otherwise = (T coef (m <> m1)) : aux t xs
        where coef = (c <.> c1) `rem` n

-- Sum of Polynomials

sumPolMod :: (Ord v)
          => Polynomial Integer v GradedLex
          -> Polynomial Integer v GradedLex
          -> Integer -> Polynomial Integer v GradedLex
sumPolMod (P xs) (P ys) n = P (sumTermList xs ys n)
  where
    sumTermList :: (Ord v)
                => [Term Integer v GradedLex]
                -> [Term Integer v GradedLex]
                -> Integer
                -> [Term Integer v GradedLex]
    sumTermList [] ys n = [T coef m | T c m <- ys, let coef = c `mod` n, coef /= 0]
    sumTermList xs [] n = [T coef m | T c m <- xs, let coef = c `mod` n, coef /= 0]
    sumTermList xs@(t1@(T c1 m1) : xs') ys@(t2@(T c2 m2) : ys') n
      | m1 < m2  = (T (c2 `mod` n) m2) : sumTermList xs ys' n
      | m1 > m2  = (T (c1 `mod` n) m1) : sumTermList xs' ys n
      | m1 == m2 = if coef == zero
                      then sumTermList xs' ys' n
                      else T coef m1 : sumTermList xs' ys' n
      where coef = (c1 <+> c2) `mod` n

-- Multiplications of Polynomials

mulPolMod :: (Ord v)
          => Polynomial Integer v GradedLex
          -> Polynomial Integer v GradedLex
          -> Integer -> Polynomial Integer v GradedLex
mulPolMod (P []) _ _ = P []
mulPolMod (P (x : xs)) p n = termMulMod x p n <+> (mulPolMod (P xs) p n)

powModPol :: (Ord v, OnlyOne v)
          => Polynomial Integer v GradedLex
          -> Integer
          -> Integer
          -> Polynomial Integer v GradedLex
          -> Polynomial Integer v GradedLex
powModPol p b n q
  | b == 0 = one
  | b == 1 = p
  | even b = powModPol aux (b `div` 2) n q
  | odd b  = mulPolMod p (powModPol aux ((b-1) `div` 2) n q) n
    where aux = (mulPolMod p p n) `remMonic` q
data X = X deriving (Ord,Show,Eq)

instance (OnlyOne X) where
  var = X

g = (variable X <-> constant 1) :: Polynomial Integer X GradedLex
f = (variable X <-> constant 1) :: Polynomial (IntegerMod 827) X GradedLex
modg = (variable X <^^> 106) <-> constant 1 :: Polynomial Integer X GradedLex
modf = (variable X <^^> 106) <-> constant 1 :: Polynomial (IntegerMod 827) X GradedLex

newtype UPol a = Pol [a]
