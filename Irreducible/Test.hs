{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}

module Irreducible.Test where

import Prelude hiding (quot, gcd)
import qualified Prelude as P
import Algebra.AlgebraicHierarchy
import Poly.Polynomial hiding (XYZ, X)
import Poly.MonomialOrder
import Poly.PolDivision
import AKS.AKS (modularExp)
import Mod.Integer
import GHC.TypeLits
import EuclideanAlgorithm.Euclid
import Data.Proxy

-- Move to somewhere else

fromList :: forall a v. (Ring a, Ord v, OnlyOne v, Eq a) => [a] -> Polynomial a v GradedLex
fromList xs = aux 0 xs
  where
    aux :: Int -> [a] -> Polynomial a v GradedLex
    aux n [] = P []
    aux n (x : xs) = (constant x <.> (variable var <^^> n)) <+> aux (n+1) xs
      
instance forall n. KnownNat n => HasSignum (IntegerMod n) where
  signum _ = Mod 1

instance forall n. KnownNat n => Domain (IntegerMod n)

instance forall n. KnownNat n => Field (IntegerMod n) where
  inv m@(Mod x)
    | d /= 1 = error ("inv IntegerMod: element and module aren't coprimes")
    | otherwise = Mod (inverse `mod` nval)
    where
      nval = natVal m
      (d,inverse,_) = extendedEuclid x nval

instance forall n. KnownNat n => FiniteField (IntegerMod n) where
  char x = natVal x

  degreeExtension _ = 1

  allValues = [Mod x | x <- [0..nval-1]]
    where
      nval = natVal (Proxy :: Proxy n)

  generator = head [x | x <- allValues, mulOrd x == order (one :: IntegerMod n) - 1]

irreducibleTest :: forall a v. (FiniteField a, Ord v, OnlyOne v, Eq a)
                => Polynomial a v GradedLex -> Bool
irreducibleTest f
  | lc f /= one = error ("irreducibleTest: input should be monic")
  | otherwise = aux h0 1
  where
    p :: Integer
    p = char (one :: a)

    w :: Integer
    w = degreeExtension (one :: a)

    q = p <^^> w

    upperBound :: Integer
    upperBound = degree f `quot` 2

    h0 :: Polynomial a v GradedLex
    h0 = variable var

    aux :: Polynomial a v GradedLex -> Integer -> Bool
    aux h k
      | k > upperBound = True
      | d /= one = False
      | otherwise = aux newh (k+1)
      where
        newh = modularExp h q f
        d = gcd (newh <-> variable var) f

polynomials :: forall v a. (FiniteField a, Ord v, OnlyOne v, Eq a)
            => Integer -> [Polynomial a v GradedLex]
polynomials n = map fromList (map (\ys -> ys ++ [one]) (operationTimes n (allValues :: [a]) [[]]))
  where
    operation :: [a] -> [[a]] -> [[a]]
    operation [x] ys = (map (\y -> y ++ [x]) ys)
    operation (x : xs) ys = (map (\y -> y ++ [x]) ys) ++ operation xs ys
    operationTimes :: Integer -> [a] -> [[a]] -> [[a]]
    operationTimes 0 xs ys = ys
    operationTimes n xs ys = operationTimes (n-1) xs (operation xs ys)

irreduciblePol :: forall v a. (FiniteField a, Ord v, OnlyOne v, Eq a)
               => Integer -> Polynomial a v GradedLex
irreduciblePol = head . filter irreducibleTest . polynomials

p :: Polynomial (IntegerMod 827) X GradedLex
p = irreduciblePol 10
