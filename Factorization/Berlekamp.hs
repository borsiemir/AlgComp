{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Factorization.Berlekamp where

import Prelude hiding (gcd, rem, quot, exponent)
import GHC.TypeLits
import Algebra.AlgebraicHierarchy
import Mod.Integer
import Poly.Polynomial hiding (XYZ, X, f)
import Poly.MonomialOrder
import Poly.Monomial hiding (fromList)
import qualified Poly.Monomial as M
import Poly.PolDivision
import Poly.Derivate
import Data.List
import Matrix.Gaussian hiding (fromList)
import qualified Matrix.Gaussian as Mat
import Mod.PrimeField
import Factorization.SquareFree
import Factorization.DistinctDegree
import System.Random

------------------------------------------------------------------
-- Berlekamp-Splitting

-- Step one - Getting the matrix of phi_f

toListPol :: forall v a. (Ord v, OnlyOne v, Ring a, Eq a) => Polynomial a v GradedLex -> Integer -> [a]
toListPol (P []) k = genericReplicate k zero
toListPol p k = reverse (aux d p) ++ genericReplicate (k - d - 1) zero
  where
    d = degree p
    aux :: Integer -> Polynomial a v GradedLex -> [a]
    aux i p
      | i < 0 = []
      | i == degree (lm p) = lc p : aux (i-1) (p <-> (P [lt p]))
      | otherwise = zero : aux (i-1) p

fromListPol :: forall v a. (Ord v, Ring a, Eq a) => v -> [a] -> Polynomial a v GradedLex
fromListPol x cs = aux x 0 cs
  where
    aux x n [] = zero
    aux x n (c : cs) = (constant c <.> (variable x <^^> n)) <+> (aux x (n+1) cs)

modularExpPol :: forall v a o. (Ord v, OnlyOne v, Field a, Eq a, Ord (Monomial v o))
              => Polynomial a v o -> Integer -> Polynomial a v o -> Polynomial a v o
modularExpPol p n f
  | n == 0 = one
  | n == 1 = p `rem` f
  | even n = modularExpPol ((p <.> p) `rem` f) (n `div` 2) f
  | otherwise = (p <.> (modularExpPol p (n-1) f)) `rem` f

phiMatrix :: forall a v. (FiniteField a, Ord v, OnlyOne v, Eq a)
          => Polynomial a v GradedLex
          -> Matrix a
phiMatrix f
  | degree f <= 0 = error "phiMatrix: Input can't be constant"
  | lc f /= one = error "phiMatrix: Polynomial should be monic"
  | f' == zero || gcdff' /= one = error "phiMatrix: Polynomial should be squarefree"
  | otherwise = Mat.transpose $ Mat.fromList [toListPol ((modularExpPol (variable var) (qnat*e) f) <-> (variable var <^^> e)) d | e <- [0..d-1]]
  where
    f' = deriv f var
    pnat = char (one :: a)
    nnat = degreeExtension (one :: a)
    qnat = pnat <^^> nnat
    gcdff' = gcd f f'
    d = degree f

basisPhi :: forall a v. (FiniteField a, Ord v, OnlyOne v, Eq a)
         => Polynomial a v GradedLex
         -> [Polynomial a v GradedLex]
basisPhi f = map (fromListPol var) (kernBase $ phiMatrix f)

-- Berlekamp

berlekampSplitting :: forall a v. (FiniteField a, Ord v, OnlyOne v, Eq a)
          => Polynomial a v GradedLex
          -> Polynomial a v GradedLex
berlekampSplitting f 
  | s == 1 = f
  | otherwise = aux 2
  where
    pnat = char (one :: a)
    rnat = degreeExtension (one :: a)
    qnat = pnat <^^> rnat
    basis = basisPhi f
    s = length basis
    h i = basis !! (i-1)
    
    aux i
      | i <= s && null xs = aux (i + 1)
      | i <= s && not (null xs) = head xs
      | i > s = error "berlekampSplitting: Factor should have been found already"
      where
        xs = [g | a <- (allValues :: [a]), let g = gcd f (h i <-> constant a),  g /= one, g /= f]

berlekamp :: forall a v. (FiniteField a, Ord v, OnlyOne v, Eq a)
          => Polynomial a v GradedLex
          -> [Polynomial a v GradedLex]
berlekamp f = aux [f] []
  where
    basis = basisPhi f
    s = length basis
    aux :: [Polynomial a v GradedLex]
        -> [Polynomial a v GradedLex]
        -> [Polynomial a v GradedLex]
    aux factor irred
      | length factor + length irred < s = if h /= g then aux ((g `quot` h) : h : tail factor) irred
                                            else aux (tail factor) (g : irred)
      | otherwise = factor ++ irred
      where
        g = head factor
        h = berlekampSplitting g

factorBerlekamp :: forall a v. (FiniteField a, Eq a, Ord v, OnlyOne v)
                => Polynomial a v GradedLex
                -> [(Polynomial a v GradedLex, Integer)]
factorBerlekamp f = concat $ map aux' $ map (\(g,i) -> (berlekamp g, i)) $ filter (\(g,_) -> degree g >= 1) (aux 1 xs)
  where
    aux :: forall a. Integer -> [a] -> [(a,Integer)]
    aux _ [] = []
    aux n (x : xs) = (x,n) : aux (n+1) xs
    aux' :: forall a b. ([a],b) -> [(a,b)]
    aux' (xs,y) = [(x,y) | x <- xs]
    xs = squarefreeDecomposition f
    l = length xs - 1

-- Now that we cant factorize polynomials, they form a UFD:

instance forall a v. (FiniteField a, Eq a, Ord v, OnlyOne v)
         => UFD (Polynomial a v GradedLex) where
  factorise p = (constant lcp , map (\(f,k) -> (f,fromInteger k)) $ factorBerlekamp g)
    where
      lcp = lc p
      g = (constant (inv lcp)) <.> p

----------------------------------------------------------------------------
-- LAS VEGAS VERSION OF BELERKAMP (ONLY FOR ODD CHARACTHERISTIC)
----------------------------------------------------------------------------

randList :: forall g. (RandomGen g) => g -> Int -> Int -> [Int]
randList gen n m = take n (randomRs (0 :: Int,m-1) gen)

lasVegasBerlekamp :: forall a v g. (FiniteField a, Eq a, Ord v, OnlyOne v, RandomGen g)
                  => g
                  -> Polynomial a v GradedLex
                  -> [Polynomial a v GradedLex]
lasVegasBerlekamp gen f = aux gen [f]
  where
    q = order (one :: a)
    basis = basisPhi f
    s = length basis

    aux :: g -> [Polynomial a v GradedLex]
             -> [Polynomial a v GradedLex]
    aux gen result
      | l < s = if (w == one || w == pol) then aux newgen result else aux newgen ((delete pol result) ++ [w,pol `quot` w])
      | otherwise = result
      where
        l = length result

        (randnum, newgen) = randomR (0,l-1) gen

        pol = head $ filter (\f -> degree f > 1) (drop randnum result ++ take randnum result)
        
        coeffs = map (\x -> (allValues :: [a]) !! x) $ randList gen s (fromIntegral q)

        h = ringSum $ zipWith coefMul coeffs basis

        w = gcd pol ((h <^^> ((q-1) `quot` 2)) <-> constant one)

factorlasVegas :: forall a v g. (FiniteField a, Eq a, Ord v, OnlyOne v, RandomGen g)
                => g
                -> Polynomial a v GradedLex
                -> [(Polynomial a v GradedLex, Integer)]
factorlasVegas gen f = concat $ map aux' $ map (\(g,i) -> (lasVegasBerlekamp gen g, i)) $ filter (\(g,_) -> degree g >= 1) (aux 1 xs)
  where
    aux :: forall a. Integer -> [a] -> [(a,Integer)]
    aux _ [] = []
    aux n (x : xs) = (x,n) : aux (n+1) xs
    aux' :: forall a b. ([a],b) -> [(a,b)]
    aux' (xs,y) = [(x,y) | x <- xs]
    xs = squarefreeDecomposition f
    l = length xs - 1

-- PRUEBAS

prueba pol = do
  gen <- newStdGen
  print $ factorlasVegas gen pol

polPhi = (variable X <^^> 3) <+> (variable X <^^> 2) <+> (variable X) <+> (constant (one <+> root)) :: Polynomial (ExtensionField 3 2) X GradedLex

polFacto = (variable X <^^> 9) <-> (variable X) :: Polynomial (ExtensionField 3 2) X GradedLex
