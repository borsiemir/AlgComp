{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Factorization.SquareFree where

import Prelude hiding (gcd, rem, quot, exponent)
import GHC.TypeLits
import Algebra.AlgebraicHierarchy
import Poly.Polynomial hiding (XYZ, X)
import Poly.MonomialOrder
import Poly.Monomial hiding (fromList)
import Poly.PolDivision
import Poly.Term
import Poly.Derivate
import Data.List
import qualified Matrix.Gaussian as Mat
import Mod.PrimeField

-- SQUAREFREE DECOMPOSITION IN Fq

rootForSquareFree :: forall a v. (FiniteField a, Ord v, OnlyOne v, Eq a)
                  => Polynomial a v GradedLex
                  -> Polynomial a v GradedLex
rootForSquareFree (P []) = P []
rootForSquareFree (P ((T c m) : xs)) = P [T (c <^^> (pnat <^^> (nnat - 1))) (newExponent var (exponent var m `quot` pnat) m) ] <+> rootForSquareFree (P xs)
  where
    pnat = char (one :: a)
    nnat = degreeExtension (one :: a)


squarefreeDecomposition :: forall a v. (FiniteField a, Ord v, OnlyOne v, Eq a)
                        => Polynomial a v GradedLex
                        -> [Polynomial a v GradedLex]
squarefreeDecomposition f
  | degree f <= 0 = error "squarefreeDecomposition: Input can't be constant"
  | lc f /= one = error "squarefreeDecomposition: Input must be monic"
  | f' == zero = concat [ genericReplicate (pnat -1) one ++ [h] | h <- squarefreeDecomposition (rootForSquareFree f)]
  | otherwise = let g0 = gcd f f' in aux g0 (f `quot` g0) []
    where
      f' = deriv f var
      pnat = char (one :: a)
      nnat = degreeExtension (one :: a)
      lproductList :: forall a. (a -> a -> a) -> [a] -> [a] -> [a]
      lproductList f [] ys = ys
      lproductList f xs [] = xs
      lproductList f (x : xs) (y : ys) = f x y : (lproductList f xs ys)
      aux :: Polynomial a v GradedLex
          -> Polynomial a v GradedLex
          -> [Polynomial a v GradedLex]
          -> [Polynomial a v GradedLex]
      aux g w xs
        | w == one = if g == one then xs else lproductList (<.>) xs (concat [ genericReplicate (pnat -1) one ++ [h] | h <- squarefreeDecomposition (rootForSquareFree g)])
        | otherwise = aux newg neww (xs ++ [w `quot` neww])
          where
            neww = gcd g w
            newg = g `quot` neww

-- Example for squarefree factorization
        
ex1 = (variable X <+> one) <^^> 32 :: Polynomial (ExtensionField 2 1) X GradedLex
ex2 = (((variable X <^^> 2) <+> variable X) <+> one)<^^>30 :: Polynomial (ExtensionField 2 1) X GradedLex
ex3 = (((variable X <^^> 3) <-> variable X) <+> one)<^^>15 :: Polynomial (ExtensionField 2 1) X GradedLex

exnew = ex1 <.> ex2 <.> ex3

