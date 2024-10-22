{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-} -- Ver que hace

module Factorization.DistinctDegree where

import Prelude hiding (gcd, rem, quot, exponent)
import GHC.TypeLits
import Algebra.AlgebraicHierarchy
import AKS.AKS (modularExp)
import Mod.Integer
import Poly.Polynomial hiding (XYZ, X)
import Poly.MonomialOrder
import qualified Poly.Monomial as M
import Poly.PolDivision
import Poly.Term
import Poly.Derivate
import Mod.PrimeField

-- Distinct degree factorization

ddf :: forall a v. (FiniteField a, Ord v, OnlyOne v, Eq a)
    => Polynomial a v GradedLex
    -> [(Polynomial a v GradedLex, Integer)]
ddf f
  | degree f <= 0 = error "ddf: Polynomial can't be constant"
  | lc f /= one = error "ddf: Polynomial should be monic"
  | f' == zero || gcdff' /= one = error "ddf: Polynomial should be squarefree"
  | otherwise = aux 0 f (variable var) []
  where
    f' = deriv f var
    pnat = char (one :: a)
    nnat = degreeExtension (one :: a)
    qnat = pnat <^^> nnat
    gcdff' = gcd f f'
    aux :: Integer
        -> Polynomial a v GradedLex
        -> Polynomial a v GradedLex
        -> [(Polynomial a v GradedLex, Integer)]
        -> [(Polynomial a v GradedLex, Integer)]
    aux d g h xs
      | d <= (degree g `quot` 2) - 1 = if degree fd /= 0 then aux newd newg newh (xs ++ [(fd,newd)])
                                                         else aux newd newg newh xs
      | g /= one = xs ++ [(g,degree g)]
      | otherwise = xs
      where
        newd = d + 1
        newh = modularExp h qnat g
        fd = gcd g (newh <-> variable var)
        newg = g `quot` fd
