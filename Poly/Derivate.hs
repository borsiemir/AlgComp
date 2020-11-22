{-# LANGUAGE FlexibleContexts #-}

module Poly.Derivate where

import Prelude hiding (exponent, (<*>))
import Data.Map hiding (map)
import Algebra.AlgebraicHierarchy
import Poly.Polynomial
import Poly.Term
import Poly.Monomial



deriv :: (Ord v, Ring a, Eq a, Ord (Monomial v o))
      => Polynomial a v o -> v -> Polynomial a v o
deriv (P []) x = P []
deriv (P ((T c mon@(M m)) : ts)) x
  | e == 0 = deriv (P ts) x
  | e == 1 = P [T c (M (delete x m))] <+> deriv (P ts) x
  | newcoef == zero = deriv (P ts) x
  | otherwise = P [T newcoef (M (adjust (\y -> y-1) x m))] <+> deriv (P ts) x
  where e = exponent x mon
        newcoef = e <*> c

