{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Poly.PolDivision where

import Prelude hiding (quotRem, signum)
import qualified Prelude as P
import GHC.Natural
import Algebra.AlgebraicHierarchy
import Poly.Monomial
import Poly.MonomialOrder
import Poly.Polynomial hiding (X, p1, p2)
import Poly.Term
import EuclideanAlgorithm.Euclid

-- We make a class wich have the only variable

class OnlyOne a where
  var :: a

-- If R is a field, R[X] is euclidean

instance (Ord v, Field a, Eq a, Ord (Monomial v o), OnlyOne v) => Euclidean (Polynomial a v o) where
  norm = degree

  quotRem _ (P []) = error "quot: Dividing by zero polynomial"
  quotRem p q
    | d < e = (zero, p)
    | otherwise = (P [mon] <+> fst result, snd result)
    where
      d = degree p
      e = degree q
      mon = T (lc p </> lc q) (fromList [(var, d - e)])
      result = quotRem (p <-> (termMul mon q)) q

instance (Ord v, Field a, Eq a, Ord (Monomial v o), OnlyOne v) => GcdDomain (Polynomial a v o) where
  gcd f g = inv (lc d) `coefMul` d
    where
      d = euclid f g

-- Division by monic polynomial (this division is alway defined)

quotRemMonic :: (Ord v,Ring a, Eq a, Ord (Monomial v o), OnlyOne v)
         => Polynomial a v o -> Polynomial a v o -> (Polynomial a v o,Polynomial a v o)
quotRemMonic p q
  | lc q /= one = error "quotMonic: Sorry divisor should be monic"
  | d < e = (zero, p)
  | otherwise = (P [mon] <+> fst result, snd result)
    where
      d = degree p
      e = degree q
      mon = T (lc p) (fromList [(var,d - e)])
      result = quotRemMonic (p <-> (termMul mon q)) q

quotMonic p q = fst $ quotRemMonic p q
remMonic p q  = snd $ quotRemMonic p q

----------------------------------------------------------
-- Para Hacer Pruebas

data X = X deriving (Eq,Show,Ord)

instance OnlyOne X where
  var = X

instance HasSignum Rational where
  signum = P.signum

p1 :: Polynomial Integer X GradedLex
p1 = (constant 2 <.> (variable X <^^> 3)) <+> (constant 1 <.> (variable X <^^> 2)) <+> (constant 5 <.> variable X) <+> constant 1


p2 :: Polynomial Integer X GradedLex
p2 = constant 1 <.> (variable X <^^> 2) <+> constant 3
