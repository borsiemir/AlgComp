module Poly.Term where

import Algebra.AlgebraicHierarchy
import Poly.Monomial

data Term a v o = T a (Monomial v o) deriving (Eq, Show)

instance (Ring a, Ord v) => Semigroup (Term a v o) where
  (T t1 m1) <> (T t2 m2) = T (t1 <.> t2) (m1 <> m2)

instance (Ring a, Ord v) => Monoid (Term a v o) where
  mempty = T one mempty
