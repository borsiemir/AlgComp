{-# LANGUAGE FlexibleInstances #-}

module Poly.MonomialOrder where

import Algebra.AlgebraicHierarchy
import GHC.Natural
import Prelude hiding (lex)
import Poly.Monomial

lex' :: Ord v => [(v,Integer)] -> [(v,Integer)] -> Ordering
lex' [] [] = EQ
lex' [] ys = LT
lex' xs [] = GT
lex' ((x,n) : xs) ((y,m) : ys) = case compare x y of
  LT -> GT
  EQ -> case compare n m of
    LT -> LT
    EQ -> lex' xs ys
    GT -> GT
  GT -> LT

lex :: Ord v => Monomial v o -> Monomial v o -> Ordering
lex m1 m2 = lex' (toList m1) (toList m2) 

revlex :: Ord v => Monomial v o -> Monomial v o -> Ordering
revlex m1 m2 = lex' (toDescList m1) (toDescList m2)

data Lex
data RevLex
data GradedLex
data GradedRevLex

instance Ord v => Ord (Monomial v Lex) where
  compare = lex

instance Ord v => Ord (Monomial v RevLex) where
  compare = revlex

instance Ord v => Ord (Monomial v GradedLex) where
  compare m1 m2 = case compare (degree m1) (degree m2) of
    LT -> LT
    GT -> GT
    EQ -> lex m1 m2

instance Ord v => Ord (Monomial v GradedRevLex) where
  compare m1 m2 = case compare (degree m1) (degree m2) of
    LT -> LT
    GT -> GT
    EQ -> lex m1 m2
