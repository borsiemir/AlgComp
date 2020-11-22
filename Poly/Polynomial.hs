{-# LANGUAGE FlexibleContexts #-}

module Poly.Polynomial where

import Prelude hiding (signum)
import qualified Prelude as P
import Algebra.AlgebraicHierarchy
import Poly.Monomial
import Poly.MonomialOrder
import Poly.Term

-- We will imagine Polynomials as descending lists
newtype Polynomial a v o = P [Term a v o] deriving (Eq)

-- Product of a coefficient

coefMul :: (Ord v, Ring a, Eq a) => a -> Polynomial a v o -> Polynomial a v o
y `coefMul` (P xs) = P [T c m | T x m <- xs, let c = y <.> x, c /= zero ]

-- Multiply a polynomial by a term

termMul :: (Ord v, Ring a, Eq a, Ord (Monomial v o))
        => Term a v o -> Polynomial a v o -> Polynomial a v o
termMul t (P xs) = P $ aux t xs
  where
    aux _ [] = []
    aux t@(T c m) ((T c1 m1) : xs)
      | c <.> c1 == zero = aux t xs
      | otherwise = (T (c <.> c1) (m <> m1)) : aux t xs

-- Sum of Polynomials

instance (Ord v, Ring a, Eq a, Ord (Monomial v o)) => Ring (Polynomial a v o) where
  (P xs) <+> (P ys) = P (sumTermList xs ys)
    where
      sumTermList :: (Ord v, Ring a, Eq a, Ord (Monomial v o))
                  => [Term a v o] -> [Term a v o] -> [Term a v o]
      sumTermList [] ys = ys
      sumTermList xs [] = xs
      sumTermList xs@(t1@(T c1 m1) : xs') ys@(t2@(T c2 m2) : ys')
        | m1 < m2  = t2 : sumTermList xs ys'
        | m1 > m2   = t1 : sumTermList xs' ys
        | m1 == m2 = if c1 <+> c2 == zero
                        then sumTermList xs' ys'
                        else T (c1 <+> c2) m1 : sumTermList xs' ys'
-- zero Polynomial

  zero = P []

-- neg of Polynomials

  neg (P xs) = P $ map (\t -> case t of T c m -> T (neg c) m) xs

-- Multiplications of Polynomials

  (P []) <.> _ = P []
  (P (x : xs)) <.> p = termMul x p <+> ((P xs) <.> p)

-- one Polynomial

  one = constant one

-- Polynomials are a ring

instance (Ord v, CommRing a, Eq a, Ord (Monomial v o)) => CommRing (Polynomial a v o)
instance (Ord v, Domain a, Eq a, Ord (Monomial v o)) => Domain (Polynomial a v o)

-- Show

instance (Ord v, Ring a, Show v, Show a, Eq a, HasSignum a) => Show (Polynomial a v o) where
  show (P []) = "0"
  show (P (x : xs)) = showFirst x ++ " " ++ showTermList xs
    where
      showFirstSign :: (Ring a, Eq a, HasSignum a) => a -> String
      showFirstSign x
        | signum x == one     = ""
        | signum x == neg one = "-"
        | otherwise = error ("The signum in a ring must be 1 or -1")
      
      showSign :: (Ring a, Eq a, HasSignum a) => a -> String
      showSign x
        | signum x == one     = "+"
        | signum x == neg one = "-"
        | otherwise = error ("The signum in a ring must be 1 or -1")

      showMonomial :: (Ord v, Show v) => Monomial v o -> String
      showMonomial m
        | m == mempty  = ""
        | otherwise = show m

      showFirst :: (Ord v, Ring a, Show v, Show a, Eq a, HasSignum a) => Term a v o -> String
      showFirst (T x m)
        | x == one = if m == mempty then "1" else show m
        | x == neg one = if m == mempty then "- 1" else "- " ++ show m
        | otherwise = showFirstSign x ++ " " ++ show (signum x <.> x) ++ showMonomial m
      
      showTerm :: (Ord v, Ring a, Show v, Show a, Eq a, HasSignum a) => Term a v o -> String
      showTerm (T x m)
        | x == one = if m == mempty then "+ 1" else "+ " ++ show m
        | x == neg one = if m == mempty then "- 1" else "- " ++ show m
        | otherwise = showSign x ++ " " ++ show (signum x <.> x) ++ showMonomial m
      
      showTermList :: (Ord v, Ring a, Show v, Show a, Eq a, HasSignum a) => [Term a v o] -> String
      showTermList [] = ""
      showTermList (x : xs) = showTerm x ++ " " ++ showTermList xs
    

-- Injecting elements of the ring

constant :: (Ord v,Ring a, Eq a) => a -> Polynomial a v o
constant x
  | x == zero = P []
  | otherwise = P [T x mempty]

-- Injecting variables

variable :: (Ord v, Ring a) => v -> Polynomial a v o
variable x = P [T one (inject x)]

-- Extracting leading parts

lt :: (Ord v, Ring a) => Polynomial a v o -> Term a v o
lt (P []) = T zero mempty
lt (P (t : xs)) = t

lc :: (Ord v, Ring a) => Polynomial a v o -> a
lc (P []) = zero
lc (P ((T a m) : xs)) = a

lm :: (Ord v, Ring a) => Polynomial a v o -> Monomial v o
lm (P []) = mempty
lm (P ((T a m) : xs)) = m

-- Degree of a polynomial

instance (Ord v, Ring a) => HasDegree (Polynomial a v o) where
    degree (P []) = -1
    degree (P ts) = maximum [ degree m | T _ m <- ts ]

-- Evaluate a polynomial

eval :: (Ord v, Ring a) => (v -> a) -> Polynomial a v o -> a
eval f (P xs) = ringSum (map (evalTerm f) xs)
  where
    evalTerm :: (Ord v, Ring a) => (v -> a) -> Term a v o -> a
    evalTerm f (T c m) = c <.> (evalMonomial f m)
    
    evalMonomial :: (Ord v, Ring a) => (v -> a) -> Monomial v o -> a
    evalMonomial f m = ringMul [ (f x) <^^> n | (x,n) <- toList m ]

-- map for coefficients

mapCoef :: (Ord v, Ring a, Ring b, Eq b) => (a -> b) -> Polynomial a v o -> Polynomial b v o
mapCoef f (P xs) = P [T newc m| T c m <- xs, let newc = f c, f c /= zero]

-- Coefficients

coefficients :: (Ord v, Ring a) => Polynomial a v o -> [a]
coefficients (P []) = []
coefficients (P ((T c m) : xs)) = c : coefficients (P xs)

-- SOLO PARA PRUEBAS

data XYZ = X | Y | Z deriving (Eq, Ord, Show)

-- Integers are a ring

instance HasSignum Integer where
  signum = P.signum

p1 :: Polynomial Integer XYZ GradedLex
p1 =  (variable X <+> variable Y) <.> (variable X <^^> 2)

m1 :: Monomial XYZ Lex
m1 = inject X

f :: XYZ -> Integer
f X = 2
f Y = 1
f Z = 0
