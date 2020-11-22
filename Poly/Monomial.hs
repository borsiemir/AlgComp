module Poly.Monomial where

import GHC.Natural
import Data.Map (Map)
import qualified Data.Map as Map
import Algebra.AlgebraicHierarchy

newtype Monomial v o = M (Map v Integer) deriving (Eq) -- v is the type for
-- variables, o is a phantom type for introducing an ordering

-- Showing Monomials

instance (Ord v, Show v) => Show (Monomial v o) where
  show (M m)
    | Map.null m = "1"
    | otherwise = aux (Map.toList m)
    where
      aux :: (Ord v, Show v) => [(v,Integer)] -> String
      aux [] = ""
      aux ((a,n) : xs)
        | n == 1 = show a ++ aux xs
        | otherwise = show a ++ "^" ++ show n ++ aux xs

-- Monomials form a semigroup

instance Ord v => Semigroup (Monomial v o) where
  (M m1) <> (M m2) = M $ Map.unionWith (+) m1 m2
  
instance Ord v => Monoid (Monomial v o) where
  mempty = M Map.empty
  
inject :: Ord v => v -> Monomial v o
inject v = M $ Map.singleton v 1

-- Injecting variables and with the semigroup operations we can create any
-- Monomial we want

-- Monomials and List

toList :: Ord v => Monomial v o -> [(v,Integer)] -- in fact this gives an
          -- ascending list with respect to the variables
toList (M m) = Map.toList m

toAscList :: Ord v => Monomial v o -> [(v,Integer)]
toAscList = toList

toDescList :: Ord v => Monomial v o -> [(v,Integer)]
toDescList (M m) = Map.toDescList m

fromList :: Ord v => [(v,Integer)] -> Monomial v o
fromList xs = M $ Map.fromList (filter (\x -> snd x /= 0) xs) -- Here we assume
              -- that the list doesnt contain a negative exponent

-- Given a variable gives its exponent

exponent :: Ord v => v -> Monomial v o -> Integer
exponent x (M m) = Map.findWithDefault 0 x m

-- Changing an exponent

newExponent :: Ord v => v -> Integer -> Monomial v o -> Monomial v o
newExponent v n (M m)
  | n < 0 = error "newExponent: Exponent must be positive"
  | n == 0 = M (Map.delete v m)
  | otherwise = M (Map.insert v n m)

-- List of variables

variables :: Ord v => Monomial v o -> [v]
variables = map fst . toList

-- Monomials have degree

instance Ord v => HasDegree (Monomial v o) where
  degree = sum . map (toInteger . snd) . toList
