module ChineseRemainderTheorem.CRT where

import Prelude hiding (quot,rem)
import Algebra.AlgebraicHierarchy
import EuclideanAlgorithm.Euclid

crt :: (Euclidean a, Eq a) => [(a,a)] -> a -- We asume that the numbers in map snd
       -- [(a,a)] are pairwise coprime
crt xs = (ringSum [ (independentTerms !! i) <.> s i <.> partN i | i <- [0..l-1] ]) `rem` totalN
  where
    l = length xs
    independentTerms = map fst xs
    modules = map snd xs

    totalN = ringMul modules

    partN i = totalN `quot` (modules !! i)

    s i = let (_,_,result) = extendedEuclid (modules !! i) (partN i) in result


