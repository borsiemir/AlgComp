{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module GcdInUFD.UFDareGcdDomain where

import Prelude  hiding (lookup)
import Data.List  hiding (lookup)
import Algebra.AlgebraicHierarchy

lookup :: Eq a => a -> [(a,b)] -> b
lookup _ [] = error "lookup: No value associated with the key"
lookup a ((k,v) : xs)
  | a == k = v
  | otherwise = lookup a xs

instance (UFD a,Domain a,Eq a) => GcdDomain a where
  gcd x y = ringMul [a <^^> b | a <- factors, let b = min (lookup a factx) (lookup a facty)]
    where
      factx = snd (factorise x)
      facty = snd (factorise y)
      factors = map fst factx `intersect` map fst facty
