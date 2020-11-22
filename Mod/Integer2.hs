module Mod.Integer2 where

import Algebra.AlgebraicHierarchy

data Mod a i = Mod {val :: a, modular :: Maybe i}

-- Modular Integers

instance (Integral a, Integral i, Show a) => Show (Mod a i) where
  show (Mod x Nothing) = show x
  show (Mod x (Just n)) = show (x `mod` (fromIntegral n))

instance (Integral a, Integral i) => Eq (Mod a i) where
  (Mod x (Just n)) == (Mod y (Just m))
    | n /= m = error "==: Modules don't match"
    | otherwise = x `mod` (fromIntegral n) == y `mod` (fromIntegral n)
  (Mod x Nothing) == (Mod y (Just m)) = x `mod` (fromIntegral m) == y `mod` (fromIntegral m)
  (Mod x (Just n)) == (Mod y Nothing) = x `mod` (fromIntegral n) == y `mod` (fromIntegral n)
  _ == _ = error "==: Modules don't match"
  
instance (Integral a, Integral i) => Ring (Mod a i) where
  one = Mod 1 Nothing
  zero = Mod 0 Nothing
  (Mod x (Just n)) <+> (Mod y (Just m))
    | n == m = Mod ((x + y) `mod` (fromIntegral n)) (Just n)
    | otherwise = error "(<+>): Modules don't match"
  (Mod x Nothing) <+> (Mod y (Just m)) = Mod ((x + y) `mod` (fromIntegral m)) (Just m)
  (Mod x (Just n)) <+> (Mod y Nothing) = Mod ((x + y) `mod` (fromIntegral n)) (Just n)
  _ <+> _ = error "(<+>): No module at all"
  (Mod x (Just n)) <.> (Mod y (Just m))
    | n == m = Mod ((x * y) `mod` (fromIntegral n)) (Just n)
    | otherwise = error "(<.>): Modules don't match"
  (Mod x Nothing) <.> (Mod y (Just m)) = Mod ((x * y) `mod` (fromIntegral m)) (Just m)
  (Mod x (Just n)) <.> (Mod y Nothing) = Mod ((x * y) `mod` (fromIntegral n)) (Just n)
  _ <.> _ = error "(<.>): No module at all"

instance (Integral a, Integral i) => CommRing (Mod a i) 

toMod :: a -> i -> Mod a i
toMod x n = Mod x (Just n)
