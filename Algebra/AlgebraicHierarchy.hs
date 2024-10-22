{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Algebra.AlgebraicHierarchy where

import Prelude hiding (quot, rem, quotRem, gcd)
import qualified Prelude as P
import Numeric.Natural (Natural)
import Data.List

-- A class for a functions called degree

class HasDegree a where
  degree :: a -> Integer

class HasSignum a where
  signum :: a -> a

-- Ring Hierarchy

class Ring a where
  (<+>) :: a -> a -> a
  zero :: a
  
  (<->) :: a -> a -> a
  neg :: a -> a
  neg x = zero <-> x
  x <-> y = x <+> neg y

  (<*>) :: Integral m => m -> a -> a
  exp0 <*> base0 = case compare exp0 0 of
    LT -> neg $ fastExponentation base0 (negate exp0)
    EQ -> zero
    GT -> fastExponentation base0 exp0
    where
      fastExponentation base exp
        | exp == 0  = zero
        | exp == 1  = base
        | even exp  = fastExponentation (base <+> base) (exp `P.quot` 2)
        | otherwise = base <+> (fastExponentation (base <+> base) (exp `P.quot` 2))
  
  (<.>) :: a -> a -> a
  one :: a

  (<^^>) :: Integral m => a -> m -> a
  base0 <^^> exp0
    | exp0 < 0  = error ("<^^> : Exponent should be positive")
    | otherwise = fastExponentation base0 exp0
    where
      fastExponentation base exp
        | exp == 0  = one
        | exp == 1  = base
        | even exp  = fastExponentation (base <.> base)  (exp `P.quot` 2)
        | otherwise = base <.> (fastExponentation (base <.> base) (exp `P.quot` 2))

  ringSum :: [a] -> a
  ringSum = foldr (<+>) zero

  ringMul :: [a] -> a
  ringMul = foldr (<.>) one

class Ring a => CommRing a

class CommRing a => Domain a

class Domain a => GcdDomain a where
  gcd :: a -> a -> a

  gcdList :: [a] -> a
  gcdList [] = error "gcdList: empty lis"
  gcdList [x] = x
  gcdList (x:y:xs) = gcdList $ (gcd x y) : xs

class Domain a => UFD a where
  factorise :: a -> (a,[(a,Natural)])

class Domain a => PID a

class Domain a => Euclidean a where
  quotRem :: a -> a -> (a , a)
  quot :: a -> a -> a
  rem :: a -> a -> a

  norm :: a -> Integer

  quot x y = fst $ quotRem x y
  rem  x y = snd $ quotRem x y
  quotRem x y = (quot x y, rem x y)

  powMod :: a -> Integer -> a -> a
  powMod x n y = aux (x `rem` y) n y
    where
      aux x n y
        | n == 0    = one
        | n == 1    = x `rem` y
        | even n    = aux ((x <.> x) `rem` y) (n `div` 2) y
        | otherwise = (x <.> (aux ((x <.> x) `rem` y) ((n-1) `div` 2) y)) `rem` y

-- We may want to change this

class Domain a => Field a where
  
  inv :: a -> a
  (</>) :: a -> a -> a
  inv x = one </> x
  x </> y = x <.> inv y

  (<^>) :: Integral m => a -> m -> a
  base0 <^> exp0 = case compare exp0 0 of
    LT -> inv $ fastExponentation base0 (negate exp0)
    EQ -> one
    GT -> fastExponentation base0 exp0
    where
      fastExponentation base exp
        | exp == 0  = one
        | exp == 1  = base
        | even exp  = fastExponentation (base <.> base) (exp `P.quot` 2)
        | otherwise = base <.> (fastExponentation (base <.> base) (exp `P.quot` 2))

class Field a => FiniteField a where
  char :: a -> Integer
  degreeExtension :: a -> Integer
  allValues :: [a]
  
  order :: a -> Integer
  order x = (char x) ^ (degreeExtension x)

  mulOrd :: (Eq a) => a -> Integer
  mulOrd x
    | x == zero = 0
    | otherwise =  1 + (genericLength $ takeWhile (one /=) [x <^^> n | n <- [1..]])

  generator :: (Eq a) => a
  
-- Some Instances

-- Int

instance Ring Int where
  (<+>) = (+)
  (<->) = (-)
  (<.>) = (*)
  one = 1
  zero = 0

instance CommRing Int
instance Domain Int

-- Integer

instance Ring Integer where
  (<+>) = (+)
  (<->) = (-)
  (<.>) = (*)
  one = 1
  zero = 0

instance CommRing Integer
instance Domain Integer

instance Euclidean Integer where
  quotRem = P.quotRem
  norm = abs

-- Rational

instance Ring Rational where
  (<+>) = (+)
  (<->) = (-)
  (<.>) = (*)
  one = 1
  zero = 0

instance CommRing Rational
instance Domain Rational

instance Field Rational where
  inv x = 1/x

-- Float

instance Ring Float where
  (<+>) = (+)
  (<.>) = (*)
  (<->) = (-)
  one = 1
  zero = 0

instance CommRing Float
instance Domain Float

instance Field Float where
  inv x = 1/x

-- Double

instance Ring Double where
  (<+>) = (+)
  (<.>) = (*)
  (<->) = (-)
  one = 1
  zero = 0

instance CommRing Double
instance Domain Double

instance Field Double where
  inv x = 1/x
