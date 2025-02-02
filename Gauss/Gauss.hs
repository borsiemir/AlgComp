module Gauss.Gauss where

import Algebra.AlgebraicHierarchy hiding (signum)
import Prelude hiding (quot)

data Gauss a = Gauss {rPart :: a, iPart :: a} deriving (Eq)

instance (Eq a, Num a, Show a) => Show (Gauss a) where
  show (Gauss x y)
    | signum y == -1  = (show x) ++ " - " ++ (show $ abs y) ++ "i"
    | otherwise       = (show x) ++ " + " ++ (show y) ++ "i"

instance Ring a => Ring (Gauss a) where
  (Gauss x1 y1) <+> (Gauss x2 y2) = Gauss (x1 <+> x2) (y1  <+> y2)

  (Gauss x1 y1) <.> (Gauss x2 y2) = Gauss ((x1 <.> x2) <-> (y1 <.> y2)) ((x1 <.> y2) <+> (x2 <.> y1))

  zero = Gauss zero zero

  one = Gauss one zero

i :: Ring a => Gauss a
i = Gauss zero one

instance Num a => Num (Gauss a) where
  (Gauss x1 y1) + (Gauss x2 y2) = Gauss (x1 + x2) (y1 + y2)
  (Gauss x1 y1) * (Gauss x2 y2) = Gauss (x1*x2-y1*y2) (x1*y2+x2*y1)
  negate (Gauss x y) = Gauss (negate x) (negate y)
  abs (Gauss x y) = error ("abs isn't defined in Gauss")
  signum = error ("signum isn't defined in Gauss")
  fromInteger n = Gauss (fromInteger n) 0

instance Ring a =>  CommRing (Gauss a)
instance Ring a =>  Domain (Gauss a)

instance (Integral a, Ring a) => Euclidean (Gauss a) where
  quot (Gauss a b) (Gauss c d) = Gauss (round r) (round s)
    where
      doubDen :: Double
      doubDen = fromIntegral $ c*c + d*d
      doubNum1 :: Double
      doubNum1 = fromIntegral $ a*c + b*d
      doubNum2 :: Double
      doubNum2 = fromIntegral $ b*c - a*d
      r = doubNum1 / doubDen
      s = doubNum2 / doubDen

  rem x y = x - y*(quot x y)
  
  norm (Gauss x y) = toInteger $ (x <.> x) <+> (y <.> y)
