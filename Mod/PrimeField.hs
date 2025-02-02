{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Mod.PrimeField where

import Prelude hiding (gcd, rem, quot, exponent)
import GHC.TypeLits
import Algebra.AlgebraicHierarchy
import EuclideanAlgorithm.Euclid
import Mod.Integer
import Poly.Polynomial hiding (XYZ, X)
import Poly.MonomialOrder
import Poly.PolDivision
import Data.Proxy
import Data.List
import Irreducible.Test

-- Extensions fields

data Root = Root deriving (Eq, Ord)

instance Show (Root) where
  show Root = "α"
  
instance OnlyOne Root where
  var = Root

newtype ExtensionField (p :: Nat) (n :: Nat) = Ext {unModPol :: Polynomial (IntegerMod p) Root GradedLex}

instance forall p n. (KnownNat p, KnownNat n) => Eq (ExtensionField p n) where
  a@(Ext p) == (Ext q) = (p `rem` modular) == (q `rem` modular)
    where modular = getModPol a

instance forall p n. (KnownNat p, KnownNat n) => Show (ExtensionField p n) where
  show (Ext p) = show p

getModPol :: forall p n. (KnownNat p, KnownNat n)
          => ExtensionField p n -> Polynomial (IntegerMod p) Root GradedLex
getModPol _ = irreduciblePol (natVal (Proxy :: Proxy n))

root :: forall p n. (KnownNat p, KnownNat n) => ExtensionField p n
root = Ext (variable Root)

instance forall p n. (KnownNat p, KnownNat n) => Ring (ExtensionField p n) where
  a@(Ext p) <+> (Ext q) = Ext $ (p <+> q) `rem` getModPol a
  a@(Ext p) <-> (Ext q) = Ext $ (p <-> q) `rem` getModPol a
  a@(Ext p) <.> (Ext q) = Ext $ (p <.> q) `rem` getModPol a
  zero = Ext zero
  one = Ext one

instance forall p n. (KnownNat p, KnownNat n) => CommRing (ExtensionField p n)

instance forall p n. (KnownNat p, KnownNat n) => Domain (ExtensionField p n)

instance forall p n. (KnownNat p, KnownNat n) => Field (ExtensionField p n) where
  inv a@(Ext p)
    | a == zero = error "inv: zero is not invertible"
    | otherwise = Ext ((dinv `coefMul` inverse) `rem` modular)
    where
      modular = getModPol a
      (d,inverse,_) = extendedEuclid p modular
      dinv = inv $ lc d

cons :: forall p n. (KnownNat p, KnownNat n) => IntegerMod p -> ExtensionField p n
cons x = Ext (constant x)

instance forall n. KnownNat n => Enum (IntegerMod n) where
  succ x = x <+> 1
  pred x = x <-> 1
  toEnum n
    | n == 0 = 0
    | n > 0 = succ (toEnum (n-1))
    | n < 0 = pred (toEnum (n+1))

  fromEnum = fromInteger . unMod
  
enumFq :: forall p r. (KnownNat p, KnownNat r) => Integer -> [ExtensionField p r]
enumFq 0 = genericTake pnat $ map cons [0..]
    where
    pnat = natVal (Proxy :: Proxy p)
enumFq n = enumFq (n-1) ++ [ x <+> (y <.> (root <^^> n)) | x <- enumFq (n-1), y <- tail (enumFq 0)]
  -- We use tail (enumFq 0) in order to eliminate 0 from the list, to dont
  -- repeat elements

instance forall p n. (KnownNat p, KnownNat n) => FiniteField (ExtensionField p n) where
  char _ = natVal (Proxy :: Proxy p)

  degreeExtension _ = natVal (Proxy :: Proxy n)

  allValues = enumFq (nVal - 1)
    where
      nVal = natVal (Proxy :: Proxy n)

  generator = head [x | x <- (genericDrop (char (one :: ExtensionField p n)) allValues),
                    mulOrd x == order (one :: ExtensionField p n) - 1]

instance forall p n. (KnownNat p, KnownNat n) => HasSignum (ExtensionField p n) where
  signum _ = one
