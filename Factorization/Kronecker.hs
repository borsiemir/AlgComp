{-# LANGUAGE ScopedTypeVariables #-}

module Factorization.Kronecker where

import Prelude hiding (rem, quot)
import Algebra.AlgebraicHierarchy
import Poly.Polynomial hiding (X)
import Poly.MonomialOrder
import Poly.PolDivision 
import qualified Matrix.Gaussian as M
import Data.List
import Factorization.Berlekamp (fromListPol)

-- Given matrix m and vector b such that m*x=b has an unique solution, solves give the x

content :: (Ord v, OnlyOne v) => Polynomial Integer v GradedLex -> Integer
content = gcdList . coefficients

solve :: M.Matrix Rational -> [Rational] -> [Rational]
solve mat xs
  | n /= l = error "solve: Not the same numbers of rows and elements in the list"
  | otherwise =  M.getColumn (m+1) (M.gauss mat')
  where
    n = M.nrows mat
    m = M.ncols mat
    l = length xs
    mat' = M.matrix n (m+1) (\(i,j) -> if j == m+1 then xs !! (i-1) else mat M.! (i,j))

vandermoreMatrix :: [Integer] -> M.Matrix Rational
vandermoreMatrix xs = M.matrix l l (\(i,j) -> (xs' !! (i-1)) <^^> (l-j))
  where
    l = length xs
    xs' :: [Rational]
    xs' = map fromIntegral xs

kronecker :: forall v. (Ord v, OnlyOne v)
          => Polynomial Integer v GradedLex
          -> Maybe (Polynomial Rational v GradedLex)
kronecker f
  | d <= 0 = error "kronecker: Input can't be constant polynomial"
  | d == 1 = Nothing
  | f0 == 0 = Just (variable var)
  | f1 == 0 = Just (variable var <-> constant (fromIntegral $ 1))
  | otherwise = aux 1 mList [0,1]
    where
      d = degree f
      f0 = eval (\_ -> 0) f
      f1 = eval (\_ -> 1) f
      fRat :: Polynomial Rational v GradedLex
      fRat = mapCoef fromIntegral f

      mList = [1] : [f0] : [[c] | c <- [2..f0 `quot` 2], f0 `rem` c == 0]
      
      mListFun :: Integer -> [Integer]
      mListFun x = 1 : (-1) : fx : (-fx) : concat [[c,-c] | c <- [2..fx `quot` 2], fx `rem` c == 0]
        where
          fx = eval (\_ -> x) f

      upperBound = d `quot` 2

      aux :: Integer -> [[Integer]] -> [Integer] -> Maybe (Polynomial Rational v GradedLex)
      aux e mList choosed
        | e > upperBound = Nothing
        | otherwise = auxinaux newmList
        where
          newmList = [x ++ [y] | x <- mList, y <- mListFun (last choosed)]

          firstNew :: [Integer] -> Integer -> Integer
          firstNew xs x
            | not (x `elem` xs) = x
            | not ((-x) `elem` xs) = -x
            | otherwise = firstNew xs (x+1)
          
          auxinaux :: [[Integer]] -> Maybe (Polynomial Rational v GradedLex)
          auxinaux [] = aux (e+1) newmList (choosed ++ [firstNew choosed 0])
          auxinaux (x : xs)
            | head b /= 0 && fRat `rem` polcandidate == constant 0 = Just polcandidate
            | otherwise = auxinaux xs
            where
              b = solve (vandermoreMatrix choosed) (map fromIntegral x)
              polcandidate :: (Ord v, OnlyOne v) => Polynomial Rational v GradedLex
              polcandidate = fromListPol var (reverse b)

kroneckerFactorization :: forall v. (Ord v, OnlyOne v)
                       => Polynomial Integer v GradedLex
                       -> [Polynomial Integer v GradedLex]
kroneckerFactorization f
  | degree f <= 0 = error "kronecker: Input can't be constant"
  | content f /= 1 = error "kronecker: Input must be primitive"
  | otherwise = case kronecker f of
      Just g -> concat [kroneckerFactorization (mapCoef floor g), kroneckerFactorization (mapCoef floor (fRat `quot` g))]
      Nothing -> [f]
  where
    fRat :: Polynomial Rational v GradedLex
    fRat = mapCoef fromIntegral f

-- Note that instead of float we could have used round or ceiling, since in
-- fact we are only converting rationals that are integers
-- Are we sure about this?
