module  Matrix.Gaussian where

import Data.Array hiding ((!))
import qualified Data.Array as A
import Data.List hiding (transpose)
import Algebra.AlgebraicHierarchy

-- We create the datatype of matrixes as arrays with two Int indixes

data Matrix a = Matrix {nrows :: Int, ncols :: Int, toArray :: (Array (Int,Int) a)}

instance Show a => Show (Matrix a) where
  show (Matrix n m arr) = unlines [ "( " ++ showRow [ blankSpace (maximumLengthInColum j - length (symbol i j)) ++ symbol i j | j <- [1..m]] | i <- [1..n]]
    where
      symbol :: Int -> Int -> String
      symbol i j = show (arr A.! (i,j))
      maximumLengthInColum :: Int -> Int
      maximumLengthInColum j = maximum [length $ symbol i j | i <- [1..n]]
      showRow :: [String] -> String
      showRow [] = ")"
      showRow (x : xs) = x ++ " " ++ showRow xs
      blankSpace :: Int -> String
      blankSpace 0 = ""
      blankSpace n = " " ++ blankSpace (n-1)

-- Getting elements from a matrix

getElem :: Matrix a -> (Int,Int) -> a
getElem (Matrix n m arr) (i,j)
  | not (1 <= i && i <= n && 1 <= j && j <= m) = error "getElem: Index out of range"
  | otherwise = arr A.! (i,j)

(!) :: Matrix a -> (Int,Int) -> a
(!) = getElem

getRow :: Int -> Matrix a -> [a]
getRow i m
  | not (1 <= i && i <= nrows m) = error "getRow: Index out of range"
  | otherwise = [m ! (i,j) | j <- [1..ncols m]]

getColumn :: Int -> Matrix a -> [a]
getColumn j m
  | not (1 <= j && j <= ncols m) = error "getRow: Index out of range"
  | otherwise = [m ! (i,j) | i <- [1..nrows m]]

-- Transpose

transpose :: Matrix a -> Matrix a
transpose m = matrix (ncols m) (nrows m) (\(i,j) -> m ! (j,i))

-- SubMatrix

subMatrix :: (Int,Int) -> (Int,Int) -> Matrix a -> Matrix a
subMatrix (i1,i2) (j1,j2) m = matrix (i2 - i1 + 1) (j2 - j1 + 1) aux
  where
    aux (i,j) = m ! (i+i1-1,j+j1-1)


-- Some Matrix Constructors

matrix :: Int -> Int -> ((Int,Int) -> a) -> Matrix a
matrix n m f = Matrix n m $ array ((1,1),(n,m)) [((i,j), f (i,j)) | i <- [1..n], j <- [1..m]]

identity :: (Ring a, Eq a) => Int -> Int -> Matrix a
identity n m = matrix n m (\(i,j) -> if i == j then one else zero)

diagonal :: (Ring a, Eq a) => Int -> Int -> a -> Matrix a
diagonal n m elem = matrix n m (\(i,j) -> if i == j then elem else zero)

fromList :: [[a]] -> Matrix a
fromList [] = error "fromList: Empty input"
fromList xs@(x : xs') = matrix (length xs) (length x) (\(i,j) -> (xs !! (i - 1)) !! (j - 1))

-- Some Matrix Operations

opElemByElem :: (a -> b -> c) -> Matrix a -> Matrix b -> Matrix c
opElemByElem f m1 m2
  | not (nrows m1 == nrows m2 && ncols m1 == nrows m2) = error "opElemByElem: This matrixes have a distinct number of rows or columns"
  | otherwise = matrix (nrows m1) (ncols m1) (\(i,j) -> f (m1 ! (i,j)) (m2 ! (i,j)))

matSum :: (Ring a) => Matrix a -> Matrix a -> Matrix a
matSum = opElemByElem (<+>)

opMul :: ([c] -> c) -> (a -> b -> c) -> Matrix a -> Matrix b -> Matrix c
opMul fsum f m1 m2
  | not (ncols m1 == nrows m2) = error "opMul: These matrixes can't be multiplied"
  | otherwise = matrix (nrows m1) (ncols m2) (\(i,j) -> fsum [f x y | (x,y) <- zip (getRow i m1) (getColumn j m2)])

matMul :: (Ring a) => Matrix a -> Matrix a -> Matrix a
matMul = opMul ringSum (<.>)

-- Matrix row elemental operations

rowPermutation :: Matrix a -> Int -> Int -> Matrix a
rowPermutation m i j
  | not (1 <= min i j && max i j <= nrows m) = error "rowPermutation: Indexes out of range"
  | otherwise = matrix (nrows m) (ncols m) aux
  where
    aux (k,l)
      | k == i = m ! (j,l)
      | k == j = m ! (i,l)
      | otherwise = m ! (k,l)

rowMul :: (Ring a) => Matrix a -> a -> Int -> Matrix a
rowMul m elem i
  | not (1 <= i && i <= nrows m) = error "rowMul: Index out of range"
  | otherwise = matrix (nrows m) (ncols m) aux
  where
    aux (k,l)
      | k == i = elem <.> (m ! (i,l))
      | otherwise = m ! (k,l)

rowSum :: (Ring a) => Matrix a -> a -> Int -> Int -> Matrix a
rowSum m elem i j
  | i == j = error "rowSum: You can't sum the same row"
  | not (1 <= min i j && max i j <= nrows m) = error "rowSum: Indexes out of range"
  | otherwise = matrix (nrows m) (ncols m) aux
  where
    aux (k,l)
      | k == j = (elem <.> (m ! (i,l))) <+> (m ! (j,l))
      | otherwise = m ! (k,l)

-- A function from making ceros above and below a position, suppose that in the
-- position there is a one, using row elemental operations

creatingZerosExcept :: (Field a) => Int -> Int -> Matrix a -> Matrix a
creatingZerosExcept i j m = foldl (\m -> \i' -> rowSum m (neg $ m ! (i',j)) i i')
                                  m
                                  (filter (\x -> x /= i) [1..nrows m])

-- Finding a pivot from a given position (so if you are in a nxm matrix looking
-- for a pivot from position (2,3) the new position must be in the (2,n) (3,m) submatrix)

findPivot :: (Field a, Eq a) => (Int,Int) -> Matrix a -> Maybe (Int,Int)
findPivot (i,j) = aux i (i,j)
  where
  aux :: (Field a, Eq a) => Int -> (Int,Int) -> Matrix a -> Maybe (Int,Int)
  aux i0 (i,j) m 
    | j > nc = Nothing
    | i > nr = aux i0 (i0,j+1) m
    | otherwise = if m ! (i,j) /= zero then Just (i,j) else aux i0 (i+1,j) m
    where
      nr = nrows m
      nc = ncols m

-- Gauss, recording in i j the position of the actual pivot and in xs the pivot used

gauss' :: (Field a, Eq a) => Int -> Int -> [(Int,Int)] -> Matrix a -> (Matrix a,[(Int,Int)])
gauss' i j xs m -- xs is a list registering the columns with pivots
  | i > nr = (m,xs)
  | j > nc = (m,xs)
  | mij == zero = case findPivot (i,j) m of
      Nothing -> (m,xs)
      Just (ip,jp) -> gauss' i jp xs $ rowPermutation m i ip
  | mij /= one = gauss' i j xs $ rowMul m (inv $ mij) i
  | otherwise = gauss' (i+1) (j+1) (xs ++ [(i,j)]) $ creatingZerosExcept i j m
  where
    nr = nrows m
    nc = ncols m
    mij = m ! (i,j)

-- Gauss to be used outside the module

gauss :: (Field a, Eq a) => Matrix a -> Matrix a
gauss m = fst (gauss' 1 1 [] m)

-- The location of the pivots

pivots :: (Field a, Eq a) => Matrix a -> [(Int,Int)]
pivots m = snd (gauss' 1 1 [] m)

-- Columns of the matrix that correspond to basic variables

basicVars :: (Field a, Eq a) => Matrix a -> [Int]
basicVars m = map snd (pivots m)

-- Columns of the matrix that correspond to free variables

freeVars :: (Field a, Eq a) => Matrix a -> [Int]
freeVars m = [1..ncols m] \\ basicVars m

-- Getting a base of the kernel of a linear transformation using gauss

kernBase :: (Field a, Eq a) => Matrix a -> [[a]]
kernBase m = [[ aux i x m | i <- [1..ncols m]] | x <- fvs ]
  where
    nr = nrows m
    nc = ncols m
    (mGaussForm,pvs) = gauss' 1 1 [] m
    bvs = map snd pvs
    fvs = [1..nc] \\ bvs
    aux i j m
      | i == j = one
      | i `elem` fvs = zero
      | otherwise = head [ neg (mGaussForm ! (l,j)) | (l,k) <- pvs, i == k]
