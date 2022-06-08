{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE FlexibleContexts #-}
module MemoizedCurryBench where

import Control.Monad ( liftM2 )
import Data.Functor ( (<&>) )
import Criterion.Main
    ( bench, bgroup, nf, defaultConfig, defaultMainWith )
import Criterion.Types ( Config(resamples) )

import MemoizedCurry
    ( Curry,
      failed,
      NormalForm,
      ListC(..),
      Tree(Single),
      evalCurry,
      evalCurryTree,
      (?),
      mkList )
import MemoizedCurryTests ( lengthC, anyOf, appendC )
import Tree ( dfs, bfs )
import Classes (share, Shareable)

-- some benchmarks we used before we had the plugin.

insertC :: Shareable Curry a => Curry a -> Curry (ListC a) -> Curry (ListC a)
insertC x xs = xs >>= \case
  NilC         -> return (ConsC x (return NilC))
  ConsC y' ys' -> share y' >>= \y -> share ys' >>= \ys ->
                    return (ConsC x (return (ConsC y ys))) ?
                    return (ConsC y (insertC x ys))

permsC :: Shareable Curry a => Curry (ListC a) -> Curry (ListC a)
permsC xs = xs >>= \case
  NilC       -> return NilC
  ConsC y ys -> insertC y (permsC ys)

isSorted :: (Shareable Curry a, Ord a) => Curry (ListC a) -> Curry (ListC a)
isSorted xs = xs >>= \case
  NilC       -> return NilC
  ConsC y' ys -> share y' >>= \y -> ys >>= \case
    NilC       -> return (ConsC y (return NilC))
    ConsC z' zs -> share z' >>= \z -> liftM2 (<=) y z >>= \case
      True  -> return (ConsC y (isSorted (return (ConsC z zs))))
      False -> failed

permsort :: (Shareable Curry a, Ord a) => Curry (ListC a) -> Curry (ListC a)
permsort = isSorted . permsC

mkIntegerList :: [Integer] -> Curry (ListC Integer)
mkIntegerList = return . mkList . map return

perm4 :: Curry (ListC Integer)
perm4 = permsort $ mkIntegerList [2,4,3,1]

perm12 :: Curry (ListC Integer)
perm12 = permsort $ mkIntegerList [2,12,11,10,9,8,7,6,5,3,1]

perm13 :: Curry (ListC Integer)
perm13 = permsort $ mkIntegerList [2,13,12,11,10,9,8,7,6,5,4,3,1]

perm14 :: Curry (ListC Integer)
perm14 = permsort $ mkIntegerList [2,14,13,12,11,10,9,8,7,6,5,4,3,1]

-- arbitrary number between 1 and n:
someNum :: Curry Integer -> Curry Integer
someNum n' = n' >>= \case
  n | n <= 0    -> return 0
    | otherwise -> return n ? someNum (return (n-1))

add :: Curry Integer -> Curry Integer -> Curry Integer
add x y = x >>= \x' -> y >>= \y' -> return (x' + y')

addSomeNum5 :: Curry Integer -> Curry Integer
addSomeNum5 n = let x' = someNum n in share x' >>= \x ->
  x `add` x `add` x `add` x `add` x `add` x

addSomeNum10 :: Curry Integer -> Curry Integer
addSomeNum10 n = let x' = someNum n in share x' >>= \x ->
  x `add` x `add` x `add` x `add` x `add` x `add`
  x `add` x `add` x `add` x `add` x `add` x

isZero :: Curry Integer -> Curry Bool
isZero n = n <&> (==0)

addNum_5 :: Curry Bool
addNum_5 = isZero (addSomeNum5 (return 2000))

addNum_10 :: Curry Bool
addNum_10 = isZero (addSomeNum10 (return 2000))

transList :: NormalForm a => ListC a -> [a]
transList NilC         = []
transList (ConsC x xs) = case (evalCurry x, evalCurry xs) of
  (Single x', Single xs') -> x' : transList xs'
  _                       -> error "Not in normal form"

del :: (Shareable Curry a, Eq a)
    => Curry a -> Curry (ListC a) -> Curry (ListC a)
del x xs = xs >>= \case
  NilC       -> failed
  ConsC y ys -> share ys >>= \sys -> share y >>= \sy -> share x >>= \sx ->
    sx >>= \x' -> sy >>= \y' ->
    if x' == y' then sys else return (ConsC sy (del sx sys))

sumC :: Curry (ListC Integer) -> Curry Integer
sumC xs = xs >>= \case
  NilC       -> return 0
  ConsC y ys -> liftM2 (+) y (sumC ys)

sumUp :: Curry (ListC Integer) -> Curry Integer -> Curry Integer
sumUp xs m' = share m' >>= \m -> liftM2 (+) m (sumC (del m xs))

select :: Curry (ListC Integer) -> Curry Integer
select xs = sumUp xs (anyOf xs)

select_50 :: Curry Integer
select_50 = select (return $ mkList $ map return [1..50])

select_150 :: Curry Integer
select_150 = select (return $ mkList $ map return [1..150])

queens :: Curry Integer -> Curry Integer
queens nq = lengthC (gen nq)
 where
  gen :: Curry Integer -> Curry (ListC (ListC Integer))
  gen n = n >>= \n' ->
    if n'==0
      then return (ConsC (return NilC) (return NilC))
      else concatMapC (\b -> concatMapC (\q -> safe q (return 1) b >>= \case
              True  -> return (ConsC (return (ConsC q b)) (return NilC))
              False -> return NilC)
                                        (fromToC (return 1) nq))
                      (gen (return (n'-1)))

fromToC :: Curry Integer -> Curry Integer -> Curry (ListC Integer)
fromToC x y = x >>= \x' -> y >>= \y' -> return (mkList $ map return [x'..y'])

mapC :: (Curry a -> Curry b) -> Curry (ListC a) -> Curry (ListC b)
mapC f xs = xs >>= \case
  NilC       -> return NilC
  ConsC y ys -> return (ConsC (f y) (mapC f ys))

concatMapC :: (Curry a -> Curry (ListC b)) -> Curry (ListC a) -> Curry (ListC b)
concatMapC f xs = xs >>= \case
  NilC       -> return NilC
  ConsC y ys -> appendC (f y) (concatMapC f ys)

safe :: Curry Integer -> Curry Integer -> Curry (ListC Integer) -> Curry Bool
safe x d xs = xs >>= \case
  NilC      -> return True
  ConsC q l ->
    andC (andC (liftM2 (/=) x q)
               (liftM2 (/=) x (q `add` d)))
         (andC (liftM2 (/=) x (q `add` (negate <$> d)))
               (safe x (d `add` return 1) l))

safeS :: Curry Integer -> Curry Integer -> Curry (ListC Integer) -> Curry Bool
safeS x d xs = share x >>= \x' -> share d >>= \d' -> xs >>= \case
  NilC      -> return True
  ConsC q l -> share q >>= \q' ->
    andC (andC (liftM2 (/=) x' q')
               (liftM2 (/=) x' (q' `add` d')))
         (andC (liftM2 (/=) x' (q' `add` (negate <$> d')))
               (safe x' (d' `add` return 1) l))

andC :: Curry Bool -> Curry Bool -> Curry Bool
andC x y = x >>= \case
  False -> return False
  True  -> y

queens_5, queens_6, queens_7, queens_8, queens_10, queens_11 :: Curry Integer
queens_5 = queens (return 5)
queens_6 = queens (return 6)
queens_7 = queens (return 7)
queens_8 = queens (return 8)
queens_10 = queens (return 10)
queens_11 = queens (return 11)

primes :: Curry (ListC Integer)
primes = mapC headC (iterateC sieve (iterateC succC (return 2)))

headC :: Curry (ListC a) -> Curry a
headC xs = xs >>= \case
  NilC      -> failed
  ConsC x _ -> x

iterateC :: Shareable Curry a
         => (Curry a -> Curry a) -> Curry a -> Curry (ListC a)
iterateC f x' = share x' >>= \x -> return (ConsC x (iterateC f (f x)))

succC :: Curry Integer -> Curry Integer
succC = fmap succ

sieve :: Curry (ListC Integer) -> Curry (ListC Integer)
sieve xs = xs >>= \case
  NilC       -> failed
  ConsC n ns -> filterC (isDiv n) ns

isDiv :: Curry Integer -> Curry Integer -> Curry Bool
isDiv x y = (/=0) <$> liftM2 mod y x

filterC :: Shareable Curry a
        => (Curry a -> Curry Bool) -> Curry (ListC a) -> Curry (ListC a)
filterC f xs = xs >>= \case
  NilC       -> return NilC
  ConsC y ys -> f y >>= \case
    True  -> return (ConsC y (filterC f ys))
    False -> filterC f ys

at :: Curry (ListC a) -> Curry Integer -> Curry a
at xs n = xs >>= \case
  NilC       -> failed
  ConsC y ys -> n >>= \case
    0 -> y
    x -> ys `at` return (x - 1)

primesHs :: [Integer]
primesHs = map head (iterate (\case
  []     -> error "finite iterate"
  (x:xs) -> filter (\y -> mod y x /= 0) xs) [2..])

primeList :: Curry (ListC Integer)
primeList = share primes >>= \p -> return $ mkList
  [ p `at` return 303
  , p `at` return 302
  , p `at` return 301
  , p `at` return 300]

perm_p4 :: Curry (ListC Integer)
perm_p4 = share primeList >>= permsort

main :: IO ()
main = print $ dfs $ evalCurryTree perm13

main2 :: IO ()
main2 = defaultMainWith (defaultConfig  { resamples = 20 })
  [ bgroup "select"
    [ bench "50b" $ nf (bfs . evalCurryTree) select_50
    , bench "50d" $ nf (dfs . evalCurryTree) select_50
    , bench "150b" $ nf (bfs . evalCurryTree) select_150
    , bench "150d" $ nf (dfs . evalCurryTree) select_150
    ]
  , bgroup "permsort"
    [ bench "primes4b" $ nf (transList . head . bfs . evalCurryTree) perm_p4
    , bench "primes4d" $ nf (transList . head . dfs . evalCurryTree) perm_p4
    , bench "12b"      $ nf (transList . head . bfs . evalCurryTree) perm12
    , bench "12d"      $ nf (transList . head . dfs . evalCurryTree) perm12
    , bench "13b"      $ nf (transList . head . bfs . evalCurryTree) perm13
    , bench "13d"      $ nf (transList . head . dfs . evalCurryTree) perm13
    , bench "14b"      $ nf (transList . head . bfs . evalCurryTree) perm14
    , bench "14d"      $ nf (transList . head . dfs . evalCurryTree) perm14
    ]
  , bgroup "addNum"
    [ bench "5b" $ nf (bfs . evalCurryTree) addNum_5
    , bench "5d" $ nf (dfs . evalCurryTree) addNum_5
    , bench "10b" $ nf (bfs . evalCurryTree) addNum_10
    , bench "10d" $ nf (dfs . evalCurryTree) addNum_10
    ]
  , bgroup "queens"
    [ bench "10b" $ nf (bfs . evalCurryTree) queens_10
    , bench "10d" $ nf (dfs . evalCurryTree) queens_10
    ]
  ]
