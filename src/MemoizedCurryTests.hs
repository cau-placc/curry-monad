{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
module MemoizedCurryTests where

import Control.Applicative ( Applicative(liftA2) )
import Control.Monad ( liftM2 )

import MemoizedCurry
    ( Curry,
      free,
      failed,
      Tuple2C(..),
      ListC(..),
      evalCurryTree,
      (?),
      unify,
      unifyL,
      set0,
      set1,
      set2,
      mkList )
import Classes ( Shareable, Sharing(share) )

-- Some basic tests. Mostly uncommented, but the results are annotated at each test

factorial :: Curry Integer -> Curry Integer
factorial mx = mx >>= \case
  0 -> return 1
  n -> liftM2 (*) (factorial (return (n - 1))) (return n)

highFac :: Curry Integer
highFac = factorial (return 50000)

-- Node (Leaf 1) (Leaf 1) is fast, second Leaf is printed immediately after the first.
testNDShare :: Curry Integer
testNDShare = let e = highFac in share e >>= \e' ->
  e' ? e'

testNDShareTwice :: Curry Integer
testNDShareTwice = do
  e <- share highFac
  e1 <- share e
  e2 <- share e
  e1 ? e2

testSomething :: Curry Integer
testSomething = let e = return 1 ? return 2 in share e >>= \e' ->
  e' ? e'

notC :: Curry Bool -> Curry Bool
notC x = x >>= \case
  True  -> return False
  False -> return True

choiceNotC :: Curry Bool -> Curry Bool
choiceNotC x = share x >>= \x' -> x' >>= \case
  True  -> notC x' ? notC x'
  False -> return True ? return False

someFC :: Curry Integer -> Curry Integer
someFC x = x >>= \case
  1 -> return 11
  2 -> return 22
  _ -> failed

choiceSomeFC :: Curry Integer -> Curry Integer
choiceSomeFC x = share x >>= \x' -> x' >>= \case
  1 -> someFC x' ? someFC x'
  2 -> return 3 ? return 4
  _ -> failed

-- unifySelf :: (Shareable Curry a, Data a) => Curry a -> Curry Bool
-- unifySelf x = share x >>= \x' -> x' =:<= x'

-- failIfUnifiable :: Data a => Curry a -> Curry a -> Curry a
-- failIfUnifiable x y = (x =:<= y) >>= \case
--   False -> x
--   True  -> failed

-- failAlways :: (Shareable Curry a, Data a) => Curry a -> Curry a
-- failAlways x = share x >>= \x' -> failIfUnifiable x' x'

testAssumption1C :: Curry Integer -> Curry Integer
testAssumption1C x = return 1 ? x

testAssumption2C :: Curry a -> Curry a -> Curry a
testAssumption2C x y = x ? y

testAssumption3C :: Curry Integer -> Curry Integer -> Curry Integer
testAssumption3C x y = (x ? y) ? (return 5 ? return 6)

testAssumption4C :: Curry Integer -> Curry Integer
testAssumption4C _ = (return 1 ? return 2) ? (return 3 ? return 4)

testAssumption1 :: Curry (ListC Integer)
testAssumption1 = set1 testAssumption1C (return 2 ? failed)
-- Node (Leaf [1,2]) (Leaf [1])

testAssumption2 :: Curry (ListC Integer)
testAssumption2 =
  set2 testAssumption2C (return 1 ? return 2) (return 3 ? return 4)
-- Node (Node (Leaf [1,3]) (Leaf [1,4])) (Node (Leaf [2,3]) (Leaf [2,4]))

testAssumption3 :: Curry (ListC Bool)
testAssumption3 = set2 testAssumption2C (return True ? return False) free
-- Node (Node (Leaf [True,False]) (Leaf [True,True]))
--      (Node (Leaf [False,False]) (Leaf [False,True]))

testAssumption4 :: Curry (ListC Bool)
testAssumption4 = set2 testAssumption2C (return True ? return False) failed
-- Node (Leaf [True]) (Leaf [False])

testAssumption5 :: Curry Integer
testAssumption5 = lengthC testAssumption4
-- Node (Leaf 1) (Leaf 1)

lengthC :: Curry (ListC a) -> Curry Integer
lengthC list = list >>= \case
  NilC       -> return 0
  ConsC _ xs -> succ <$> lengthC xs

testAssumption6 :: Curry (ListC Integer)
testAssumption6 =
  set2 testAssumption3C (return 1 ? failed) (return 3 ? return 4)
-- Node (Node (Leaf [1,3,5,6]) (Leaf [1,4,5,6]))
--      (Node (Leaf [3,5,6]) (Leaf [4,5,6]))

testAssumption7 :: Curry Bool
testAssumption7 = set1 testAssumption4C (return 1) >>= \case
  _ -> free
-- Node (Leaf False) (Leaf True)

test0a :: Curry (Tuple2C (ListC Bool) Bool)
test0a = let x' = return True ? return False in share x' >>= \x ->
  return (Tuple2C (set1 notC x) x)
-- Node (Leaf ([False],True)) (Leaf ([True],False))

failOnFalse :: Curry Bool -> Curry Bool
failOnFalse mb = share mb >>= \mb' -> mb' >>= \case
  True  -> mb'
  False -> failed

test0b :: Curry (Tuple2C (ListC Bool) Bool)
test0b = let x' = return True ? return False in share x' >>= \x ->
  return (Tuple2C (set1 failOnFalse x) x)
-- Node (Leaf ([True],True)) (Leaf ([],False))

constFail :: Curry Bool -> Curry Bool
constFail x = x >>= \case
  True  -> failed
  False -> failed

test0c :: Curry (Tuple2C (ListC Bool) Bool)
test0c = let x' = return True ? return False in share x' >>= \x ->
  return (Tuple2C (set1 constFail x) x)
-- Node (Leaf ([],True)) (Leaf ([],False))

weird :: Curry Bool -> Curry Bool
weird x = failed ? (x >>= \case
  True  -> failed
  False -> failed)

weird2 :: Curry Bool -> Curry Bool
weird2 x = (x >>= \case
  True  -> failed
  False -> failed) ? failed

test0d :: Curry (Tuple2C (ListC Bool) Bool)
test0d = let x' = return True ? return False in share x' >>= \x ->
  return (Tuple2C (set1 weird x) x)
-- Node (Leaf ([],True)) (Leaf ([],False))

test0e :: Curry (Tuple2C (ListC Bool) Bool)
test0e = let x' = return True ? return False in share x' >>= \x ->
  return (Tuple2C (set1 weird2 x) x)
-- Node (Leaf ([],True)) (Leaf ([],False))

weird3 :: Curry Bool -> Curry Bool
weird3 x = share x >>= \x' -> (x' >>= \case
  True  -> failed
  False -> failed) ? (x' >>= \case
  True  -> failed
  False -> failed)

test0f :: Curry (Tuple2C (ListC Bool) Bool)
test0f = let x' = return True ? return False in share x' >>= \x ->
  return (Tuple2C (set1 weird3 x) x)
-- Node (Leaf ([],True)) (Leaf ([],False))

someChoiceVal :: Curry (Tuple2C Bool Bool)
someChoiceVal =
  let x = return True ? return False
  in share x >>= \x' -> return (Tuple2C x' x')

test0g :: Curry (Tuple2C (ListC Bool) Bool)
test0g = let x' = free in share x' >>= \x ->
  return (Tuple2C (set1 weird3 x) x)
-- Node (Leaf ([],False)) (Leaf ([],True))

weird4 :: Curry (Tuple2C Bool Bool) -> Curry (Tuple2C Bool Bool)
weird4 x = (x >>= \case
  Tuple2C a _  -> a >>= \case
    True  -> failed
    False -> failed) ? (x >>= \case
  Tuple2C a _  -> a >>= \case
    True  -> failed
    False -> failed)

test0h :: Curry (Tuple2C (ListC (Tuple2C Bool Bool)) (Tuple2C Bool Bool))
test0h = let x' = someChoiceVal in share x' >>= \x ->
  return (Tuple2C (set1 weird4 x) x)
-- Node (Leaf ([],(True, True))) (Leaf ([],(False, False)))

weird5 :: Curry (Tuple2C Bool Bool) -> Curry (Tuple2C Bool Bool)
weird5 x = (x >>= \case
  Tuple2C a b  -> a >>= \case
    True  -> b >>= \case
      True -> failed
      False -> failed
    False -> b >>= \case
      True -> failed
      False -> failed) ? (x >>= \case
  Tuple2C a b  -> a >>= \case
    True  -> b >>= \case
      True -> failed
      False -> failed
    False -> b >>= \case
      True -> failed
      False -> failed)

test0i :: Curry (Tuple2C (ListC (Tuple2C Bool Bool)) (Tuple2C Bool Bool))
test0i = let x' = someChoiceVal in share x' >>= \x ->
  return (Tuple2C (set1 weird5 x) x)
-- Node (Leaf ([],(True, True))) (Leaf ([],(False, False)))

weird6 :: Curry Bool -> Curry Integer
weird6 x = share x >>= \x' -> (x' >>= \case
  True  -> return 1
  False -> return 2) ? (x' >>= \case
  True  -> return 3
  False -> return 4)

test0j :: Curry (Tuple2C (ListC Integer) Bool)
test0j = let x' = return True ? return False in share x' >>= \x ->
  return (Tuple2C (set1 weird6 x) x)
-- Node (Leaf ([1,3],True)) (Leaf ([2,4],False))

test0k :: Curry (Tuple2C (ListC Integer) Bool)
test0k = let x' = free in share x' >>= \x ->
  return (Tuple2C (set1 weird6 x) x)
-- Node (Leaf ([2,4],False)) (Leaf ([1,3],True))

test1 :: Curry (ListC Bool)
test1 = set1 choiceNotC (return True ? return False)
-- Node (Leaf [False,False]) (Leaf [True,False])

test2 :: Curry (ListC Bool)
test2 = set1 choiceNotC (return True)
-- Leaf [False,False]

test3 :: Curry (ListC Integer)
test3 = set1 choiceSomeFC (return 1 ? return 2)
-- Node (Leaf [11,11]) (Leaf [3,4])

test4 :: Curry (ListC Integer)
test4 = set1 choiceSomeFC (return 1)
-- Leaf [11,11]

test5 :: Curry (ListC Integer)
test5 = set1 choiceSomeFC failed
-- Empty

test6 :: Curry (ListC Bool)
test6 = set1 choiceNotC free
-- Node (Leaf [True,False]) (Leaf [False,False])
-- Result correct, but variable is narrowed instead of captured
-- This is probably correct behaviour though

--------------------------------------------------------------------------------
-- Synthesizing Set Functions examples
--------------------------------------------------------------------------------

ndconst :: Curry Integer -> Curry a -> Curry Integer
ndconst x _ = x ? return 1

test7a :: Curry (ListC Integer)
test7a = set2 ndconst (return 2) (failed :: Curry Integer)
-- Leaf [2,1]

test7b :: Curry (ListC Integer)
test7b = set2 ndconst (return 2 ? return 4) (failed :: Curry Integer)
-- Node (Leaf [2,1]) (Leaf [4,1])

anyOf :: Curry (ListC a) -> Curry a
anyOf arg = arg >>= \case
  NilC       -> failed
  ConsC x xs -> x ? anyOf xs

test8 :: Curry (ListC Integer)
test8 = set1 anyOf (return (mkList [return 0 ? return 1, return 2, return 3]))
-- Node (Leaf [0,2,3]) (Leaf [1,2,3])

nullC :: Curry (ListC a) -> Curry Bool
nullC xs = xs >>= \case
  NilC -> return True
  ConsC _ _-> return False

test9 :: Curry (ListC Bool)
test9 = set1 nullC (return (mkList [failed :: Curry Integer]))
-- Leaf [False]

--------------------------------------------------------------------------------
-- other stuff
--------------------------------------------------------------------------------

notPlural :: Curry Bool -> Curry Bool
notPlural b = b >>= \case
  True -> return False
  False -> return True

notSa :: Curry Bool -> Curry (ListC Bool)
notSa = set1 notPlural

notSb :: Curry (ListC Bool)
notSb = set1 notPlural (return False ? failed)

test10a :: Curry (ListC (ListC Bool))
test10a = set1 notSa (return False ? failed)
-- Node (Leaf [[True]]) Empty

test10b :: Curry (ListC (ListC Bool))
test10b = set0 notSb
-- Node (Leaf [[True]]) Empty

--------------------------------------------------------------------------------
-- XML for neste set functions
--------------------------------------------------------------------------------

type DocC = ListC EntryC
type EntryC = ListC AttrC
type AttrC = Tuple2C Integer Integer

michael :: Curry EntryC
michael = return (mkList [return (Tuple2C (return 0) (return 1)), return (Tuple2C (return 1) (return 2))])

finn :: Curry EntryC
finn = return (mkList [return (Tuple2C (return 0) (return 2)), return (Tuple2C (return 1) (return 2)), return (Tuple2C (return 1) (return 2))])

sandra :: Curry EntryC
sandra = return (mkList [return (Tuple2C (return 0) (return 3))])

testDoc :: Curry DocC
testDoc = return (mkList [michael, finn, sandra])

lookupC :: Shareable Curry a
        => (Curry a -> Curry a -> Curry Bool)
        -> Curry a -> Curry (ListC (Tuple2C a b)) -> Curry b
lookupC eq sk xs = share sk >>= \k -> xs >>= \case
  NilC -> failed
  ConsC x xs' -> x >>= \case
    Tuple2C k' v -> k `eq` k' >>= \case
      True  -> v
      False -> lookupC eq k xs'

nameOfC :: Curry EntryC -> Curry Integer
nameOfC = lookupC (liftA2 (==)) (return 0)

mailOf :: Curry EntryC -> Curry Integer
mailOf = lookupC (liftA2 (==)) (return 1)

getMailsC :: Curry DocC -> Curry (Tuple2C Integer Integer)
getMailsC d = let e = anyOf d in share e >>= \e' ->
  return (Tuple2C (nameOfC e') (lengthC $ set1 mailOf e'))

getPersonsC :: Curry DocC -> Curry (ListC (Tuple2C Integer Integer))
getPersonsC = set1 getMailsC

test11 :: Curry (ListC (Tuple2C Integer Integer))
test11 = getPersonsC testDoc
-- Leaf [(1,1),(2,1),(3,0)]

--------------------------------------------------------------------------------
-- Unify
--------------------------------------------------------------------------------

test12 :: Curry Bool
test12 = return (mkList [return True]) `unify` return (mkList [failed])
-- Empty

lastC :: Curry (ListC Bool) -> Curry Bool
lastC xs = do
  let var1 = free
  var2 <- share free
  b <- appendC var1 (return (ConsC var2 (return NilC))) `unifyL` xs
  if b
    then var2
    else failed

appendC :: Curry (ListC a) -> Curry (ListC a) -> Curry (ListC a)
appendC xs' ys = xs' >>= \case
  NilC       -> ys
  ConsC x xs -> return (ConsC x (appendC xs ys))

test13a :: Curry Bool
test13a = lastC (return (mkList []))
-- Node Empty Empty

test13b :: Curry Bool
test13b = lastC (return (mkList [return True]))
-- Node (Leaf True) (Node Empty Empty)

test13c :: Curry Bool
test13c = lastC (return (mkList [failed]))
-- Node Empty (Node Empty Empty)

test13d :: Curry Bool
test13d = lastC (return (mkList [failed, return True]))
-- Node Empty (Node (Leaf True) (Node Empty Empty))

test13e :: Curry Bool
test13e = lastC (return (mkList [failed, return True ? return False]))
-- Node Empty (Node (Node (Leaf True) (Leaf False)) (Node Empty Empty))

test13f :: Curry Bool
test13f = lastC (return (mkList [return True ? return False, return True ? return False]))
-- Node Empty (Node (Node (Leaf True) (Leaf False)) (Node Empty Empty))

test13g :: Curry Bool
test13g = lastC (return (mkList [return True ? return False, return True]))
-- Node Empty (Node (Leaf True) (Node Empty Empty))

test14a :: Curry (Tuple2C Bool Bool)
test14a = do
  x <- share free
  b <- x `unifyL` (return True ? return False)
  if b
    then return (Tuple2C x x)
    else failed
-- Node (Leaf (True,True)) (Leaf (False,False))

test14b :: Curry (Tuple2C Bool Bool)
test14b = do
  x <- share free
  _ <- x `unifyL` failed
  return (Tuple2C x x)
-- Empty

test14c :: Curry Integer
test14c = do
  x <- share free
  _ <- x `unifyL` (return True ? return False)
  return 1
-- Leaf 1

appendInv :: Curry (ListC Bool) -> Curry (Tuple2C (ListC Bool) (ListC Bool))
appendInv xs = do
  var1 <- share free
  var2 <- share free
  _ <- appendC var1 var2 `unify` xs
  return (Tuple2C var1 var2)

appendInvT :: Curry (ListC Bool) -> Curry Bool
appendInvT xs = do
  var1 <- share free
  var2 <- share free
  _ <- appendC var1 var2 `unify` xs
  return True

test15a :: Curry (Tuple2C (ListC Bool) (ListC Bool))
test15a = appendInv (return (mkList []))
-- Node (Leaf ([],[])) Empty

-- TODO: inversion dinger kaputt

test15b :: Curry (Tuple2C (ListC Bool) (ListC Bool))
test15b = appendInv (return (mkList [return True]))
-- Node (Leaf ([],[True])) (Node (Leaf ([True],[])) Empty)

test15c :: Curry (Tuple2C (ListC Bool) (ListC Bool))
test15c = appendInv (return (mkList [failed]))
-- Node Empty Empty

test15d :: Curry (Tuple2C (ListC Bool) (ListC Bool))
test15d = appendInv (return (mkList [return True ? return False]))
-- Node (Node (Leaf ([],[True])) (Leaf ([],[False])))
--      (Node (Node (Leaf ([True],[])) Empty) (Node (Leaf ([False],[])) Empty))

test15e :: Curry (Tuple2C (ListC Bool) (ListC Bool))
test15e = appendInv (return (mkList [return True, return False]))
-- Node (Leaf ([],[True,False]))
--      (Node (Leaf ([True],[False]))
--            (Node (Leaf ([True,False],[])) Empty))

test15f :: Curry (Tuple2C (ListC Bool) (ListC Bool))
test15f = share (return False ? return True) >>= \x ->
  appendInv (return (mkList [x, return True, x]))
-- Node (Node (Leaf ([],[False,True,False]))
--            (Leaf ([],[True,True,True])))
--      (Node (Node (Leaf ([False],[True,False]))
--                  (Node (Leaf ([False,True],[False]))
--                        (Node (Leaf ([False,True,False],[])) Empty)))
--            (Node (Leaf ([True],[True,True]))
--                  (Node (Leaf ([True,True],[True]))
--                        (Node (Leaf ([True,True,True],[])) Empty))))

appendInvLazy :: Curry (ListC Bool) -> Curry (Tuple2C (ListC Bool) (ListC Bool))
appendInvLazy xs = do
  var1 <- share free
  var2 <- share free
  _ <- appendC var1 var2 `unifyL` xs
  return (Tuple2C var1 var2)

test16a :: Curry (Tuple2C (ListC Bool) (ListC Bool))
test16a = appendInvLazy (return (mkList []))
-- Node (Leaf ([],[])) Empty

test16b :: Curry (Tuple2C (ListC Bool) (ListC Bool))
test16b = appendInvLazy (return (mkList [return True]))
-- Node (Leaf ([],[True])) (Node (Leaf ([True],[])) Empty)

test16c :: Curry (Tuple2C (ListC Bool) (ListC Bool))
test16c = appendInvLazy (return (mkList [failed]))
-- Node Empty (Node Empty Empty)

test16d :: Curry (Tuple2C (ListC Bool) (ListC Bool))
test16d = appendInvLazy (return (mkList [return True ? return False]))
-- Node (Node (Leaf ([],[True])) (Leaf ([],[False])))
--      (Node (Node (Leaf ([True],[])) (Leaf ([False],[])))
--            Empty)

test16e :: Curry (Tuple2C (ListC Bool) (ListC Bool))
test16e = appendInvLazy (return (mkList [return True, return False]))
-- Node (Leaf ([],[True,False]))
--      (Node (Leaf ([True],[False]))
--            (Node (Leaf ([True,False],[])) Empty))

test16f :: Curry (Tuple2C (ListC Bool) (ListC Bool))
test16f = share (return False ? return True) >>= \x ->
  appendInvLazy (return (mkList [x, return True, x]))
-- Node (Node (Leaf ([],[False,True,False]))
--            (Leaf ([],[True,True,True])))
--      (Node (Node (Leaf ([False],[True,False]))
--                  (Leaf ([True],[True,True])))
--            (Node (Node (Leaf ([False,True],[False]))
--                        (Leaf ([True,True],[True])))
--                  (Node (Node (Leaf ([False,True,False],[]))
--                              (Leaf ([True,True,True],[])))
--                        Empty)))

test16g :: Curry (Tuple2C Integer Integer)
test16g = appendInvLazy (return (mkList [failed])) >>=
  \(Tuple2C a b) -> return (Tuple2C (lengthC a) (lengthC b))
-- Node (Leaf (0,1)) (Node (Leaf (1,0)) Empty)

test17 :: Curry (ListC Bool)
test17 = do
  x <- share (return False ? return True)
  v1 <- share free
  v2 <- share free
  _ <- return (mkList [v1, v2]) `unifyL` return (mkList [x, x])
  return (mkList [v1, v2])
-- Node (Leaf [False,False]) (Leaf [True,True])

takeC :: Curry Int -> Curry (ListC a) -> Curry (ListC a)
takeC n xs = n >>= \case
  0  -> return NilC
  n' -> xs >>= \case
    NilC       -> return NilC
    ConsC y ys -> return (ConsC y (takeC (return (pred n')) ys))

(??) :: Shareable Curry a => Curry a -> Curry a
(??) x' = share x' >>= \x -> x ? x

-- let x' = False ?x True in share x' >>= \x -> set2 ?? x x
-- (False <3?x4> True) <1??2> (False ?x True) -- 0 -> False ?id_1 True
-- [False ?x True, False ?x True]
-- ([False, False ?x True]) ?x ([True, False ?x True])
-- ([False, False]) ?x ([True, True])

-- let x' = False ?x True in share x' >>= \x -> x ? x
-- (False ?x True) ? (False ?x True)


test18 :: Curry (ListC Integer)
test18 = takeC (return 10) (set0 (free :: Curry Integer))
-- Leaf [0,-1,-2,1,-3,-4,-5,2,3,4]

--------------------------------------------------------------------------------
-- Double sharing
--------------------------------------------------------------------------------

test19 :: Curry (Tuple2C Bool Bool)
test19 = do
  x <- share (return True ? return False)
  x1 <- share x
  x2 <- share x
  return (Tuple2C x1 x2)
-- Node (Leaf (True,True)) (Leaf (False,False))

testAll :: IO ()
testAll = do
    putStrLn "testAssumption1"
    print (evalCurryTree testAssumption1)
    putStrLn ""
    putStrLn "testAssumption2"
    print (evalCurryTree testAssumption2)
    putStrLn ""
    putStrLn "testAssumption3"
    print (evalCurryTree testAssumption3)
    putStrLn ""
    putStrLn "testAssumption4"
    print (evalCurryTree testAssumption4)
    putStrLn ""
    putStrLn "testAssumption5"
    print (evalCurryTree testAssumption5)
    putStrLn ""
    putStrLn "testAssumption6"
    print (evalCurryTree testAssumption6)
    putStrLn ""
    putStrLn "testAssumption7"
    print (evalCurryTree testAssumption7)
    putStrLn ""

    putStrLn "test0a"
    print (evalCurryTree test0a)
    putStrLn ""
    putStrLn "test0b"
    print (evalCurryTree test0b)
    putStrLn ""
    putStrLn "test0c"
    print (evalCurryTree test0c)
    putStrLn ""
    putStrLn "test0d"
    print (evalCurryTree test0d)
    putStrLn ""
    putStrLn "test0e"
    print (evalCurryTree test0e)
    putStrLn ""
    putStrLn "test0f"
    print (evalCurryTree test0f)
    putStrLn ""
    putStrLn "test0g"
    print (evalCurryTree test0g)
    putStrLn ""
    putStrLn "test0h"
    print (evalCurryTree test0h)
    putStrLn ""
    putStrLn "test0i"
    print (evalCurryTree test0i)
    putStrLn ""
    putStrLn "test0j"
    print (evalCurryTree test0j)
    putStrLn ""
    putStrLn "test0k"
    print (evalCurryTree test0k)
    putStrLn ""
    putStrLn "test1"
    print (evalCurryTree test1)
    putStrLn ""
    putStrLn "test2"
    print (evalCurryTree test2)
    putStrLn ""
    putStrLn "test3"
    print (evalCurryTree test3)
    putStrLn ""
    putStrLn "test4"
    print (evalCurryTree test4)
    putStrLn ""
    putStrLn "test5"
    print (evalCurryTree test5)
    putStrLn ""
    putStrLn "test6"
    print (evalCurryTree test6)
    putStrLn ""

    putStrLn "test7a"
    print (evalCurryTree test7a)
    putStrLn ""
    putStrLn "test7b"
    print (evalCurryTree test7b)
    putStrLn ""
    putStrLn "test8"
    print (evalCurryTree test8)
    putStrLn ""
    putStrLn "test9"
    print (evalCurryTree test9)
    putStrLn ""
    putStrLn "test10a"
    print (evalCurryTree test10a)
    putStrLn ""
    putStrLn "test10b"
    print (evalCurryTree test10b)
    putStrLn ""
    putStrLn "test11"
    print (evalCurryTree test11)
    putStrLn ""

    putStrLn "test12"
    print (evalCurryTree test12)
    putStrLn ""
    putStrLn "test13a"
    print (evalCurryTree test13a)
    putStrLn ""
    putStrLn "test13b"
    print (evalCurryTree test13b)
    putStrLn ""
    putStrLn "test13c"
    print (evalCurryTree test13c)
    putStrLn ""
    putStrLn "test13d"
    print (evalCurryTree test13d)
    putStrLn ""
    putStrLn "test13e"
    print (evalCurryTree test13e)
    putStrLn ""
    putStrLn "test13f"
    print (evalCurryTree test13f)
    putStrLn ""
    putStrLn "test13g"
    print (evalCurryTree test13g)
    putStrLn ""
    putStrLn "test14a"
    print (evalCurryTree test14a)
    putStrLn ""
    putStrLn "test14b"
    print (evalCurryTree test14b)
    putStrLn ""
    putStrLn "test14c"
    print (evalCurryTree test14c)
    putStrLn ""

    putStrLn "test15a"
    print (evalCurryTree test15a)
    putStrLn ""
    putStrLn "test15b"
    print (evalCurryTree test15b)
    putStrLn ""
    putStrLn "test15c"
    print (evalCurryTree test15c)
    putStrLn ""
    putStrLn "test15d"
    print (evalCurryTree test15d)
    putStrLn ""
    putStrLn "test15e"
    print (evalCurryTree test15e)
    putStrLn ""
    putStrLn "test15f"
    print (evalCurryTree test15f)
    putStrLn ""
    putStrLn "test16a"
    print (evalCurryTree test16a)
    putStrLn ""
    putStrLn "test16b"
    print (evalCurryTree test16b)
    putStrLn ""
    putStrLn "test16c"
    print (evalCurryTree test16c)
    putStrLn ""
    putStrLn "test16d"
    print (evalCurryTree test16d)
    putStrLn ""
    putStrLn "test16e"
    print (evalCurryTree test16e)
    putStrLn ""
    putStrLn "test16f"
    print (evalCurryTree test16f)
    putStrLn ""
    putStrLn "test16g"
    print (evalCurryTree test16g)
    putStrLn ""

    putStrLn "test17"
    print (evalCurryTree test17)
    putStrLn ""
    putStrLn "test18"
    print (evalCurryTree test18)
    putStrLn ""
    putStrLn "test19"
    print (evalCurryTree test19)
    putStrLn ""
