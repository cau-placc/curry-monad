{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE EmptyCase         #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
module Narrowable where

import GHC.Generics
    ( Generic(..),
      V1,
      U1(..),
      K1(K1),
      M1(M1),
      type (:+:)(..),
      type (:*:)(..) )

import Classes ( Shareable )
import HasPrimitiveInfo ( HasPrimitiveInfo )
import {-# SOURCE #-} MemoizedCurry ( Curry, free )

-- Narrowable class and methods.
-- We use Generics to give a default implementation for this class.
-- That way, we can automatically derive instances.

class Narrowable a where
  narrow :: [a]
  default narrow :: (Generic a, NarrowableGen (Rep a)) => [a]
  narrow = map to narrowGen

  narrowConstr :: a -> a
  default narrowConstr :: (Generic a, NarrowableGen (Rep a)) => a -> a
  narrowConstr a = to (narrowConstrGen (from a))

-- Beyond here, the machinery for the default implementation is defined.
-- There are some tutorials on the internet about GHC's generic types and how to use them to
-- derive instances of different classes.

class NarrowableGen f where
  narrowGen :: [f x]
  narrowConstrGen :: f x -> f x

instance NarrowableGen V1 where
  narrowGen = []
  narrowConstrGen x = case x of

instance NarrowableGen U1 where
  narrowGen = [U1]
  narrowConstrGen U1 = U1

instance (NarrowableGen f, NarrowableGen g) => NarrowableGen (f :+: g) where
  narrowGen = map L1 narrowGen ++ map R1 narrowGen

  narrowConstrGen (L1 x) = L1 (narrowConstrGen x)
  narrowConstrGen (R1 x) = R1 (narrowConstrGen x)

instance (NarrowableGen f, NarrowableGen g) => NarrowableGen (f :*: g) where
  narrowGen = concatMap (\x -> map (x :*:) narrowGen) narrowGen

  narrowConstrGen (x :*: y) = narrowConstrGen x :*: narrowConstrGen y

instance NarrowableGen f => NarrowableGen (M1 j h f) where
  narrowGen = map M1 narrowGen
  narrowConstrGen (M1 x) = M1 (narrowConstrGen x)

instance (Shareable Curry a, HasPrimitiveInfo a) => NarrowableGen (K1 i (Curry a)) where
  narrowGen = [K1 free]

  narrowConstrGen (K1 _) = K1 free

-- implementation is generated automatically.
instance Narrowable Bool
