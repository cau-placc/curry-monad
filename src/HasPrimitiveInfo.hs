{-# LANGUAGE DefaultSignatures         #-}
{-# LANGUAGE ExistentialQuantification #-}
module HasPrimitiveInfo where

import Data.SBV ( SymVal )

import {-# SOURCE #-} Narrowable ( Narrowable )

-- Differentiates between primitive types (e.g., Int)
-- and non-primitive types (e.g, lists).
-- Also carries a type class constraint as an existential.
-- Depending on the type, we either need to be able to narrow it
-- or to use constraint solving with it.
data PrimitiveInfo a = Narrowable a => NoPrimitive
                     | SymVal a => Primitive

-- Class to see if a type is a primitive type (e.g., Int)
class HasPrimitiveInfo a where
  primitiveInfo :: PrimitiveInfo a
  default primitiveInfo :: (Narrowable a) => PrimitiveInfo a
  primitiveInfo = NoPrimitive

instance HasPrimitiveInfo Integer where
  primitiveInfo = Primitive

instance HasPrimitiveInfo Bool
