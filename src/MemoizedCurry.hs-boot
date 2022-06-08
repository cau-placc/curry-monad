{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE RoleAnnotations          #-}
{-# LANGUAGE StandaloneKindSignatures #-}
module MemoizedCurry where

import Data.Kind

import HasPrimitiveInfo (HasPrimitiveInfo)
import Classes

type Curry :: Type -> Type
type role Curry nominal
data Curry a

instance Functor Curry

instance Applicative Curry

instance Monad Curry

failed :: Curry a

free :: (HasPrimitiveInfo a, Shareable Curry a) => Curry a
