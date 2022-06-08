{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
module NormalForm where

import GHC.Generics
    ( Generic(..),
      V1,
      U1(..),
      K1(K1),
      M1(M1),
      type (:+:)(..),
      type (:*:)(..) )

import {-# SOURCE #-} MemoizedCurry (Curry, failed)

-- Class to pull all non-determinisim to the top
class NormalForm a where
  nfWith :: (forall x. NormalForm x => Curry x -> Curry x) -> a -> Curry a
  default nfWith :: (Generic a, NormalFormGen (Rep a))
                 => (forall x. NormalForm x => Curry x -> Curry x)
                 -> a -> Curry a
  nfWith f = fmap to . nfWithGen f . from

class NormalFormGen f where
  nfWithGen :: (forall x. NormalForm x => Curry x -> Curry x)
            -> f z -> Curry (f z)

instance NormalFormGen V1 where
  nfWithGen _ _ = failed

instance NormalFormGen U1 where
  nfWithGen _ U1 = return U1

instance (NormalFormGen f, NormalFormGen g) => NormalFormGen (f :+: g) where
  nfWithGen f (L1 x) = L1 <$> nfWithGen f x
  nfWithGen f (R1 y) = R1 <$> nfWithGen f y

instance (NormalFormGen f, NormalFormGen g) => NormalFormGen (f :*: g) where
  nfWithGen f (x :*: y) = nfWithGen f x >>= \x' -> nfWithGen f y >>= \y' ->
    return (x' :*: y')

instance NormalFormGen f => NormalFormGen (M1 a b f) where
  nfWithGen f (M1 x) = M1 <$> nfWithGen f x

instance NormalForm f => NormalFormGen (K1 a (Curry f)) where
  nfWithGen f (K1 x) = f x >>= \x' -> return (K1 (return x'))

instance NormalForm Integer where
  nfWith _ !x = return x

instance NormalForm Bool where
  nfWith _ True  = return True
  nfWith _ False = return False
