{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
module MemoizedCurry (module MemoizedCurry, module NormalForm, module Narrowable, module HasPrimitiveInfo) where

import qualified Data.Map                           as Map
import           Data.Map                           (Map)
import qualified Data.Set                           as Set
import           Data.Set                           (Set)
import           Data.IORef                         (IORef, modifyIORef, atomicModifyIORef', newIORef, readIORef)
import           Data.SBV                           ( SBool,
                                                      SymVal(literal),
                                                      SBV,
                                                      runSMT,
                                                      constrain,
                                                      EqSymbolic((.===), (./==)),
                                                      Uninterpreted(sym) )
import           Data.SBV.Control                   (query, checkSat, getValue, CheckSatResult(..))
import           Control.Applicative                (Alternative(..))
import           Control.Arrow                      (first)
import           Control.Monad                      (MonadPlus(..), liftM, ap)
import           Control.Monad.Codensity            (Codensity(..))
import           Control.Monad.Reader               (ReaderT(..), MonadReader(..))
import           Control.Monad.Representable.State  (MonadState(..))
import           Control.Monad.Trans                (MonadTrans(..))
import           GHC.Generics                       ( Generic(..),
                                                      V1,
                                                      U1(..),
                                                      K1(K1),
                                                      M1(M1),
                                                      type (:+:)(..),
                                                      type (:*:)(..) )
import           GHC.Magic                          (noinline)
import           GHC.IO                             ( unsafeDupableInterleaveIO,
                                                      unsafeDupablePerformIO,
                                                      unsafePerformIO )
import           Unsafe.Coerce                      (unsafeCoerce)
import           Classes                            (Sharing(..), Shareable(..))
import qualified Tree

import NormalForm
import Narrowable
import HasPrimitiveInfo

-- Changes to the paper:
-- - The performance optimization that was teasered
-- - Unification, lazy unification
-- - Set functions
-- - Constraint solving for operations on variables of primitive types
-- - Performance optimizations using `Codensity` where possible.

--------------------------------------------------------------------------------
-- Lifted function type

infixr 0 :->
newtype (:->) a b = Func (Curry a -> Curry b)

--------------------------------------------------------------------------------
-- Define a Tree that is polymorphic in the annotations at leafs and nodes.
-- Even the Fail constructor has an argument for later use.

data Tree n f l = Single l
                | Fail f
                | Choice n (Tree n f l) (Tree n f l)
  deriving (Functor, Show)

instance Applicative (Tree n f) where
  pure = Single
  Single f       <*> a = fmap f a
  Fail   lvlSt   <*> _ = Fail lvlSt
  Choice lvl l r <*> a = Choice lvl (l <*> a) (r <*> a)

instance Monad (Tree n f) where
  Single a       >>= f = f a
  Fail   lvlSt   >>= _ = Fail lvlSt
  Choice lvl l r >>= f = Choice lvl (l >>= f) (r >>= f)


-- For efficiency reasons, we will use Codensity here to get faster tree traversals.
-- We can convert freely between Search and Tree.
type Search n f = Codensity (Tree n f)

--------------------------------------------------------------------------------
-- Existential type that, so that we can later put data of arbirtrary types in the same structure.

data Untyped = forall a. Untyped a

typed :: Untyped -> a
typed (Untyped x) = unsafeCoerce x

untyped :: a -> Untyped
untyped = Untyped

--------------------------------------------------------------------------------
-- Defining the type for identifiers and
-- a function to generate a new identifier from its predecessor.

type ID = Integer

nextID :: ID -> ID
nextID = succ

--------------------------------------------------------------------------------
-- The Heap is just a map from identifiers to arbitrary values of the given type.

type Heap a = Map ID a

emptyHeap :: Heap a
emptyHeap = mempty

insertHeap :: ID -> a -> Heap a -> Heap a
insertHeap = Map.insert

lookupHeap :: ID -> Heap a -> Maybe a
lookupHeap = Map.lookup

--------------------------------------------------------------------------------
-- Our Monad also contains an extension where free variables
-- on primitive types (e.g. Numeric types) use constraint solving.
-- This improves performance for numerical operations on free variables,
-- since we can then instantiate variables less eagerly.
-- The implementation of those numerical operations is not shown in this file.
-- For a taste you could look at https://github.com/cau-placc/inversion-plugin,
-- where we did this in a different context.
-- To solve constraints, we use the SBV library,
-- which we use to check consistency of a set of constraints
-- and retrieve models that satisfy the constraints.

type Constraint = SBool

type ConstraintStore = [Constraint]

insertConstraint :: Constraint -> ConstraintStore -> ConstraintStore
insertConstraint = (:)

isConsistent :: ConstraintStore -> Bool
isConsistent cst = unsafePerformIO $ runSMT $ do
  mapM_ constrain cst
  query $ checkSat >>= \case
    Sat -> return True
    _   -> return False

toSBV :: SymVal a => CurryVal a -> SBV a
toSBV (Var _ i) = varToSBV i
toSBV (Val _ a) = literal a

varToSBV :: SymVal a => ID -> SBV a
varToSBV i = sym $ "x" ++ (if i < 0 then "n" else "") ++ show (abs i)

--------------------------------------------------------------------------------
-- Our State contains the stuff from the paper:
-- - idSupply for fresh IDs
-- - varHeap to store variable bindings
-- - branchID to distinguish branches
-- - parentIDs to see which branches this one originated from
-- Additionally, we need:
-- - the constraintStore to store constraints on primitive variables
-- - the currentLevel for set functions (see later)
-- - setComputation as a flag for set functions as well

data NDState = NDState {
    idSupply        :: IORef ID,
    currentLevel    :: Level,
    varHeap         :: Heap Untyped, -- (Var) ID -> Curry a
    constraintStore :: ConstraintStore,
    branchID        :: ID,           -- (Branch) ID
    parentIDs       :: Set ID,
    setComputation  :: Bool
  }

--------------------------------------------------------------------------------
-- Here are a few function to generate the initial state and
-- to generate new IDs in a monadic context

{-# NOINLINE initialNDState #-}
initialNDState :: () -> NDState
initialNDState () = NDState (unsafePerformIO (newIORef 1)) 0 emptyHeap mempty 0 Set.empty False

{-# NOINLINE freshIDFromState #-}
freshIDFromState :: NDState -> ID
freshIDFromState NDState { .. } = unsafePerformIO $ do
  atomicModifyIORef' idSupply (\i -> (nextID i, i))

-- {-# NOINLINE freshID #-}
-- NOINLINE not required, because freshIDFromState is the unsafe part
freshID :: MonadState NDState m => m ID
freshID = freshIDFromState <$> get

advanceNDState :: NDState -> NDState
advanceNDState s =
  let i = freshIDFromState s
      ps = Set.insert (branchID s) (parentIDs s)
  in s { branchID = i, parentIDs = ps }

--------------------------------------------------------------------------------
-- Before defining the actual memoizing curry monad, we define this intermediate monad,
-- which is basically the same as `StateT NDState (Tree Level (NDState, Level)) a`.
-- Meaning, we have a state monad withb the above state and a Tree that is annotated with:
-- - Level at Choices/Nodes (NOT Fingerprints), which are used for set functions
-- - Level and State at Failures, which are used for set functions as well.
-- We just use Codensity for performance.
-- Codensity with Reader is semantically equivalent to State.

newtype ND a = ND {
    unND :: Codensity (ReaderT NDState (Search Level (NDState, Level))) a
  } deriving newtype ( Functor, Applicative, Monad
                     , MonadState NDState, MonadReader NDState )

--------------------------------------------------------------------------------
-- Two convenience function to run an ND action to get the resulting tree.
-- The latter of these functions also gives the end state at each leaf.

evalND :: ND a -> NDState -> Tree Level (NDState, Level) a
evalND (ND a) ndState =
  runCodensity (runReaderT (runCodensity a return) ndState) return

runND :: ND a -> NDState -> Tree Level (NDState, Level) (NDState, a)
runND a = evalND (a >>= \a' -> get >>= \st -> return (st, a'))

--------------------------------------------------------------------------------
-- For later, we need a variant of the MonadPlus operations `mzero`/`mplus`,
-- which decorate the choices and failures with a specific level.
-- Thus, we indroduce these here.

-- mzero is easy, just retrieve the state so that we can decorate the failure with the state and the level,
-- afterwards the failure is lifted to the ND level.
mzeroLevel :: Level -> ND a
mzeroLevel lvl = get >>= \s -> ND $ lift $ lift $ lift $ Fail (s, lvl)

-- For mplus, we have to differentiate between two different states.
-- If we are within a computation from a set function,
-- we basically need to sequence the two computations.
-- The details will follow later when set functions are introduced.
-- The other if-branch is basically the same as in the paper, just writtern more verbose.
-- We update the parents and branch IDs an create a choice with the given level.
mplusLevel :: forall a. Level -> ND a -> ND a -> ND a
mplusLevel lvl (ND ma1) (ND ma2) = ND $ Codensity $ \c -> ReaderT $ \ndState1 ->
  Codensity $ \sc ->
    if setComputation ndState1
      then do
        let thisLvl = currentLevel ndState1
        (ndState2, a) <- augment thisLvl (runND (ND ma1) ndState1)
        runCodensity (runReaderT (c a) ndState2) sc
      else let i1 = freshIDFromState ndState1
               i2 = noinline const (freshIDFromState ndState1) i1
               ps = Set.insert (branchID ndState1) (parentIDs ndState1)
               s1 = ndState1 { branchID = i1, parentIDs = ps }
               s2 = ndState1 { branchID = i2, parentIDs = ps }
               t1 = runReaderT (runCodensity ma1 c) s1
               t2 = runReaderT (runCodensity ma2 c) s2
          in Choice lvl (runCodensity t1 sc) (runCodensity t2 sc)
  where
    augment :: Level -> Tree Level (NDState, Level) (NDState, a)
            -> Tree Level (NDState, Level) (NDState, a)
    augment thisLvl (Single (ndState, a))    =
      Choice lvl (Single (ndState, a))
                  (runND (ND ma2) (ndState { currentLevel = thisLvl }))
    augment thisLvl (Fail   (ndState, lvl')) =
      Choice lvl (Fail   (ndState, lvl'))
                  (runND (ND ma2) (ndState { currentLevel = thisLvl }))
    augment thisLvl (Choice lvl' l r)
      | lvl == lvl' =
        Choice lvl' l (augment thisLvl r)
      | otherwise   =
        Choice lvl' (augment thisLvl l) (augment thisLvl r)

msumLevel :: Level -> [ND a] -> ND a
msumLevel lvl [] = mzeroLevel lvl
msumLevel lvl xs = foldr1 (mplusLevel lvl) xs

instance Alternative ND where
  empty = get >>= \s -> mzeroLevel (currentLevel s)

  a <|> b = get >>= \s -> mplusLevel (currentLevel s) a b

instance MonadPlus ND

--------------------------------------------------------------------------------
-- In comparison to the paper, Variables  include some kind of Level type,
-- which will be shown later.
-- We also need a Shareable constraint for the type of variables.
-- Additionally, to include the performance optimization in the paper,
-- values are tagged with whether or not they have been shared already.

data CurryVal a = Val ShareTag a
                | (HasPrimitiveInfo a, Shareable Curry a) => Var Level ID

data ShareTag = Unshared
              | Shared
  deriving Show

deriving instance Show a => Show (CurryVal a)

--------------------------------------------------------------------------------
-- Now the type of our final monad just uses `CurryVal` as the return type
-- together with the `ND` monad.

newtype Curry a = Curry {
    unCurry :: ND (CurryVal a)
  }

-------------------------------------------------------------------------------
-- For evalutation of Curry values, we compute the ground normal form of the given value.
-- We also provide a funtion that converts results to a non-polymorphic, "normal" tree.

evalCurry :: NormalForm a => Curry a -> Tree Level (NDState, Level) a
evalCurry ma =
  unVal <$> evalND (unCurry (groundNormalForm ma)) (initialNDState ())
  where
    unVal (Val _ x) = x
    unVal (Var _ _) = error "evalCurry: Variable"

evalCurryTree :: NormalForm a => Curry a -> Tree.Tree a
evalCurryTree ma = convertTree $ evalCurry ma
  where
    convertTree (Single x)     = Tree.Leaf x
    convertTree (Fail   _)     = Tree.Empty
    convertTree (Choice _ l r) = Tree.Node (convertTree l) (convertTree r)

--------------------------------------------------------------------------------
-- Instantiation of variables follows a similar scheme as in the paper,
-- we only differentiate between Primitive types and NonPrimitives.
-- Non-Primitives are istantiated like in the paper,
-- but we keep the level annotation from the given variable for the generated choices.
-- Primitives are generated with a helper function that is the same for all primitive types.
-- In addition to generating a value for a primitive variable, we also add a constraint
-- that restricts the given variable to exactly that value.

instantiate :: forall a. (HasPrimitiveInfo a, Shareable Curry a) => Level -> ID -> Curry a
instantiate lvl i = Curry $
  case primitiveInfo @a of
    NoPrimitive -> msumLevel lvl $ flip map narrow $ \x -> unCurry $ do
                      sX <- share (return x)
                      modify (addToVarHeap i sX)
                      sX
    Primitive   -> get >>= \NDState { constraintStore = cst } ->
                   msumLevel lvl $ flip map (narrowPrimitive i cst) $ \x -> do
                      s@NDState { .. } <- get
                      let c = toSBV (Var 0 i) .=== toSBV (Val Shared x)
                      let cst' = insertConstraint c constraintStore
                      put (s { constraintStore = cst' })
                      modify (addToVarHeap i (return x))
                      return (Val Unshared x)

--------------------------------------------------------------------------------
-- Instantiation of primitive variables is done by querying the SMT solver for
-- a single solution to all constraints
-- and then asking for the value of the required variable in that solution.
-- If no solution exists, there are no values that we can instantiate to.
-- If a solution existed, we return the value from the solution and
-- ask recursively for another solution where the variable is not equal to any previous solution.
-- For that, we accumulate inequalties on the given variable.

narrowPrimitive :: SymVal a => ID -> ConstraintStore -> [a]
narrowPrimitive i cst = unsafePerformIO $ runSMT $ do
  mapM_ constrain cst
  query $ checkSat >>= \case
    Sat -> do
      v <- getValue (varToSBV i)
      let c = varToSBV i ./== toSBV (Val Shared v)
      return (v : narrowPrimitive i (insertConstraint c cst))
    _   -> return []


--------------------------------------------------------------------------------
-- To define the Monad istance, we also use the deref function from the paper appendix.
-- That function recursively checks if a variable is bound.
-- The recursion is necessary, since a variable can be bound to another variable.
-- Bind and return are then easy to define.

deref :: Curry a -> ND (CurryVal a)
deref (Curry m) = do
  fl <- m
  case fl of
    v@(Var _ i) -> get >>= \ndState ->
      case lookupHeap i (varHeap ndState) of
        Nothing  -> return v
        Just res -> deref (typed res)
    x@(Val _ _) -> return x

{-# INLINE[1] pureCurry #-}
pureCurry :: a -> Curry a
pureCurry = Curry . return . Val Unshared

{-# INLINE[1] bind #-}
bind :: Curry t -> (t -> Curry a) -> Curry a
ma `bind` f = Curry $ do
  a <- deref ma
  unCurry $ case a of
    Val _   x -> f x
    Var lvl i -> instantiate lvl i >>= f

instance Monad Curry where
  {-# INLINE return #-}
  return = pureCurry

  {-# INLINE (>>=) #-}
  (>>=) = bind

instance Functor Curry where
  fmap = liftM

instance Applicative Curry where
  pure = pureCurry
  (<*>) = ap

instance MonadState NDState Curry where
  get = Curry (Val Unshared <$> get)
  put s = Curry (put s >> return (Val Unshared ()))

--------------------------------------------------------------------------------
-- Non-determinisitic choice and failure are simply defined using the
-- `MonadPlus` instance of `ND`.

failed :: Curry a
failed = Curry mzero

(?) :: Curry a -> Curry a -> Curry a
Curry ma ? Curry mb = Curry $ mplus ma mb

instance Alternative Curry where
  empty = failed
  (<|>) = (?)

instance MonadPlus Curry

--------------------------------------------------------------------------------
-- Free variables are created by getting a freshID and the current level to annotate the variable with.

free :: (HasPrimitiveInfo a, Shareable Curry a) => Curry a
free = do
  ndState <- get
  let key = freshIDFromState ndState
  freeWith (currentLevel ndState) key

freeWith :: (HasPrimitiveInfo a, Shareable Curry a) => Level -> ID -> Curry a
freeWith lvl = Curry . return . Var lvl

--------------------------------------------------------------------------------
-- Sharing/memoization works as written in the paper,
-- with the optimization that a shareArgs on values that have benn shared already are omitted.

instance Sharing Curry where
  type ShareConstraints Curry a = Shareable Curry a
  share (Curry m) = memo (Curry (m >>= unCurry . shareCurryVal))
    where
      shareCurryVal (Val Unshared v) = shareArgs v
      shareCurryVal (Val Shared   v) = Curry (return (Val Shared v))
      shareCurryVal (Var lvl      i) = freeWith lvl i

{-# INLINE memo #-}
-- | Memorize a value or variable for explicit sharing.
memo :: Curry a -> Curry (Curry a)
memo (Curry m) = Curry $ do
  ndState1 <- get
  -- s needs to be used inside the unsafePerformIO to prevent it from
  -- floating out of the withTaskMap entirely.
  -- That would cause each memo to use the same IORef.
  let taskMap = unsafeDupablePerformIO
                    $ unsafeDupableInterleaveIO
                    $ noinline const (newIORef Map.empty) ndState1
  return $ Val Shared $ Curry $ do
    ndState2 <- get
    case lookupTaskResult taskMap (branchID ndState2) (parentIDs ndState2)  of
      Just (y, False) -> return y
      Just (y, True)  -> put (advanceNDState ndState2) >> return y
      Nothing -> do
        y <- m
        ndState3 <- get
        let wasND   = branchID ndState2 /= branchID ndState3
            insertID = if wasND
                          then branchID ndState3
                          else branchID ndState1
            insertH h = insertHeap insertID (toShared y, wasND) h
        unsafePerformIO (modifyIORef taskMap insertH)
          `seq` return (toShared y)
  where
    toShared (Val Unshared x) = Val Shared x
    toShared x                = x

--------------------------------------------------------------------------------
-- We could define lookupTaskResult exactly as in the paper,
-- but a small optimization is to get any value (we chose the maximium) from the
-- task result map after restricting the mep to all keys that are valid in the current branch.
-- There should only ever be one valid result for a branch.
-- Thus, choosing the maximum is ok.
-- This saves a few lookup operations for a single restrictKeys operation.

{-# NOINLINE lookupTaskResult #-}
lookupTaskResult :: IORef (Heap a) -> ID -> Set ID -> Maybe a
lookupTaskResult ref i s =
  -- msum $ map (`Map.lookup` trMap) $ Set.toList allIDs
  snd <$> Map.lookupMax trMap
  where
    allIDs = Set.insert i s
    trMap = Map.restrictKeys (unsafePerformIO (readIORef ref)) allIDs

--------------------------------------------------------------------------------
-- We provide two different funtions to compute normal forms.
-- The basic one does not instantiate variables, whereas the ground variant does.
-- Both traverse value arguments to pull up any non-determinism to the top.

normalForm :: NormalForm a => Curry a -> Curry a
normalForm a = Curry $ do
  a' <- deref a
  case a' of
    Val _ x -> unCurry (nfWith normalForm x)
    Var _ _ -> return a'

groundNormalForm :: NormalForm a => Curry a -> Curry a
groundNormalForm a = a >>= nfWith groundNormalForm

--------------------------------------------------------------------------------
-- Unification proceeds as shown in the appendix of the paper.
-- Our class uses Generics so that we can easily derive instances.
-- Since we also provide a "lazy" unification operator,
-- we also have a function for that in the type class.

class (Shareable Curry a, NormalForm a, HasPrimitiveInfo a) => Unifiable a where
  unifyWith :: (forall x. Unifiable x => Curry x -> Curry x -> Curry Bool)
            -> a -> a -> Curry Bool
  default unifyWith :: (Generic a, UnifiableGen (Rep a))
                    => (forall x. Unifiable x
                               => Curry x -> Curry x -> Curry Bool)
                    -> a -> a -> Curry Bool
  unifyWith f x y = unifyWithGen f (from x) (from y)

  lazyUnifyVar :: a -> ID -> Curry Bool
  default lazyUnifyVar :: (Generic a, UnifiableGen (Rep a))
                       => a -> ID -> Curry Bool
  lazyUnifyVar x i = do
    (x', xs) <- lazyUnifyVarGen (from x)
    modify (addToVarHeap i (return (to x' :: a)))
    and <$> sequence xs

--------------------------------------------------------------------------------
-- Unify itself is implemented as shown in the paper.

unify :: Unifiable a => Curry a -> Curry a -> Curry Bool
ma1 `unify` ma2 = Curry $ do
  a1 <- deref ma1
  a2 <- deref ma2
  unCurry $ case (a1, a2) of
    (Var _ i1, y@(Var _ i2))
      | i1 == i2        -> return True
      | otherwise       -> do
        modify (addToVarHeap i1 (Curry (return y)))
        return True
    (Val _ x, Val _ y)  -> unifyWith unify x y
    (Var _ i1, Val _ y) -> unifyVar i1 y
    (Val _ x, Var _ i2) -> unifyVar i2 x
  where
    unifyVar :: forall a. (HasPrimitiveInfo a, Unifiable a) => ID -> a -> Curry Bool
    unifyVar i v = case primitiveInfo @a of
      NoPrimitive -> do
        let x = narrowConstr v
        sX <- share (return x)
        modify (addToVarHeap i sX)
        unify sX (return v)
      Primitive   -> do
        modify (addToVarHeap i (return v))
        return True

(=:=) :: Unifiable a => Curry (a :-> a :-> Bool)
(=:=) = return . Func $ \a -> return . Func $ \b -> unify a b

--------------------------------------------------------------------------------
-- Lazy unification is used to implement functional patterns.
-- It tries to look just at its first argument.
-- In consequence, it can happen that a variable is bound to a failing computations.
-- Such a unification succeeds with this lazy unification,
-- but fails in the "normal" stricter unification.

unifyL :: Unifiable a => Curry a -> Curry a -> Curry Bool
ma1 `unifyL` ma2 = Curry $ do
  a1 <- deref ma1
  case a1 of
    Var _ i1 -> unCurry $ do
      ma2' <- share ma2
      modify (addToVarHeap i1 ma2')
      return True
    Val _ x  -> do
      a2 <- deref ma2
      unCurry $ case a2 of
        Var _ i2 -> lazyUnifyVar x i2
        Val _ y  -> unifyWith unifyL x y

addToVarHeap :: ID -> Curry a -> NDState -> NDState
addToVarHeap i v ndState =
  ndState { varHeap = insertHeap i (Untyped v) (varHeap ndState) }

(=:<=) :: Unifiable a => Curry (a :-> a :-> Bool)
(=:<=) = return . Func $ \a -> return . Func $ \b -> unifyL a b

--------------------------------------------------------------------------------
-- The set function of a given non-deterministic function are supposed to
-- encapsulate the non-determinism introduced by the given function.
-- However, the non-determinism of the arguments that funtion was applied to should
-- NOT be captured.
-- For this, we introduce a set of funtions `setX`,
-- where `X` is the arity of the function to be encapsulated.
-- To avoid capturing non-determinism from arguments
-- and to allow nested applications of set functions,
-- we introduce the level type.
-- By giving choices, variables and failures a level
-- and incrementing the level for arguments to a set function,
-- we can see if non-determinism introduced by something is supposed to be captured
-- by the set function we currently evaluate.

type Level = Integer

-- This setting of a level is supported by a type class again,
-- which sets the level of nested data structures using recursion.
-- The class uses generics again to automatically implement instances.

class Levelable a where
  setLevel :: Level -> a -> a
  default setLevel :: (Generic a, LevelableGen (Rep a)) => Level -> a -> a
  setLevel lvl = to . setLevelGen lvl . from

-- The set function operators are then defined by
-- 1. getting the current level
-- 2. modifying the state to set the setComputation flag (reason why is explained later)
-- 3. capturing the values of the ground normal form of the function applied to arguments.
-- All arguments get their level increased by one. Note that this is done lazily.
-- If the argument is not needed by the captured function, the argument is still not evaluated.
-- Since a 0-arity function bhas no arguments, step 3 is omitted there.

set0 :: NormalForm a
     => Curry a -> Curry (ListC a)
set0 f = do
  lvl <- currentLevel <$> get
  modify (\s -> s { setComputation = True })
  captureWithLvl lvl $ groundNormalForm f

set1 :: (Levelable a, NormalForm b)
     => (Curry a -> Curry b) -> Curry a -> Curry (ListC b)
set1 f arg = do
  lvl <- currentLevel <$> get
  modify (\s -> s { setComputation = True })
  captureWithLvl lvl $ groundNormalForm $ f
    (setLevelC (succ lvl) arg)

set2 :: (Levelable a, Levelable b, NormalForm c)
     => (Curry a -> Curry b -> Curry c) -> Curry a -> Curry b -> Curry (ListC c)
set2 f arg1 arg2 = do
  lvl <- currentLevel <$> get
  modify (\s -> s { setComputation = True })
  captureWithLvl lvl $ groundNormalForm $ f
    (setLevelC (succ lvl) arg1)
    (setLevelC (succ lvl) arg2)

-- So why do we need the setComputation flag?
-- The answer is complex, but as an intuition:
-- Every choice in a set function will be encapsulated and returned in the SAME non-deterministic branch.
-- And all choices for values that were not captured by the set function need to be consistent across all these captured values.
-- Thus, some information has to flow from one branch of the coice to the other one.
-- In consequence, we have to sequentialize the coputation of choices under a set function.

-- KiCS2 can avoid this sequenzialization due to the fingerprinting of choices, but we cannot.
-- Note that we are still not more strict than KiCS2, because to compute the element at an index `i` for a list,
-- we have to get the `i`-th result, which means we have to traverse the choices up to that point anyway.

-- So to set a level, we change the state.
-- In addition to changing the level, we also unset the setComputation flag, since we are in an argument position.
-- Arguments must be evaluated normally (i.e. not sequentially) like without set functions.
-- After computing the value, where we have to update the level recursively using the type class,
-- we reset the flag and level to whatever they were before.

setLevelC :: Levelable a => Level -> Curry a -> Curry a
setLevelC lvl (Curry a) = Curry $ do
  ndState1 <- get
  put (ndState1 { currentLevel = lvl, setComputation = False })
  res <- fmap setLevelCurryVal a
  ndState2 <- get
  put (ndState2 { currentLevel = currentLevel ndState1
                , setComputation = setComputation ndState1 })
  return res
  where
    setLevelCurryVal (Val t    x) = Val t (setLevel lvl x)
    setLevelCurryVal (Var lvl' i) = Var lvl' i

-- Capturing proceeds by traversing the tree structure
-- and collection the results into a list of trees.
-- When we encounter a choice, that needs to be captured,
-- we capture the left and right tree and combine the results.

captureWithLvl :: Level -> Curry a -> Curry (ListC a)
captureWithLvl lvl (Curry ma) = Curry $ ND $ Codensity $ \c1 ->
  ReaderT $ \ndState ->
    let list = captureTree (runND ma ndState)
    in lift list >>= \(s, v) -> runReaderT (c1 $ Val Unshared $ transListTree v) s
  where
    captureTree :: Tree Level (NDState, Level) (NDState, CurryVal a)
                -> Tree Level (NDState, Level) (NDState, ListTree a)
    captureTree (Single (s, Val _ a)) =
      Single (s, ConsTree (Single a) (Single NilTree))
    captureTree (Single (_, Var _ _)) =
      error "captureWithLvl: variable"
    captureTree (Fail (s, lvl'))
      | lvl == lvl' = Single (s, NilTree)
      | otherwise   = Fail (s, lvl')
    captureTree (Choice lvl' l r)
      | lvl' == lvl = combine (captureTree l) (captureTree r)
      -- this ^ is depth first (capturing l first), but we could change it if we want
      | otherwise   = Choice lvl' (captureTree l) (captureTree r)

-- Combining trees is straightforward.
-- We recurse into the tree of the first argument.
-- When we encounter a leaf, we combine it with all collected values of the second argument.
-- When we encounter a failure, it is absorbed by the second argument.

combine :: Tree Level (NDState, Level) (NDState, ListTree a)
        -> Tree Level (NDState, Level) (NDState, ListTree a)
        -> Tree Level (NDState, Level) (NDState, ListTree a)
combine (Single (_, NilTree))       ys      = ys
combine (Single (s, ConsTree x xs)) ys      =
  Single (s, ConsTree x (snd <$> combine (fmap (s,) xs) (getValues ys)))
combine (Choice lvl1 l1 r1) ys              =
  Choice lvl1 (combine l1 ys) (combine r1 ys)
combine (Fail _) (Single xs)                = Single xs
combine (Fail (s1, lvl1)) (Fail (s2, lvl2)) =
  if lvl1 <= lvl2 then Fail (s1, lvl1) else Fail (s2, lvl2)
combine (Fail lvl1) (Choice lvl2 l r)  =
  Choice lvl2 (combine (Fail lvl1) l) (combine (Fail lvl1) r)

-- We only want successes in the list, thus we remove failures from a tree list
getValues :: Tree Level (NDState, Level) (NDState, ListTree a)
          -> Tree Level (NDState, Level) (NDState, ListTree a)
getValues (Single (s, v))   = Single (s, v)
getValues (Fail   (s, _))   = Single (s, NilTree)
getValues (Choice lvl' l r) = Choice lvl' (getValues l) (getValues r)

-- Convert a tree list to a curry list.
transListTree :: ListTree a -> ListC a
transListTree NilTree         = NilC
transListTree (ConsTree x xs) =
  ConsC (treeToCurry x) (treeToCurry (fmap transListTree xs))

-- Lift a tree computation to a Curry computation
treeToCurry :: Tree Level (NDState, Level) a -> Curry a
treeToCurry = Curry . ND . lift . lift . lift . fmap (Val Unshared)

-- Basically a monadic List type, lifted with our tree monad.
data ListTree a = NilTree
                | ConsTree (Tree Level (NDState, Level) a)
                           (Tree Level (NDState, Level) (ListTree a))

mkList :: [Curry a] -> ListC a
mkList = foldr (\e xs -> ConsC e (return xs)) NilC

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Everything beyond this pint is not really interesting.
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Instances for the Generic implementation of Unifiable

class UnifiableGen f where
  unifyWithGen :: (forall x. Unifiable x => Curry x -> Curry x -> Curry Bool)
               -> f a -> f a -> Curry Bool

  lazyUnifyVarGen :: f a -> Curry (f a, [Curry Bool])

instance UnifiableGen V1 where
  unifyWithGen _ _ _ = failed

  lazyUnifyVarGen _ = failed

instance UnifiableGen U1 where
  unifyWithGen _ U1 U1 = return True

  lazyUnifyVarGen U1 = return (U1, [return True])

instance (UnifiableGen f, UnifiableGen g) => UnifiableGen (f :+: g) where
  unifyWithGen f (L1 x) (L1 y) = unifyWithGen f x y
  unifyWithGen f (R1 x) (R1 y) = unifyWithGen f x y
  unifyWithGen _ _      _      = failed

  lazyUnifyVarGen (L1 x) = first L1 <$> lazyUnifyVarGen x
  lazyUnifyVarGen (R1 x) = first R1 <$> lazyUnifyVarGen x

instance (UnifiableGen f, UnifiableGen g) => UnifiableGen (f :*: g) where
  unifyWithGen f (x1 :*: y1) (x2 :*: y2) =
    unifyWithGen f x1 x2 >> unifyWithGen f y1 y2

  lazyUnifyVarGen (x :*: y) = do
    (x', xs) <- lazyUnifyVarGen x
    (y', ys) <- lazyUnifyVarGen y
    return (x' :*: y', xs ++ ys)

instance UnifiableGen f => UnifiableGen (M1 i j f) where
  unifyWithGen f (M1 x) (M1 y) = unifyWithGen f x y

  lazyUnifyVarGen (M1 x) = first M1 <$> lazyUnifyVarGen x

instance Unifiable f => UnifiableGen (K1 i (Curry f)) where
  unifyWithGen f (K1 x) (K1 y) = x `f` y

  lazyUnifyVarGen (K1 x) = do
    x' <- share free
    return (K1 x', [x `unifyL` x'])

instance Unifiable Bool

instance Unifiable Integer where
  unifyWith _ x y = if x == y then return True else failed

  lazyUnifyVar n i = modify (addToVarHeap i (return n)) >> return True

--------------------------------------------------------------------------------
-- Instances for the Generic implementation of Levelable

class LevelableGen f where
  setLevelGen :: Level -> f x -> f x

instance LevelableGen V1 where
  setLevelGen _ = id

instance LevelableGen U1 where
  setLevelGen _ = id

instance (LevelableGen f, LevelableGen g) => LevelableGen (f :+: g) where
  setLevelGen lvl (L1 x) = L1 (setLevelGen lvl x)
  setLevelGen lvl (R1 x) = R1 (setLevelGen lvl x)

instance (LevelableGen f, LevelableGen g) => LevelableGen (f :*: g) where
  setLevelGen lvl (f :*: g) = setLevelGen lvl f :*: setLevelGen lvl g

instance LevelableGen f => LevelableGen (M1 j h f) where
  setLevelGen lvl (M1 x) = M1 (setLevelGen lvl x)

instance (Levelable a) => LevelableGen (K1 i (Curry a)) where
  setLevelGen lvl (K1 x) = K1 (setLevelC lvl x)

instance Levelable Bool

instance Levelable Int where
  setLevel _ x = x

instance Levelable Integer where
  setLevel _ x = x

--------------------------------------------------------------------------------
-- Some example data types.

data ListC a = NilC | ConsC (Curry a) (Curry (ListC a))
  deriving (Generic, Levelable, NormalForm)

instance (Shareable Curry a, HasPrimitiveInfo a) => HasPrimitiveInfo (ListC a)

instance (HasPrimitiveInfo a, Shareable Curry a) => Narrowable (ListC a)

instance Unifiable a => Unifiable (ListC a)

instance Shareable Curry a => Shareable Curry (ListC a) where
  shareArgs NilC         = return NilC
  shareArgs (ConsC x xs) = ConsC <$> share x <*> share xs

data Tuple2C a b = Tuple2C (Curry a) (Curry b)
  deriving (Generic, Levelable, NormalForm)

instance (Shareable Curry a, HasPrimitiveInfo a, Shareable Curry b, HasPrimitiveInfo b)
  => HasPrimitiveInfo (Tuple2C a b)

instance (HasPrimitiveInfo a, Shareable Curry a, HasPrimitiveInfo b, Shareable Curry b)
  => Narrowable (Tuple2C a b)

deriving instance (Shareable Curry a, Shareable Curry b)
  => Shareable Curry (Tuple2C a b)

instance (Unifiable a, Unifiable b) => Unifiable (Tuple2C a b)

--------------------------------------------------------------------------------
-- some debugging functions, not relevant

testShareTag :: Bool
testShareTag = head $ Tree.bfs $ evalCurryTree $ share xs
  >>= Curry . fmap (Val Shared) . ensureTagged
  where
    xs = return $ mkList [return 1 ? return 2, return 3, return 4]

    ensureTagged :: Curry (ListC Integer) -> ND Bool
    ensureTagged xs' = unCurry xs' >>= \case
      Val Unshared _          -> return False
      Val Shared NilC         -> return True
      Val Shared (ConsC y ys) -> (&&) <$> ensureTaggedI y <*> ensureTagged ys
      Var _ _                 -> return True

    ensureTaggedI :: Curry Integer -> ND Bool
    ensureTaggedI n = unCurry n >>= \case
      Val Unshared _ -> return False
      _              -> return True

showStructure :: Tree Level (NDState, Level) (NDState, CurryVal a) -> [Char]
showStructure (Single (_, Var  lvl idt)) =
  "<SVar_" ++ show lvl ++ "_" ++ show idt ++ ">"
showStructure (Single (_, Val _ _)) =
  "<Val>"
showStructure (Fail (_, lvl)) =
  "<Fail_" ++ show lvl ++ ">"
showStructure (Choice lvl l r) =
  "(" ++ showStructure l ++ ") :" ++ show lvl ++ ": (" ++ showStructure r ++ ")"

instance (NormalForm a, Show a) => Show (ListC a) where
  show NilC         = "[]"
  show (ConsC x xs) = show (toHsList x xs)
    where
      toHsList x' xs' = case evalCurry x' of
        Single x''' -> x''' : case evalCurry xs' of
          Single NilC             -> []
          Single (ConsC x'' xs'') -> toHsList x'' xs''
          _                       -> error ""
        _        -> error ""

instance (NormalForm a, Show a, NormalForm b, Show b)
  => Show (Tuple2C a b) where
    show (Tuple2C x y) = case (evalCurry x, evalCurry y) of
      (Single a, Single b) -> "(" ++ show a ++ "," ++ show b ++ ")"
      _                    -> error ""

--------------------------------------------------------------------------------
-- Convenience funtion to operate with MonadState

modify :: MonadState s m => (s -> s) -> m ()
modify f = state (\s -> ((), f s))
