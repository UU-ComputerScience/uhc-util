{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies, UndecidableInstances, ExistentialQuantification, ScopedTypeVariables, StandaloneDeriving #-}

-------------------------------------------------------------------------------------------
--- Constraint Handling Rules
-------------------------------------------------------------------------------------------

{- |
Derived from work by Gerrit vd Geest, but with searching structures for predicates
to avoid explosion of search space during resolution.
-}

module UHC.Util.CHR.Base
  ( IsConstraint(..)
  , ConstraintSolvesVia(..)

  , IsCHRConstraint(..)
  , CHRConstraint(..)
  
  , IsCHRGuard(..)
  , CHRGuard(..)
  
  , IsCHRBuiltin(..)
  , CHRBuiltin(..)
  
  , IsCHRPrio(..)
  , CHRPrio(..)
  
  , CHREmptySubstitution(..)
  
  , CHRMatchable(..), CHRMatchableKey
  
  , CHRCheckable(..)
  
  , CHRPrioEvaluatable(..)
  
  , CHRBuiltinSolvable(..)
  
  , CHRTrOpt(..)
  )
  where

import qualified UHC.Util.TreeTrie as TreeTrie
import           UHC.Util.VarMp
import           Data.Monoid
import           Data.Typeable
import           Unsafe.Coerce
import qualified Data.Set as Set
import           UHC.Util.Pretty
import           UHC.Util.CHR.Key
import           Control.Monad
import           UHC.Util.Utils
import           UHC.Util.Binary
import           UHC.Util.Serialize
import           UHC.Util.Substitutable

-------------------------------------------------------------------------------------------
--- Constraint, Guard, & Prio API
-------------------------------------------------------------------------------------------

-- | (Class alias) API for constraint requirements
class ( CHRMatchable env c subst
      , VarExtractable c
      , VarUpdatable c subst
      , Typeable c
      , Serialize c
      , TTKeyable c
      , IsConstraint c
      , Ord c, Ord (TTKey c)
      , PP c, PP (TTKey c)
      ) => IsCHRConstraint env c subst

-- | (Class alias) API for guard requirements
class ( CHRCheckable env g subst
      , VarExtractable g
      , VarUpdatable g subst
      , Typeable g
      , Serialize g
      , PP g
      ) => IsCHRGuard env g subst

-- | (Class alias) API for builtin solvable requirements
class ( CHRBuiltinSolvable env b subst
      , Typeable b
      , Serialize b
      , PP b
      ) => IsCHRBuiltin env b subst

instance {-# OVERLAPPABLE #-} IsCHRBuiltin env () subst

-- | (Class alias) API for priority requirements
class ( CHRPrioEvaluatable env p subst
      , Typeable p
      , Serialize p
      , PP p
      ) => IsCHRPrio env p subst

instance {-# OVERLAPPABLE #-} IsCHRPrio env () subst

-------------------------------------------------------------------------------------------
--- Existentially quantified Constraint representations to allow for mix of arbitrary universes
-------------------------------------------------------------------------------------------

data CHRConstraint env subst
  = forall c . 
    ( IsCHRConstraint env c subst
    , TTKey (CHRConstraint env subst) ~ TTKey c
    , ExtrValVarKey (CHRConstraint env subst) ~ ExtrValVarKey c
    )
    => CHRConstraint
         { chrConstraint :: c
         }

deriving instance Typeable (CHRConstraint env subst)
-- deriving instance (Data env, Data subst) => Data (CHRConstraint env subst)

instance TTKeyable (CHRConstraint env subst) where
  toTTKey' o (CHRConstraint c) = toTTKey' o c

instance Show (CHRConstraint env subst) where
  show _ = "CHRConstraint"

instance PP (CHRConstraint env subst) where
  pp (CHRConstraint c) = pp c

instance IsConstraint (CHRConstraint env subst) where
  cnstrRequiresSolve (CHRConstraint c) = cnstrRequiresSolve c

instance Eq (CHRConstraint env subst) where
  CHRConstraint (c1 :: c1) == CHRConstraint c2 = case cast c2 of
    Just (c2' :: c1) -> c1 == c2'
    _                -> False

instance Ord (CHRConstraint env subst) where
  CHRConstraint (c1 :: c1) `compare` CHRConstraint (c2 :: c2) = case cast c2 of
    Just (c2' :: c1) -> c1 `compare` c2'
    _                -> typeOf (undefined :: c1) `compare` typeOf (undefined :: c2)

instance (CHRMatchableKey subst ~ TTKey (CHRConstraint env subst)) => CHRMatchable env (CHRConstraint env subst) subst where
  chrMatchTo env subst c1 c2
    = case (c1, c2) of
        (CHRConstraint (c1' :: c), CHRConstraint c2') -> case cast c2' of
          Just (c2'' :: c) -> chrMatchTo env subst c1' c2''
          _ -> Nothing

instance (Ord (ExtrValVarKey (CHRConstraint env subst))) => VarExtractable (CHRConstraint env subst) where
  varFreeSet (CHRConstraint c) = varFreeSet c

instance VarUpdatable (CHRConstraint env subst) subst where
  s `varUpd`    CHRConstraint c =  CHRConstraint c'
    where c'        = s `varUpd`    c
  s `varUpdCyc` CHRConstraint c = (CHRConstraint c', cyc)
    where (c', cyc) = s `varUpdCyc` c

-------------------------------------------------------------------------------------------
--- Existentially quantified Guard representations to allow for mix of arbitrary universes
-------------------------------------------------------------------------------------------

data CHRGuard env subst
  = forall g . 
    ( IsCHRGuard env g subst
    , ExtrValVarKey (CHRGuard env subst) ~ ExtrValVarKey g
    )
    => CHRGuard
         { chrGuard :: g
         }

deriving instance Typeable (CHRGuard env subst)
-- deriving instance (Data env, Data subst) => Data (CHRGuard env subst)

instance Show (CHRGuard env subst) where
  show _ = "CHRGuard"

instance PP (CHRGuard env subst) where
  pp (CHRGuard c) = pp c

instance (Ord (ExtrValVarKey (CHRGuard env subst))) => VarExtractable (CHRGuard env subst) where
  varFreeSet (CHRGuard g) = varFreeSet g

instance VarUpdatable (CHRGuard env subst) subst where
  s `varUpd`    CHRGuard g =  CHRGuard g'
    where g'        = s `varUpd`    g
  s `varUpdCyc` CHRGuard g = (CHRGuard g', cyc)
    where (g', cyc) = s `varUpdCyc` g

instance CHRCheckable env (CHRGuard env subst) subst where
  chrCheck env subst (CHRGuard g) = chrCheck env subst g

-------------------------------------------------------------------------------------------
--- Existentially quantified Prio representations to allow for mix of arbitrary universes
-------------------------------------------------------------------------------------------

data CHRPrio env subst
  = forall p . 
    ( IsCHRPrio env p subst
    )
    => CHRPrio
         { chrPrio :: p
         }

deriving instance Typeable (CHRPrio env subst)
-- deriving instance (Data env, Data subst) => Data (CHRGuard env subst)

instance Show (CHRPrio env subst) where
  show _ = "CHRPrio"

instance PP (CHRPrio env subst) where
  pp (CHRPrio p) = pp p

{-
instance (Ord (ExtrValVarKey (CHRGuard env subst))) => VarExtractable (CHRGuard env subst) where
  varFreeSet (CHRGuard g) = varFreeSet g

instance VarUpdatable (CHRGuard env subst) subst where
  s `varUpd`    CHRGuard g =  CHRGuard g'
    where g'        = s `varUpd`    g
  s `varUpdCyc` CHRGuard g = (CHRGuard g', cyc)
    where (g', cyc) = s `varUpdCyc` g
-}

instance CHRPrioEvaluatable env (CHRPrio env subst) subst where
  chrPrioEval env subst (CHRPrio p) = chrPrioEval env subst p

-------------------------------------------------------------------------------------------
--- Existentially quantified Builtin representations to allow for mix of arbitrary universes
-------------------------------------------------------------------------------------------

data CHRBuiltin env subst
  = forall b . 
    ( IsCHRBuiltin env b subst
    )
    => CHRBuiltin
         { chrBuiltin :: b
         }

deriving instance Typeable (CHRBuiltin env subst)

instance Show (CHRBuiltin env subst) where
  show _ = "CHRBuiltin"

instance PP (CHRBuiltin env subst) where
  pp (CHRBuiltin b) = pp b

instance CHRBuiltinSolvable env (CHRBuiltin env subst) subst where
  chrBuiltinSolve env subst (CHRBuiltin b) = chrBuiltinSolve env subst b

-------------------------------------------------------------------------------------------
--- CHREmptySubstitution
-------------------------------------------------------------------------------------------

-- | Capability to yield an empty substitution.
class CHREmptySubstitution subst where
  chrEmptySubst :: subst

-------------------------------------------------------------------------------------------
--- CHRMatchable
-------------------------------------------------------------------------------------------

type family CHRMatchableKey subst :: *

-- | A Matchable participates in the reduction process as a reducable constraint.
class (TTKeyable x, TTKey x ~ CHRMatchableKey subst) => CHRMatchable env x subst where -- skey | subst -> skey where --- | x -> subst env where
  chrMatchTo :: env -> subst -> x -> x -> Maybe subst

-------------------------------------------------------------------------------------------
--- CHRCheckable
-------------------------------------------------------------------------------------------

-- | A Checkable participates in the reduction process as a guard, to be checked.
class CHRCheckable env x subst where
  chrCheck :: env -> subst -> x -> Maybe subst

-------------------------------------------------------------------------------------------
--- CHRBuiltinSolvable
-------------------------------------------------------------------------------------------

-- | A BuiltinSolvable can result from reduction to a CHR body, representing something which the solver domain specifically solves
class CHRBuiltinSolvable env x subst where
  chrBuiltinSolve :: env -> subst -> x -> Maybe subst

instance {-# OVERLAPPABLE #-} CHRBuiltinSolvable env () subst where
  chrBuiltinSolve _ _ _ = Nothing

-------------------------------------------------------------------------------------------
--- CHRPrioEvaluatable
-------------------------------------------------------------------------------------------

-- | A PrioEvaluatable participates in the reduction process to indicate the rule priority, higher prio takes precedence
class CHRPrioEvaluatable env x subst where
  chrPrioEval      :: env -> subst -> x -> Int

instance {-# OVERLAPPABLE #-} CHRPrioEvaluatable env () subst where
  chrPrioEval _ _ _ = minBound

-------------------------------------------------------------------------------------------
--- What a constraint must be capable of
-------------------------------------------------------------------------------------------

-- | Different ways of solving
data ConstraintSolvesVia
  = ConstraintSolvesVia_Rule        -- ^ rewrite/CHR rules apply
  | ConstraintSolvesVia_Solve       -- ^ solving involving finding of variable bindings (e.g. unification)
  | ConstraintSolvesVia_Residual    -- ^ a leftover, residue
  deriving (Show, Enum, Eq, Ord)

-- | The things a constraints needs to be capable of in order to participate in solving
class IsConstraint c where
  -- | Requires solving? Or is just a residue...
  cnstrRequiresSolve :: c -> Bool
  cnstrRequiresSolve c = case cnstrSolvesVia c of
    ConstraintSolvesVia_Residual -> False
    _                            -> True
  
  cnstrSolvesVia :: c -> ConstraintSolvesVia
  cnstrSolvesVia c | cnstrRequiresSolve c = ConstraintSolvesVia_Rule
                   | otherwise            = ConstraintSolvesVia_Residual

-------------------------------------------------------------------------------------------
--- Tracing options, specific for CHR solvers
-------------------------------------------------------------------------------------------

data CHRTrOpt
  = CHRTrOpt_Lookup     -- ^ trie query
  | CHRTrOpt_Stats      -- ^ various stats
  deriving (Eq, Ord, Show)

