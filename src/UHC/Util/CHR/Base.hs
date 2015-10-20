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

  , IsCHRConstraint(..)
  , CHRConstraint(..)
  
  , IsCHRGuard(..)
  , CHRGuard(..)
  
  , CHRRule(..)
  
  , Rule(..)
  , CHREmptySubstitution(..)
  , CHRMatchable(..), CHRMatchableKey
  , CHRCheckable(..)
  
  , (<==>), (==>), (|>)
  )
  where

import qualified UHC.Util.TreeTrie as TreeTrie
-- {%{EH}Base.Common},{%{EH}Substitutable}
import           UHC.Util.VarMp
import           Data.Monoid
import           Data.Typeable
import qualified Data.Set as Set
import           UHC.Util.Pretty
import           UHC.Util.CHR.Key
import           Control.Monad
import           UHC.Util.Binary
import           UHC.Util.Serialize
import           UHC.Util.Substitutable

-------------------------------------------------------------------------------------------
--- Constraint, Guard API
-------------------------------------------------------------------------------------------

-- | (Class alias) API for constraint requirements
class ( CHRMatchable env c subst
      , VarExtractable c
      , VarUpdatable c subst
      , Typeable c
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
      , PP g
      ) => IsCHRGuard env g subst

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
--- Existentially quantified Rule representations to allow for mix of arbitrary universes
-------------------------------------------------------------------------------------------

data CHRRule env subst
  = CHRRule
      { chrRule :: Rule (CHRConstraint env subst) (CHRGuard env subst)
      }

type instance TTKey (CHRRule env subst) = TTKey (CHRConstraint env subst)

deriving instance Typeable (CHRRule env subst)

instance Show (CHRRule env subst) where
  show _ = "CHRRule"

instance PP (CHRRule env subst) where
  pp (CHRRule r) = pp r

-------------------------------------------------------------------------------------------
--- CHR, derived structures
-------------------------------------------------------------------------------------------

-- | A CHR (rule) consist of head (simplification + propagation, boundary indicated by an Int), guard, and a body. All may be empty, but not all at the same time.
data Rule cnstr guard
  = Rule
      { ruleHead         :: ![cnstr]
      , ruleSimpSz       :: !Int             -- length of the part of the head which is the simplification part
      , ruleGuard        :: ![guard]         -- subst -> Maybe subst
      , ruleBody         :: ![cnstr]
      }
  deriving (Typeable, Data)

emptyCHRGuard :: [a]
emptyCHRGuard = []

instance Show (Rule c g) where
  show _ = "Rule"

instance (PP c,PP g) => PP (Rule c g) where
  pp chr
    = case chr of
        (Rule h@(_:_)  sz g b) | sz == 0        -> ppChr ([ppL h, pp  "==>"] ++ ppGB g b)
        (Rule h@(_:_)  sz g b) | sz == length h -> ppChr ([ppL h, pp "<==>"] ++ ppGB g b)
        (Rule h@(_:_)  sz g b)                  -> ppChr ([ppL (take sz h), pp "|", ppL (drop sz h), pp "<==>"] ++ ppGB g b)
        (Rule []       _  g b)                  -> ppChr (ppGB g b)
    where ppGB g@(_:_) b@(_:_) = [ppL g, "|" >#< ppL b]
          ppGB g@(_:_) []      = [ppL g >#< "|"]
          ppGB []      b@(_:_) = [ppL b]
          ppGB []      []      = []
          ppL [x] = pp x
          ppL xs  = ppBracketsCommasBlock xs -- ppParensCommasBlock xs
          ppChr l = vlist l -- ppCurlysBlock

type instance TTKey (Rule cnstr guard) = TTKey cnstr

instance (TTKeyable cnstr) => TTKeyable (Rule cnstr guard) where
  toTTKey' o chr = toTTKey' o $ head $ ruleHead chr

-------------------------------------------------------------------------------------------
--- Var instances
-------------------------------------------------------------------------------------------

type instance ExtrValVarKey (Rule c g) = ExtrValVarKey c

instance (VarExtractable c, VarExtractable g, ExtrValVarKey c ~ ExtrValVarKey g) => VarExtractable (Rule c g) where
  varFreeSet          (Rule {ruleHead=h, ruleGuard=g, ruleBody=b})
    = Set.unions $ concat [map varFreeSet h, map varFreeSet g, map varFreeSet b]

instance (VarUpdatable c s, VarUpdatable g s) => VarUpdatable (Rule c g) s where
  varUpd s r@(Rule {ruleHead=h, ruleGuard=g, ruleBody=b})
    = r {ruleHead = map (varUpd s) h, ruleGuard = map (varUpd s) g, ruleBody = map (varUpd s) b}

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
  chrMatchTo      :: env -> subst -> x -> x -> Maybe subst

-------------------------------------------------------------------------------------------
--- CHRCheckable
-------------------------------------------------------------------------------------------

-- | A Checkable participates in the reduction process as a guard, to be checked.
class CHRCheckable env x subst where
  chrCheck      :: env -> subst -> x -> Maybe subst

-------------------------------------------------------------------------------------------
--- What a constraint must be capable of
-------------------------------------------------------------------------------------------

-- | The things a constraints needs to be capable of in order to participate in solving
class IsConstraint c where
  -- | Requires solving? Or is just a residue...
  cnstrRequiresSolve :: c -> Bool

-------------------------------------------------------------------------------------------
--- Construction
-------------------------------------------------------------------------------------------

infix   1 <==>, ==>
infixr  0 |>

(<==>), (==>) :: [c] -> [c] -> Rule c g
hs <==>  bs = Rule hs (length hs) emptyCHRGuard bs
hs  ==>  bs = Rule hs 0 emptyCHRGuard bs

(|>) :: Rule c g -> [g] -> Rule c g
chr |> g = chr {ruleGuard = ruleGuard chr ++ g}

-------------------------------------------------------------------------------------------
--- Instances: ForceEval, Binary, Serialize
-------------------------------------------------------------------------------------------

instance (Serialize c,Serialize g) => Serialize (Rule c g) where
  sput (Rule a b c d) = sput a >> sput b >> sput c >> sput d
  sget = liftM4 Rule sget sget sget sget
