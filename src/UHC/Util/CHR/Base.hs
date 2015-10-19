{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies, UndecidableInstances #-}

-------------------------------------------------------------------------------------------
--- Constraint Handling Rules
-------------------------------------------------------------------------------------------

{- |
Derived from work by Gerrit vd Geest, but with searching structures for predicates
to avoid explosion of search space during resolution.
-}

module UHC.Util.CHR.Base
  ( IsConstraint(..)
  
  , CHR(..)
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
import qualified Data.Set as Set
import           UHC.Util.Pretty
import           UHC.Util.CHR.Key
import           Control.Monad
import           UHC.Util.Binary
import           UHC.Util.Serialize
import           UHC.Util.Substitutable

-------------------------------------------------------------------------------------------
--- CHR, derived structures
-------------------------------------------------------------------------------------------

-- | A CHR (rule) consist of head (simplification + propagation, boundary indicated by an Int), guard, and a body. All may be empty, but not all at the same time.
data CHR cnstr guard subst
  = CHR
      { chrHead         :: ![cnstr]
      , chrSimpSz       :: !Int             -- length of the part of the head which is the simplification part
      , chrGuard        :: ![guard]         -- subst -> Maybe subst
      , chrBody         :: ![cnstr]
      }
  deriving (Typeable, Data)

emptyCHRGuard :: [a]
emptyCHRGuard = []

instance Show (CHR c g s) where
  show _ = "CHR"

instance (PP c,PP g) => PP (CHR c g s) where
  pp chr
    = case chr of
        (CHR h@(_:_)  sz g b) | sz == 0        -> ppChr ([ppL h, pp  "==>"] ++ ppGB g b)
        (CHR h@(_:_)  sz g b) | sz == length h -> ppChr ([ppL h, pp "<==>"] ++ ppGB g b)
        (CHR h@(_:_)  sz g b)                  -> ppChr ([ppL (take sz h), pp "|", ppL (drop sz h), pp "<==>"] ++ ppGB g b)
        (CHR []       _  g b)                  -> ppChr (ppGB g b)
    where ppGB g@(_:_) b@(_:_) = [ppL g, "|" >#< ppL b]
          ppGB g@(_:_) []      = [ppL g >#< "|"]
          ppGB []      b@(_:_) = [ppL b]
          ppGB []      []      = []
          ppL [x] = pp x
          ppL xs  = ppBracketsCommasBlock xs -- ppParensCommasBlock xs
          ppChr l = vlist l -- ppCurlysBlock

type instance TTKey (CHR cnstr guard subst) = TTKey cnstr

instance (TTKeyable cnstr) => TTKeyable (CHR cnstr guard subst) where
  toTTKey' o chr = toTTKey' o $ head $ chrHead chr

-------------------------------------------------------------------------------------------
--- Var instances
-------------------------------------------------------------------------------------------

type instance ExtrValVarKey (CHR c g s) = ExtrValVarKey c

instance (VarExtractable c, VarExtractable g, ExtrValVarKey c ~ ExtrValVarKey g) => VarExtractable (CHR c g s) where
  varFreeSet          (CHR {chrHead=h, chrGuard=g, chrBody=b})
    = Set.unions $ concat [map varFreeSet h, map varFreeSet g, map varFreeSet b]

instance (VarUpdatable c s, VarUpdatable g s) => VarUpdatable (CHR c g s) s where
  varUpd s r@(CHR {chrHead=h, chrGuard=g, chrBody=b})
    = r {chrHead = map (varUpd s) h, chrGuard = map (varUpd s) g, chrBody = map (varUpd s) b}

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

(<==>), (==>) :: [c] -> [c] -> CHR c g s
hs <==>  bs = CHR hs (length hs) emptyCHRGuard bs
hs  ==>  bs = CHR hs 0 emptyCHRGuard bs

(|>) :: CHR c g s -> [g] -> CHR c g s
chr |> g = chr {chrGuard = chrGuard chr ++ g}

-------------------------------------------------------------------------------------------
--- Instances: ForceEval, Binary, Serialize
-------------------------------------------------------------------------------------------

instance (Serialize c,Serialize g,Serialize s) => Serialize (CHR c g s) where
  sput (CHR a b c d) = sput a >> sput b >> sput c >> sput d
  sget = liftM4 CHR sget sget sget sget
