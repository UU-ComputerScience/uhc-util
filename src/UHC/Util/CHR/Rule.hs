{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies, UndecidableInstances, ExistentialQuantification, ScopedTypeVariables, StandaloneDeriving #-}

-------------------------------------------------------------------------------------------
--- Constraint Handling Rules
-------------------------------------------------------------------------------------------

{- |
Derived from work by Gerrit vd Geest, but with searching structures for predicates
to avoid explosion of search space during resolution.
-}

module UHC.Util.CHR.Rule
  ( CHRRule(..)
  
  , Rule(..)
  
  , (<==>), (==>), (|>)
  , MkSolverConstraint(..)
  , MkSolverGuard(..)
  )
  where

import qualified UHC.Util.TreeTrie as TreeTrie
import           UHC.Util.CHR.Base
import           UHC.Util.VarMp
import           Data.Monoid
import           Data.Typeable
import           Data.Data
import qualified Data.Set as Set
import           UHC.Util.Pretty
import           UHC.Util.CHR.Key
import           Control.Monad
import           UHC.Util.Binary
import           UHC.Util.Serialize
import           UHC.Util.Substitutable

-------------------------------------------------------------------------------------------
--- Existentially quantified Rule representations to allow for mix of arbitrary universes
-------------------------------------------------------------------------------------------

data CHRRule env subst
  = CHRRule
      { chrRule :: Rule (CHRConstraint env subst) (CHRGuard env subst)
      }
  deriving (Typeable)

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
--- Construction: Rule
-------------------------------------------------------------------------------------------

{-
class MkRule c g c' g' r | r c -> g g' c', r g -> c c' g', c c' -> g g' r, g g' -> c c' r, r g' -> c c' g, c' g' r -> c g, r -> c g c' g' where
-- class MkRule c g c' g' r | r -> c' g' c g, c' -> g' r, g' -> c' r, c -> g r, g -> c r where
-- class MkRule c g c' g' r | r -> c' g' c g where
  -- | Lift constraint, from In to Out
  toSolverConstraint :: c -> c'
  -- | Lift guard, from In to Out
  mkSolverGuard :: g -> g'
  -- | Make rule
  mkRule :: [c'] -> Int -> [g'] -> [c'] -> r
  -- | Add guards to rule
  guardRule :: [g'] -> r -> r

infix   1 <==>, ==>
infixr  0 |>

(<==>), (==>) :: forall c g c' g' r . (MkRule c g c' g' r) => [c] -> [c] -> r
hs <==>  bs = mkRule (map toSolverConstraint hs) (length hs) ([]::[g']) (map toSolverConstraint bs)
hs  ==>  bs = mkRule (map toSolverConstraint hs) 0 ([]::[g']) (map toSolverConstraint bs)

(|>) :: (MkRule c g c' g' r) => r -> [g] -> r
r |> g = guardRule (map mkSolverGuard g) r

instance MkRule c g c g (Rule c g) where
  toSolverConstraint = id
  mkSolverGuard = id
  mkRule = Rule
  guardRule g r = r {ruleGuard = ruleGuard r ++ g}
-}

class MkSolverConstraint c c' where
  -- | Lift constraint, from In to Out
  toSolverConstraint :: c' -> c
  fromSolverConstraint :: c -> Maybe c'

instance {-# INCOHERENT #-} MkSolverConstraint c c where
  toSolverConstraint = id
  fromSolverConstraint = Just
  
instance {-# OVERLAPS #-}
         ( IsCHRConstraint e c s
         , TTKey (CHRConstraint e s) ~ TTKey c
         , ExtrValVarKey (CHRConstraint e s) ~ ExtrValVarKey c
         ) => MkSolverConstraint (CHRConstraint e s) c where
  toSolverConstraint = CHRConstraint
  fromSolverConstraint (CHRConstraint c) = cast c

class MkSolverGuard g g' where
  -- | Lift constraint, from In to Out
  mkSolverGuard :: g' -> g

instance {-# INCOHERENT #-} MkSolverGuard g g where
  mkSolverGuard = id

instance {-# OVERLAPS #-}
         ( IsCHRGuard e g s
         , ExtrValVarKey (CHRGuard e s) ~ ExtrValVarKey g
         ) => MkSolverGuard (CHRGuard e s) g where
  mkSolverGuard = CHRGuard

class MkRule r where
  type SolverConstraint r :: *
  type SolverGuard r :: *
  -- | Make rule
  mkRule :: [SolverConstraint r] -> Int -> [SolverGuard r] -> [SolverConstraint r] -> r
  -- | Add guards to rule
  guardRule :: [SolverGuard r] -> r -> r

instance MkRule (Rule c g) where
  type SolverConstraint (Rule c g) = c
  type SolverGuard (Rule c g) = g
  mkRule = Rule
  guardRule g r = r {ruleGuard = ruleGuard r ++ g}

instance MkRule (CHRRule e s) where
  type SolverConstraint (CHRRule e s) = (CHRConstraint e s)
  type SolverGuard (CHRRule e s) = (CHRGuard e s)
  mkRule h1 h2 l b = CHRRule $ mkRule h1 h2 l b 
  guardRule g (CHRRule r) = CHRRule $ guardRule g r

infix   1 <==>, ==>
infixr  0 |>

(<==>), (==>) :: (MkRule r, MkSolverConstraint (SolverConstraint r) c1, MkSolverConstraint (SolverConstraint r) c2) => [c1] -> [c2] -> r
hs <==>  bs = mkRule (map toSolverConstraint hs) (length hs) [] (map toSolverConstraint bs)
hs  ==>  bs = mkRule (map toSolverConstraint hs) 0 [] (map toSolverConstraint bs)

(|>) :: (MkRule r, MkSolverGuard (SolverGuard r) g') => r -> [g'] -> r
r |> g = guardRule (map mkSolverGuard g) r


{-
-- Below variant runs into typing problem w.r.t. injectivity of type functions...
class MkRule r where
  type MkSolverConstraintIn r :: *
  type MkSolverGuardIn r :: *
  type MkSolverConstraintOut r :: *
  type MkSolverGuardOut r :: *
  -- | Lift constraint, from In to Out
  toSolverConstraint :: MkSolverConstraintIn r -> MkSolverConstraintOut r
  -- | Lift guard, from In to Out
  mkSolverGuard :: MkSolverGuardIn r -> MkSolverGuardOut r
  -- | Make rule
  mkRule :: [MkSolverConstraintOut r] -> Int -> [MkSolverGuardOut r] -> [MkSolverConstraintOut r] -> r
  -- | Add guards to rule
  guardRule :: [MkSolverGuardOut r] -> r -> r

infix   1 <==>, ==>
infixr  0 |>

(<==>), (==>) :: forall r c . (MkRule r, c ~ MkSolverConstraintIn r) => [c] -> [c] -> r
hs <==>  bs = mkRule (map toSolverConstraint hs) (length hs) (map mkSolverGuard emptyCHRGuard) (map toSolverConstraint bs)
hs  ==>  bs = mkRule (map toSolverConstraint hs) 0 (map mkSolverGuard emptyCHRGuard) (map toSolverConstraint bs)

(|>) :: (MkRule r, g ~ MkSolverGuardIn r) => r -> [g] -> r
r |> g = guardRule (map mkSolverGuard g) r

instance MkRule (Rule c g) where
  type MkSolverConstraintIn (Rule c g) = c
  type MkSolverGuardIn (Rule c g) = g
  type MkSolverConstraintOut (Rule c g) = c
  type MkSolverGuardOut (Rule c g) = g
  toSolverConstraint = id
  mkSolverGuard = id
  mkRule = Rule
  guardRule g r = r {ruleGuard = ruleGuard r ++ g}
-}

-------------------------------------------------------------------------------------------
--- Instances: Serialize
-------------------------------------------------------------------------------------------

instance (Serialize c,Serialize g) => Serialize (Rule c g) where
  sput (Rule a b c d) = sput a >> sput b >> sput c >> sput d
  sget = liftM4 Rule sget sget sget sget

{-
instance Serialize (CHRRule e s) where
  sput (CHRRule a) = sput a
  sget = liftM CHRRule sget
-}
