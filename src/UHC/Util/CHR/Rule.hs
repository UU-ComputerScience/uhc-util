{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies, UndecidableInstances, ExistentialQuantification, ScopedTypeVariables, StandaloneDeriving #-}
-- {-# LANGUAGE AllowAmbiguousTypes #-}

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
  , ruleSz
  
  , (<==>>), (==>>), (<\=>>)
  , (<==>), (==>), (<\=>)
  , (|>), (|!)
  
  , MkSolverConstraint(..)
  , MkSolverGuard(..)
  , MkSolverBuiltin(..)
  , MkSolverPrio(..)
  
  , MkRule(prioritizeRule)
  )
  where

import qualified UHC.Util.TreeTrie as TreeTrie
import           UHC.Util.CHR.Base
import           UHC.Util.VarMp
import           UHC.Util.Utils
import           Data.Monoid
import           Data.Typeable
-- import           Data.Data
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
data Rule cnstr guard builtin prio
  = Rule
      { ruleHead         :: ![cnstr]
      , ruleSimpSz       :: !Int                -- ^ length of the part of the head which is the simplification part
      , ruleGuard        :: ![guard]            
      , ruleBody         :: ![cnstr]
      , ruleBodyBuiltin  :: ![builtin]
      , rulePrio         :: !(Maybe prio)       -- ^ optional priority, if absent it is considered the lowest possible
      }
  deriving (Typeable)

-- | Total nr of cnstrs in rule
ruleSz :: Rule c g b p -> Int
ruleSz = length . ruleHead
{-# INLINE ruleSz #-}

emptyCHRGuard :: [a]
emptyCHRGuard = []

instance Show (Rule c g b p) where
  show _ = "Rule"

instance (PP c, PP g, PP p, PP b) => PP (Rule c g b p) where
  pp chr
    = case chr of
        (Rule h@(_:_)  sz g b bi p) | sz == 0        -> ppChr ([ppL h, pp  "==>"] ++ ppGB g b)
        (Rule h@(_:_)  sz g b bi p) | sz == length h -> ppChr ([ppL h, pp "<==>"] ++ ppGB g b)
        (Rule h@(_:_)  sz g b bi p)                  -> ppChr ([ppL (take sz h), pp "\\", ppL (drop sz h), pp "<\\=>"] ++ ppGB g b)
        (Rule []       _  g b bi p)                  -> ppChr (ppGB g b)
    where ppGB g@(_:_) b@(_:_) = [ppL b, "|" >#< ppL g]
          ppGB g@(_:_) []      = ["|" >#< ppL g]
          ppGB []      b@(_:_) = [ppL b]
          ppGB []      []      = []
          ppL [x] = pp x
          ppL xs  = ppBracketsCommasBlock xs -- ppParensCommasBlock xs
          ppChr l = vlist l -- ppCurlysBlock

type instance TTKey (Rule cnstr guard builtin prio) = TTKey cnstr
type instance TreeTrie.TrTrKey (Rule cnstr guard builtin prio) = TTKey cnstr

instance (TTKeyable cnstr) => TTKeyable (Rule cnstr guard builtin prio) where
  toTTKey' o chr = toTTKey' o $ head $ ruleHead chr

-------------------------------------------------------------------------------------------
--- Existentially quantified Rule representations to allow for mix of arbitrary universes
-------------------------------------------------------------------------------------------

data CHRRule env subst
  = CHRRule
      { chrRule :: Rule (CHRConstraint env subst) (CHRGuard env subst) () ()
      }
  deriving (Typeable)

type instance TTKey (CHRRule env subst) = TTKey (CHRConstraint env subst)

deriving instance Typeable (CHRRule env subst)

instance Show (CHRRule env subst) where
  show _ = "CHRRule"

instance PP (CHRRule env subst) where
  pp (CHRRule r) = pp r

-------------------------------------------------------------------------------------------
--- Var instances
-------------------------------------------------------------------------------------------

type instance ExtrValVarKey (Rule c g b p) = ExtrValVarKey c

instance (VarExtractable c, VarExtractable g, ExtrValVarKey c ~ ExtrValVarKey g) => VarExtractable (Rule c g b p) where
  varFreeSet          (Rule {ruleHead=h, ruleGuard=g, ruleBody=b})
    = Set.unions $ concat [map varFreeSet h, map varFreeSet g, map varFreeSet b]

instance (VarUpdatable c s, VarUpdatable g s) => VarUpdatable (Rule c g b p) s where
  varUpd s r@(Rule {ruleHead=h, ruleGuard=g, ruleBody=b})
    = r {ruleHead = map (varUpd s) h, ruleGuard = map (varUpd s) g, ruleBody = map (varUpd s) b}

-------------------------------------------------------------------------------------------
--- Construction: Rule
-------------------------------------------------------------------------------------------

class MkSolverConstraint c c' where
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
  toSolverGuard :: g' -> g
  fromSolverGuard :: g -> Maybe g'

instance {-# INCOHERENT #-} MkSolverGuard g g where
  toSolverGuard = id
  fromSolverGuard = Just

instance {-# OVERLAPS #-}
         ( IsCHRGuard e g s
         , ExtrValVarKey (CHRGuard e s) ~ ExtrValVarKey g
         ) => MkSolverGuard (CHRGuard e s) g where
  toSolverGuard = CHRGuard
  fromSolverGuard (CHRGuard g) = cast g

class MkSolverBuiltin b b' where
  toSolverBuiltin :: b' -> b
  fromSolverBuiltin :: b -> Maybe b'

instance {-# INCOHERENT #-} MkSolverBuiltin b b where
  toSolverBuiltin = id
  fromSolverBuiltin = Just

instance {-# OVERLAPS #-}
         ( IsCHRBuiltin e b s
         -- , ExtrValVarKey (CHRBuiltin e s) ~ ExtrValVarKey b
         ) => MkSolverBuiltin (CHRBuiltin e s) b where
  toSolverBuiltin = CHRBuiltin
  fromSolverBuiltin (CHRBuiltin b) = cast b

class MkSolverPrio p p' where
  toSolverPrio :: p' -> p
  fromSolverPrio :: p -> Maybe p'

instance {-# INCOHERENT #-} MkSolverPrio p p where
  toSolverPrio = id
  fromSolverPrio = Just

instance {-# OVERLAPS #-}
         ( IsCHRPrio e p s
         -- , ExtrValVarKey (CHRPrio e s) ~ ExtrValVarKey p
         ) => MkSolverPrio (CHRPrio e s) p where
  toSolverPrio = CHRPrio
  fromSolverPrio (CHRPrio p) = cast p

class MkRule r where
  type SolverConstraint r :: *
  type SolverGuard r :: *
  type SolverBuiltin r :: *
  type SolverPrio r :: *
  -- | Make rule
  mkRule :: [SolverConstraint r] -> Int -> [SolverGuard r] -> [SolverConstraint r] -> [SolverBuiltin r] -> Maybe (SolverPrio r) -> r
  -- | Add guards to rule
  guardRule :: [SolverGuard r] -> r -> r
  -- | Add prio to rule
  prioritizeRule :: SolverPrio r -> r -> r

instance MkRule (Rule c g b p) where
  type SolverConstraint (Rule c g b p) = c
  type SolverGuard (Rule c g b p) = g
  type SolverBuiltin (Rule c g b p) = b
  type SolverPrio (Rule c g b p) = p
  mkRule = Rule
  guardRule g r = r {ruleGuard = ruleGuard r ++ g}
  prioritizeRule p r = r {rulePrio = Just p}

instance MkRule (CHRRule e s) where
  type SolverConstraint (CHRRule e s) = (CHRConstraint e s)
  type SolverGuard (CHRRule e s) = (CHRGuard e s)
  type SolverBuiltin (CHRRule e s) = ()
  type SolverPrio (CHRRule e s) = ()
  mkRule h l g b bi p = CHRRule $ mkRule h l g b bi p
  guardRule g (CHRRule r) = CHRRule $ guardRule g r
  prioritizeRule p (CHRRule r) = CHRRule $ prioritizeRule p r

infix   2 <==>, ==>, <\=>
infixl  1 |>
infixl  1 |!

(<==>>), (==>>) :: forall r c1 c2 c3 . (MkRule r, MkSolverConstraint (SolverConstraint r) c1, MkSolverConstraint (SolverConstraint r) c2, MkSolverBuiltin (SolverBuiltin r) c3)
  => [c1] -> ([c2], [c3]) -> r
-- | Construct simplification rule out of head, body, and builtin constraints
hs <==>>  (bs,bis) = mkRule (map toSolverConstraint hs) (length hs) [] (map toSolverConstraint bs) (map toSolverBuiltin bis) Nothing
-- | Construct propagation rule out of head, body, and builtin constraints
hs  ==>>  (bs,bis) = mkRule (map toSolverConstraint hs) 0 [] (map toSolverConstraint bs) (map toSolverBuiltin bis) Nothing

(<\=>>) :: forall r c1 c2 c3 . (MkRule r, MkSolverConstraint (SolverConstraint r) c1, MkSolverConstraint (SolverConstraint r) c2, MkSolverBuiltin (SolverBuiltin r) c3)
  => ([c1],[c1]) -> ([c2],[c3]) -> r
-- | Construct simpagation rule out of head, body, and builtin constraints
(hsprop,hssimp) <\=>>  (bs,bis) = mkRule (map toSolverConstraint $ hssimp ++ hsprop) (length hssimp) [] (map toSolverConstraint bs) (map toSolverBuiltin bis) Nothing

(<==>), (==>) :: forall r c1 c2 . (MkRule r, MkSolverConstraint (SolverConstraint r) c1, MkSolverConstraint (SolverConstraint r) c2)
  => [c1] -> [c2] -> r
-- | Construct simplification rule out of head and body constraints
hs <==>  bs = mkRule (map toSolverConstraint hs) (length hs) [] (map toSolverConstraint bs) [] Nothing
-- | Construct propagation rule out of head and body constraints
hs  ==>  bs = mkRule (map toSolverConstraint hs) 0 [] (map toSolverConstraint bs) [] Nothing

(<\=>) :: forall r c1 c2 . (MkRule r, MkSolverConstraint (SolverConstraint r) c1, MkSolverConstraint (SolverConstraint r) c2)
  => ([c1],[c1]) -> [c2] -> r
-- | Construct simpagation rule out of head and body constraints
(hsprop,hssimp) <\=>  bs = mkRule (map toSolverConstraint $ hssimp ++ hsprop) (length hssimp) [] (map toSolverConstraint bs) [] Nothing

-- | Add guards to rule
(|>) :: (MkRule r, MkSolverGuard (SolverGuard r) g') => r -> [g'] -> r
r |> g = guardRule (map toSolverGuard g) r

-- | Add priority to rule
(|!) :: (MkRule r, MkSolverPrio (SolverPrio r) p') => r -> p' -> r
r |! p = prioritizeRule (toSolverPrio p) r

-------------------------------------------------------------------------------------------
--- Instances: Serialize
-------------------------------------------------------------------------------------------

instance (Serialize c,Serialize g,Serialize b,Serialize p) => Serialize (Rule c g b p) where
  sput (Rule a b c d e f) = sput a >> sput b >> sput c >> sput d >> sput e >> sput f
  sget = liftM6 Rule sget sget sget sget sget sget

{-
instance (MkSolverConstraint (CHRConstraint e s) x', Serialize x') => Serialize (CHRConstraint e s) where
  sput x = maybe (panic "UHC.Util.CHR.Rule.Serialize.MkSolverConstraint.sput") sput $ fromSolverConstraint x
  sget = liftM toSolverConstraint sget
-}

{-
instance Serialize (CHRRule e s) where
  sput (CHRRule a) = sput a
  sget = liftM CHRRule sget
-}
