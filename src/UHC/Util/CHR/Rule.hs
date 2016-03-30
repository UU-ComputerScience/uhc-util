{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FunctionalDependencies, UndecidableInstances, ExistentialQuantification, ScopedTypeVariables, StandaloneDeriving #-}
-- {-# LANGUAGE AllowAmbiguousTypes #-}

-------------------------------------------------------------------------------------------
--- Constraint Handling Rules
-------------------------------------------------------------------------------------------

{- |
The representation of rules, which should allow an implementation of:

"A Flexible Search Framework for CHR", Leslie De Koninck, Tom Schrijvers, and Bart Demoen.
http://link.springer.com/10.1007/978-3-540-92243-8_2

-}

module UHC.Util.CHR.Rule
  ( RuleBodyAlt(..)
  
  , Rule(..)
  , ruleBody, ruleBody'
  , ruleBodyBuiltin
  , ruleSz
  
  -- , CHRRule(..)
  
  , (/\)
  , (\/)
  , (\!)
  , (<=>>), (==>>), (<\>>)
  , (<==>), (<=>), (==>), (<\>)
  , (|>), (=|)
  , (=!), (=!!)
  , (=@), (@=)
  
  , MkSolverConstraint(..)
  , MkSolverGuard(..)
  , MkSolverBuiltin(..)
  , MkSolverPrio(..)
  
  , MkRule(mkRule)
  )
  where

import qualified UHC.Util.TreeTrie as TreeTrie
import           UHC.Util.CHR.Base
import           UHC.Util.VarMp
import           UHC.Util.Utils
import           Data.Monoid
import           Data.List as List
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

data RuleBodyAlt cnstr builtin prio
  = RuleBodyAlt
      { rbodyaltBacktrackPrio       :: !(Maybe prio)        -- ^ optional backtrack priority, if absent it is inherited from the active backtrack prio
      , rbodyaltBody                :: ![cnstr]             -- ^ body constraints to be dealt with by rules
      , rbodyaltBodyBuiltin         :: ![builtin]           -- ^ builtin constraints to be dealt with by builtin solving
      }
  deriving (Typeable)

-- | A CHR (rule) consist of head (simplification + propagation, boundary indicated by an Int), guard, and a body. All may be empty, but not all at the same time.
data Rule cnstr guard builtin prio
  = Rule
      { ruleHead            :: ![cnstr]
      , ruleSimpSz          :: !Int                -- ^ length of the part of the head which is the simplification part
      , ruleGuard           :: ![guard]    
      , ruleBodyAlts        :: ![RuleBodyAlt cnstr builtin prio]
{-        
      , ruleBody            :: ![cnstr]
      , ruleBodyBuiltin     :: ![builtin]
-}
      , ruleBacktrackPrio   :: !(Maybe prio)       -- ^ backtrack priority, should be something which can be substituted with the actual prio, later to be referred to at backtrack prios of alternatives
      , rulePrio            :: !(Maybe prio)       -- ^ rule priority, to choose between rules with equal backtrack priority
      , ruleName            :: (Maybe String)
      }
  deriving (Typeable)

-- | Backwards compatibility: if only one alternative, extract it, ignore other alts
ruleBody' :: Rule c g b p -> ([c],[b])
ruleBody' (Rule {ruleBodyAlts = (a:_)}) = (rbodyaltBody a, rbodyaltBodyBuiltin a)
ruleBody' (Rule {ruleBodyAlts = []   }) = ([], [])

-- | Backwards compatibility: if only one alternative, extract it, ignore other alts
ruleBody :: Rule c g b p -> [c]
ruleBody = fst . ruleBody'
{-# INLINE ruleBody #-}

-- | Backwards compatibility: if only one alternative, extract it, ignore other alts
ruleBodyBuiltin :: Rule c g b p -> [b]
ruleBodyBuiltin = snd . ruleBody'
{-# INLINE ruleBodyBuiltin #-}

-- | Total nr of cnstrs in rule
ruleSz :: Rule c g b p -> Int
ruleSz = length . ruleHead
{-# INLINE ruleSz #-}

emptyCHRGuard :: [a]
emptyCHRGuard = []

instance Show (Rule c g b p) where
  show _ = "Rule"

instance (PP c, PP g, PP p, PP b) => PP (Rule c g b p) where
  pp chr = ppMbPre (\p -> p >#< "::") rPrio $ ppMbPre (\n -> pp n >#< "@") (ruleName chr) $ base
    where base = case chr of
            Rule {} | ruleSimpSz chr == 0                        -> ppChr ([ppL (ruleHead chr), pp  "==>"] ++ ppGB (ruleGuard chr) body)
                    | ruleSimpSz chr == length (ruleHead chr)    -> ppChr ([ppL (ruleHead chr), pp "<==>"] ++ ppGB (ruleGuard chr) body)
                    | length (ruleHead chr) == 0                 -> ppChr (ppGB (ruleGuard chr) body)
                    | otherwise                                  -> ppChr ([ppL (drop (ruleSimpSz chr) (ruleHead chr)), pp "\\", ppL (take (ruleSimpSz chr) (ruleHead chr)), pp "<\\=>"] ++ ppGB (ruleGuard chr) body)
          rPrio = case (ruleBacktrackPrio chr, rulePrio chr) of
            (Nothing, Nothing) -> Nothing
            (Just bp, Just rp) -> Just $ ppParensCommas [   bp ,    rp ]
            (Just bp, _      ) -> Just $ ppParensCommas [pp bp , pp "_"]
            (_      , Just rp) -> Just $ ppParensCommas [pp "_", pp rp ]
          body = ppSpaces $ intersperse (pp "\\/") $ map ppAlt $ ruleBodyAlts chr
            where ppAlt a = ppMbPre (\p -> ppParens p >#< "::") (rbodyaltBacktrackPrio a) $ ppL $ map pp (rbodyaltBody a) ++ map pp (rbodyaltBodyBuiltin a)
          ppGB g@(_:_) b = [ppL g, "|" >#< b] -- g b = ppListPre (\g -> ppL g >#< "|") g
          ppGB []      b = [b]
          -- ppL [x] = pp x
          ppL xs  = ppCommas' xs -- ppParensCommasBlock xs
          ppChr l = ppSpaces l -- vlist l -- ppCurlysBlock

type instance TTKey (Rule cnstr guard builtin prio) = TTKey cnstr
type instance TreeTrie.TrTrKey (Rule cnstr guard builtin prio) = TTKey cnstr

instance (TTKeyable cnstr) => TTKeyable (Rule cnstr guard builtin prio) where
  toTTKey' o chr = toTTKey' o $ head $ ruleHead chr

-------------------------------------------------------------------------------------------
--- Existentially quantified Rule representations to allow for mix of arbitrary universes
-------------------------------------------------------------------------------------------

{-
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
-}

-------------------------------------------------------------------------------------------
--- Var instances
-------------------------------------------------------------------------------------------

type instance ExtrValVarKey (Rule c g b p) = ExtrValVarKey c
type instance ExtrValVarKey (RuleBodyAlt c b p) = ExtrValVarKey c

-- TBD: should vars be extracted from prio and builtin as well?
instance (VarExtractable c) => VarExtractable (RuleBodyAlt c b p) where
  varFreeSet          (RuleBodyAlt {rbodyaltBody=b})
    = Set.unions $ concat [map varFreeSet b]

-- TBD: should vars be extracted from prio as well?
instance (VarExtractable c, VarExtractable g, ExtrValVarKey c ~ ExtrValVarKey g) => VarExtractable (Rule c g b p) where
  varFreeSet          (Rule {ruleHead=h, ruleGuard=g, ruleBodyAlts=b})
    = Set.unions $ concat [map varFreeSet h, map varFreeSet g, map varFreeSet b]

instance (VarUpdatable c s, VarUpdatable b s, VarUpdatable p s) => VarUpdatable (RuleBodyAlt c b p) s where
  varUpd s r@(RuleBodyAlt {rbodyaltBacktrackPrio=p, rbodyaltBody=b, rbodyaltBodyBuiltin=bi})
    = r {rbodyaltBacktrackPrio = fmap (varUpd s) p, rbodyaltBody = map (varUpd s) b, rbodyaltBodyBuiltin = map (varUpd s) bi}

instance (VarUpdatable c s, VarUpdatable g s, VarUpdatable b s, VarUpdatable p s) => VarUpdatable (Rule c g b p) s where
  varUpd s r@(Rule {ruleHead=h, ruleGuard=g, ruleBodyAlts=b})
    = r {ruleHead = map (varUpd s) h, ruleGuard = map (varUpd s) g, ruleBodyAlts = map (varUpd s) b}

-------------------------------------------------------------------------------------------
--- Construction: Rule
-------------------------------------------------------------------------------------------

class MkSolverConstraint c c' where
  toSolverConstraint :: c' -> c
  fromSolverConstraint :: c -> Maybe c'

instance {-# INCOHERENT #-} MkSolverConstraint c c where
  toSolverConstraint = id
  fromSolverConstraint = Just

{-  
instance {-# OVERLAPS #-}
         ( IsCHRConstraint e c s
         , TTKey (CHRConstraint e s) ~ TTKey c
         , ExtrValVarKey (CHRConstraint e s) ~ ExtrValVarKey c
         ) => MkSolverConstraint (CHRConstraint e s) c where
  toSolverConstraint = CHRConstraint
  fromSolverConstraint (CHRConstraint c) = cast c
-}

class MkSolverGuard g g' where
  toSolverGuard :: g' -> g
  fromSolverGuard :: g -> Maybe g'

instance {-# INCOHERENT #-} MkSolverGuard g g where
  toSolverGuard = id
  fromSolverGuard = Just

{-
instance {-# OVERLAPS #-}
         ( IsCHRGuard e g s
         , ExtrValVarKey (CHRGuard e s) ~ ExtrValVarKey g
         ) => MkSolverGuard (CHRGuard e s) g where
  toSolverGuard = CHRGuard
  fromSolverGuard (CHRGuard g) = cast g
-}

class MkSolverBuiltin b b' where
  toSolverBuiltin :: b' -> b
  fromSolverBuiltin :: b -> Maybe b'

instance {-# INCOHERENT #-} MkSolverBuiltin b b where
  toSolverBuiltin = id
  fromSolverBuiltin = Just

{-
instance {-# OVERLAPS #-}
         ( IsCHRBuiltin e b s
         -- , ExtrValVarKey (CHRBuiltin e s) ~ ExtrValVarKey b
         ) => MkSolverBuiltin (CHRBuiltin e s) b where
  toSolverBuiltin = CHRBuiltin
  fromSolverBuiltin (CHRBuiltin b) = cast b
-}

class MkSolverPrio p p' where
  toSolverPrio :: p' -> p
  fromSolverPrio :: p -> Maybe p'

instance {-# INCOHERENT #-} MkSolverPrio p p where
  toSolverPrio = id
  fromSolverPrio = Just

{-
instance {-# OVERLAPS #-}
         ( IsCHRPrio e p s
         -- , ExtrValVarKey (CHRPrio e s) ~ ExtrValVarKey p
         ) => MkSolverPrio (CHRPrio e s) p where
  toSolverPrio = CHRPrio
  fromSolverPrio (CHRPrio p) = cast p
-}

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
  -- | Add backtrack prio to rule
  prioritizeBacktrackRule :: SolverPrio r -> r -> r
  -- | Add label/name to rule
  labelRule :: String -> r -> r

instance MkRule (Rule c g b p) where
  type SolverConstraint (Rule c g b p) = c
  type SolverGuard (Rule c g b p) = g
  type SolverBuiltin (Rule c g b p) = b
  type SolverPrio (Rule c g b p) = p
  mkRule h l g b bi p = Rule h l g [RuleBodyAlt Nothing b bi] Nothing p Nothing
  guardRule g r = r {ruleGuard = ruleGuard r ++ g}
  prioritizeRule p r = r {rulePrio = Just p}
  prioritizeBacktrackRule p r = r {ruleBacktrackPrio = Just p}
  labelRule l r = r {ruleName = Just l}

{-
instance MkRule (CHRRule e s) where
  type SolverConstraint (CHRRule e s) = (CHRConstraint e s)
  type SolverGuard (CHRRule e s) = (CHRGuard e s)
  type SolverBuiltin (CHRRule e s) = ()
  type SolverPrio (CHRRule e s) = ()
  mkRule h l g b bi p = CHRRule $ mkRule h l g b bi p
  guardRule g (CHRRule r) = CHRRule $ guardRule g r
  prioritizeRule p (CHRRule r) = CHRRule $ prioritizeRule p r
  prioritizeBacktrackRule p (CHRRule r) = CHRRule $ prioritizeBacktrackRule p r
  labelRule p (CHRRule r) = CHRRule $ labelRule p r
-}

infixl  6 /\
infixl  5 \!
infixr  4 \/
infix   3 <==>, <=>, ==>, <\>
infixl  2 |>, =|
infixl  2 =!, =!!
infixl  2 =@
infixr  1 @=

-- | Rule body backtracking alternative
(/\) :: [c] -> [b] -> RuleBodyAlt c b p
c /\ b = RuleBodyAlt Nothing c b

-- | Rule body backtracking alternatives
(\/) :: [RuleBodyAlt c b p] -> [RuleBodyAlt c b p] -> [RuleBodyAlt c b p]
(\/) = (++)

-- | Add backtrack priority to body alternative
(\!) :: RuleBodyAlt c b p -> p -> RuleBodyAlt c b p
r \! p = r {rbodyaltBacktrackPrio = Just p}

(<=>>), (==>>) :: forall r c1 c2 c3 . (MkRule r, MkSolverConstraint (SolverConstraint r) c1, MkSolverConstraint (SolverConstraint r) c2, MkSolverBuiltin (SolverBuiltin r) c3)
  => [c1] -> ([c2], [c3]) -> r
-- | Construct simplification rule out of head, body, and builtin constraints
hs <=>>  (bs,bis) = mkRule (map toSolverConstraint hs) (length hs) [] (map toSolverConstraint bs) (map toSolverBuiltin bis) Nothing
-- | Construct propagation rule out of head, body, and builtin constraints
hs  ==>>  (bs,bis) = mkRule (map toSolverConstraint hs) 0 [] (map toSolverConstraint bs) (map toSolverBuiltin bis) Nothing

(<\>>) :: forall r c1 c2 c3 . (MkRule r, MkSolverConstraint (SolverConstraint r) c1, MkSolverConstraint (SolverConstraint r) c2, MkSolverBuiltin (SolverBuiltin r) c3)
  => ([c1],[c1]) -> ([c2],[c3]) -> r
-- | Construct simpagation rule out of head, body, and builtin constraints
(hsprop,hssimp) <\>>  (bs,bis) = mkRule (map toSolverConstraint $ hssimp ++ hsprop) (length hssimp) [] (map toSolverConstraint bs) (map toSolverBuiltin bis) Nothing

{-# DEPRECATED (<==>) "Use (<=>)" #-}
(<==>), (==>), (<=>) :: forall r c1 c2 . (MkRule r, MkSolverConstraint (SolverConstraint r) c1, MkSolverConstraint (SolverConstraint r) c2)
  => [c1] -> [c2] -> r
-- | Construct simplification rule out of head and body constraints
hs <==>  bs = mkRule (map toSolverConstraint hs) (length hs) [] (map toSolverConstraint bs) [] Nothing
-- | Construct propagation rule out of head and body constraints
hs  ==>  bs = mkRule (map toSolverConstraint hs) 0 [] (map toSolverConstraint bs) [] Nothing
(<=>) = (<==>)

(<\>) :: forall r c1 c2 . (MkRule r, MkSolverConstraint (SolverConstraint r) c1, MkSolverConstraint (SolverConstraint r) c2)
  => ([c1],[c1]) -> [c2] -> r
-- | Construct simpagation rule out of head and body constraints
(hsprop,hssimp) <\>  bs = mkRule (map toSolverConstraint $ hssimp ++ hsprop) (length hssimp) [] (map toSolverConstraint bs) [] Nothing

{-# DEPRECATED (|>) "Use (=|)" #-}
-- | Add guards to rule
(|>), (=|) :: (MkRule r, MkSolverGuard (SolverGuard r) g') => r -> [g'] -> r
r |> g = guardRule (map toSolverGuard g) r
(=|) = (|>)
{-# INLINE (=|) #-}

-- | Add priority to rule
(=!!) :: (MkRule r, MkSolverPrio (SolverPrio r) p') => r -> p' -> r
r =!! p = prioritizeRule (toSolverPrio p) r

-- | Add backtrack priority to rule
(=!) :: (MkRule r, MkSolverPrio (SolverPrio r) p') => r -> p' -> r
r =! p = prioritizeBacktrackRule (toSolverPrio p) r

-- | Add label to rule
(=@) :: (MkRule r) => r -> String -> r
r =@ l = labelRule l r

-- | Add label to rule
(@=) :: (MkRule r) => String -> r -> r
l @= r = r =@ l
{-# INLINE (@=) #-}

-------------------------------------------------------------------------------------------
--- Instances: Serialize
-------------------------------------------------------------------------------------------

instance (Serialize c,Serialize b,Serialize p) => Serialize (RuleBodyAlt c b p) where
  sput (RuleBodyAlt a b c) = sput a >> sput b >> sput c
  sget = liftM3 RuleBodyAlt sget sget sget

instance (Serialize c,Serialize g,Serialize b,Serialize p) => Serialize (Rule c g b p) where
  sput (Rule a b c d e f g) = sput a >> sput b >> sput c >> sput d >> sput e >> sput f >> sput g
  sget = liftM7 Rule sget sget sget sget sget sget sget

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
