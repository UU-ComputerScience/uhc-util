{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}

{-| Simple term language with some builtin guards and predicates 
 -}

module UHC.Util.CHR.Solve.TreeTrie.Examples.Term.AST
  ( Tm(..)
  , C(..)
  , G(..)
  , B(..)
  , P(..)
  , POp(..)
  , E
  
  , Var
  )
  where

import           UHC.Util.VarLookup
import           UHC.Util.Substitutable
import           UHC.Util.TreeTrie
import           UHC.Util.Pretty
import           UHC.Util.Serialize
import           UHC.Util.CHR.Key
import           UHC.Util.CHR.Base
import           UHC.Util.CHR.Rule
import           UHC.Util.Utils
import           UHC.Util.AssocL
import           Data.Typeable
import           Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Control.Monad.IO.Class
import           Control.Applicative
import qualified UHC.Util.CHR.Solve.TreeTrie.Mono as M
import qualified UHC.Util.CHR.Solve.TreeTrie.MonoBacktrackPrio as MBP


type Var = String -- Int

data Key
  = Key_Int     !Int            
  | Key_Var     !Var            
  | Key_Str     !String   
  deriving (Eq, Ord, Show)

instance PP Key where
  pp (Key_Int i) = "ki" >|< ppParens i
  pp (Key_Var v) = "kv" >|< ppParens v
  pp (Key_Str s) = "ks" >|< ppParens s

-- | Terms
data Tm
  = Tm_Var Var              -- ^ variable (to be substituted)
  | Tm_Int Int              -- ^ int value (for arithmetic)
  | Tm_Con String [Tm]
  deriving (Show, Eq, Ord, Typeable, Generic)

tmIsVar :: Tm -> Maybe Var
tmIsVar = \t -> case t of {Tm_Var v -> Just v; _ -> Nothing}

instance PP Tm where
  pp (Tm_Var v   ) = "v" >|< v
  pp (Tm_Con c as) = c >#< ppParensCommas as
  pp (Tm_Int i   ) = pp i

instance Serialize Tm

-- | Constraint
data C
  = C_Con String [Tm]
  deriving (Show, Eq, Ord, Typeable, Generic)

instance PP C where
  pp (C_Con c as) = c >#< ppParensCommas as

instance Serialize C

-- | Builtin
data B
  = B_Eq Tm Tm          -- ^ unification
  deriving (Show, Eq, Ord, Typeable, Generic)

instance PP B where
  pp (B_Eq x y) = "eq" >#< ppParensCommas [x,y]

instance Serialize B

-- | Guard
data G
  = G_Eq Tm Tm          -- ^ check for equality
  deriving (Show, Typeable, Generic)

instance PP G where
  pp (G_Eq x y) = "eq" >#< ppParensCommas [x,y]

instance Serialize G

type instance TrTrKey Tm = Key
type instance TrTrKey C = Key
type instance TTKey Tm = Key
type instance TTKey C = Key

instance MkSolverConstraint C C where
  toSolverConstraint = id
  fromSolverConstraint = Just

instance TTKeyable Tm where
  toTTKeyParentChildren' o (Tm_Var v) | ttkoptsVarsAsWild o = (TT1K_Any, ttkChildren [])
                                      | otherwise           = (TT1K_One $ Key_Var v, ttkChildren [])
  toTTKeyParentChildren' o (Tm_Int i) = (TT1K_One $ Key_Int i, ttkChildren [])
  toTTKeyParentChildren' o (Tm_Con c as) = (TT1K_One $ Key_Str c, ttkChildren $ map (toTTKey' o) as)

instance TTKeyable C where
  toTTKeyParentChildren' o (C_Con c as) = (TT1K_One $ Key_Str c, ttkChildren $ map (toTTKey' o) as)

type E = ()

data POp
  = POp_Add | POp_Sub | POp_Mul
  deriving (Eq, Ord, Show, Generic)

data P
  = P_Tm Tm
  | P_Op POp P P
  deriving (Eq, Ord, Show, Generic)

instance PP POp where
  pp POp_Add = pp "+"
  pp POp_Sub = pp "-"
  pp POp_Mul = pp "*"

instance PP P where
  pp (P_Tm t) = pp t
  pp (P_Op o x y) = (x >#< o >#< y)

instance Serialize POp

instance Serialize P

type S = Map.Map Var Tm

type instance SubstVarKey S = Var
type instance SubstVarVal S = Tm

{-
sLkup :: Var -> S -> Maybe Tm
sLkup v s = Map.lookup v s >>= \t -> case t of
  Tm_Var v -> sLkup v s
  t        -> Just t
-}

instance SubstMake S where
  substSingleton = Map.singleton
  substEmpty = Map.empty

instance PP S where
  pp = ppAssocL . Map.toList

type instance ExtrValVarKey G = Var
type instance ExtrValVarKey C = Var
type instance ExtrValVarKey Tm = Var
type instance CHRMatchableKey S = Key

instance VarLookup S Var Tm where
  varlookupWithMetaLev _ = Map.lookup

instance VarLookupCmb S S where
  (|+>) = Map.union

instance VarUpdatable S S where
  varUpd = (|+>)

instance VarUpdatable Tm S where
  s `varUpd` t = case fromJust $ varlookupResolveVal tmIsVar t s <|> return t of
      Tm_Con c as -> Tm_Con c $ map (s `varUpd`) as
      t -> t

instance VarUpdatable P S where
  s `varUpd` p = case p of
    P_Tm t -> P_Tm (s `varUpd` t)
    P_Op o x1 x2 -> P_Op o (s `varUpd` x1) (s `varUpd` x2)

instance VarUpdatable G S where
  s `varUpd` G_Eq x y = G_Eq (s `varUpd` x) (s `varUpd` y)

instance VarUpdatable C S where
  s `varUpd` c = case c of
    C_Con c as -> C_Con c $ map (s `varUpd`) as

instance VarUpdatable B S where
  s `varUpd` c = case c of
    B_Eq x y -> B_Eq (s `varUpd` x) (s `varUpd` y)

instance VarExtractable Tm where
  varFreeSet (Tm_Var v) = Set.singleton v
  varFreeSet (Tm_Con _ as) = Set.unions $ map varFreeSet as
  varFreeSet _ = Set.empty

instance VarExtractable G where
  varFreeSet (G_Eq x y) = Set.unions [varFreeSet x, varFreeSet y]

instance VarExtractable C where
  varFreeSet (C_Con _ as) = Set.unions $ map varFreeSet as

instance CHREmptySubstitution S where
  chrEmptySubst = Map.empty

instance IsConstraint C where
  cnstrSolvesVia (C_Con _ _) = ConstraintSolvesVia_Rule

instance IsCHRGuard E G S where

instance IsCHRConstraint E C S where

instance IsCHRPrio E P S where

instance IsCHRBuiltin E B S where

instance CHRCheckable E G S where
  chrCheck _ s g =
    case s `varUpd` g of
      G_Eq t1 t2 | t1 == t2 -> return chrEmptySubst
      _                     -> Nothing

instance CHRMatchable E Tm S where
  chrMatchTo _ s t1 t2 = case (s `varUpd` t1, s `varUpd` t2) of
      (Tm_Con c1 as1, Tm_Con c2 as2) | c1 == c2 -> panic "CHRMatchable E Tm S" -- return chrEmptySubst -- TBD
      (Tm_Int i1    , Tm_Int i2    ) | i1 == i2 -> return chrEmptySubst
      (Tm_Var v1    , Tm_Var v2    ) | v1 == v2 -> return chrEmptySubst
      (Tm_Var v1    , t2           )            -> return $ Map.singleton v1 t2
      -- (t1       , Tm_Var v2)            -> waitForBinding v2 >> return $ Nothing
      _                                 -> Nothing

{-
  chrMatchToM _ t1 t2 = do
    t1 <- chrMatchVarUpd t1
    t2 <- chrMatchVarUpd t2
    case (t1, t2) of
      (Tm_Str s1, Tm_Str s2) | s1 == s2 -> return ()
      (Tm_Var v1, Tm_Var v2) | v1 == v2 -> return ()
      (Tm_Var v1, t2       )            -> chrMatchBind v1 t2
      (t1       , Tm_Var v2)            -> chrMatchWait v2
      _                                 -> chrMatchFail
-}

{-
instance CHRMatchable E Tm S where
  chrMatchToM _ s t1 t2 = case (s `varUpd` t1, s `varUpd` t2) of
      (Tm_Str s1, Tm_Str s2) | s1 == s2 -> return $ return chrEmptySubst
      (Tm_Var v1, Tm_Var v2) | v1 == v2 -> return $ return chrEmptySubst
      (Tm_Var v1, t2       )            -> return $ return $ Map.singleton v1 t2
      -- (t1       , Tm_Var v2)            -> waitForBinding v2 >> return $ Nothing
      _                                 -> return Nothing
-}

instance CHRMatchable E C S where
  chrMatchTo e s c1 c2 = case (s `varUpd` c1, s `varUpd` c2) of
      (C_Con c1 as1, C_Con c2 as2) | c1 == c2 -> panic "CHRMatchable E C S" -- return chrEmptySubst -- TBD

{-
  chrMatchToM e c1 c2 = do
    c1 <- chrMatchVarUpd c1
    c2 <- chrMatchVarUpd c2
    case (c1, c2) of
      (C_Leq x1 y1, C_Leq x2 y2) -> m x1 y1 x2 y2
      (C_Eq x1 y1 , C_Eq x2 y2 ) -> m x1 y1 x2 y2
      _ -> chrMatchFail
    where
      m x1 y1 x2 y2 = do
        chrMatchToM e x1 x2
        chrMatchToM e y1 y2
-}

instance CHRBuiltinSolvable E B S where
  chrBuiltinSolve e s b = case s `varUpd` b of
    B_Eq x y -> panic "CHRBuiltinSolvable E B S" -- Nothing -- TBD

-- type instance CHRPrioEvaluatableVal Tm = Int

{-
instance CHRPrioEvaluatable E Tm S where
  chrPrioCompare e (s1,p1) (s2,p2) = case (s1 `varUpd` p1, s2 `varUpd` p2) of
    (Tm_Str s1, Tm_Str s2) -> (sum $ map fromEnum s1) `compare` (sum $ map fromEnum s2)
    (t1, t2) -> t1 `compare` t2
-}

-- type instance CHRPrioEvaluatableVal P = Int

instance CHRPrioEvaluatable E P S where
  chrPrioCompare e (s1,p1) (s2,p2) = panic "CHRPrioEvaluatable E P S"
{-
  chrPrioCompare e (s1,p1) (s2,p2) = case (s1 `varUpd` p1, s2 `varUpd` p2) of
    (P_Tm t1, P_Tm t2) -> chrPrioCompare e (s1,t1) (s2,t2)
    (t1, t2) -> t1 `compare` t2
-}

instance M.IsCHRSolvable E C G S where

--------------------------------------------------------
-- leq example, backtrack prio specific

instance MBP.IsCHRSolvable E C G B P S where

instance MBP.MonoBacktrackPrio C G B P S E IO


-- mainMBP = MBP.runCHRMonoBacktrackPrioT (MBP.emptyCHRGlobState) (MBP.emptyCHRBackState) mbp2
