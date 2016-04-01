{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}

{-| Simple term language with some builtin guards and predicates 
 -}

module UHC.Util.CHR.Solve.TreeTrie.Examples.Term.AST
  ( Tm(..)
  , C(..)
  , G(..)
  -- , B(..)
  , P(..)
  , POp(..)
  , E
  , S
  
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

-- import           UHC.Util.Debug


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
tmIsVar (Tm_Var v) = Just v
tmIsVar _          = Nothing

instance PP Tm where
  pp (Tm_Var v   ) = pp v -- "v" >|< v
  pp (Tm_Con c as) = c >#< ppParensCommas as
  pp (Tm_Int i   ) = pp i

instance Serialize Tm

-- | Constraint
data C
  = C_Con String [Tm]
  | CB_Eq Tm Tm          -- ^ builtin: unification
  | CB_Fail              -- ^ explicit fail
  deriving (Show, Eq, Ord, Typeable, Generic)

instance PP C where
  pp (C_Con c as) = c >#< ppParensCommas as
  pp (CB_Eq x y ) = "unify" >#< ppParensCommas [x,y]
  pp (CB_Fail   ) = pp "fail"

instance Serialize C

{-
-- | Builtin
data B
  = B_Eq Tm Tm          -- ^ unification
  deriving (Show, Eq, Ord, Typeable, Generic)

instance PP B where
  pp (B_Eq x y) = "unify" >#< ppParensCommas [x,y]

instance Serialize B
-}

-- | Guard
data G
  = G_Eq Tm Tm          -- ^ check for equality
  deriving (Show, Typeable, Generic)

instance PP G where
  pp (G_Eq x y) = "is-eq" >#< ppParensCommas [x,y]

instance Serialize G

type instance TrTrKey Tm = Key
type instance TrTrKey C = Key
type instance TTKey Tm = Key
type instance TTKey C = Key

{-
instance MkSolverConstraint C C where
  toSolverConstraint = id
  fromSolverConstraint = Just
-}

instance TTKeyable Tm where
  toTTKeyParentChildren' o (Tm_Var v) | ttkoptsVarsAsWild o = (TT1K_Any, ttkChildren [])
                                      | otherwise           = (TT1K_One $ Key_Var v, ttkChildren [])
  toTTKeyParentChildren' o (Tm_Int i) = (TT1K_One $ Key_Int i, ttkChildren [])
  toTTKeyParentChildren' o (Tm_Con c as) = (TT1K_One $ Key_Str c, ttkChildren $ map (toTTKey' o) as)

instance TTKeyable C where
  -- Only necessary for non-builtin constraints
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

instance Bounded P where
  minBound = P_Tm $ Tm_Int $ unPrio $ minBound
  maxBound = P_Tm $ Tm_Int $ unPrio $ maxBound

type S = Map.Map Var Tm

type instance SubstVarKey S = Var
type instance SubstVarVal S = Tm

{-
sLkup :: Var -> S -> Maybe Tm
sLkup v s = Map.lookup v s >>= \t -> case t of
  Tm_Var v -> sLkup v s
  t        -> Just t
-}

instance VarLookupBase S Var Tm where
  varlookupSingletonWithMetaLev _ = Map.singleton
  varlookupEmpty = Map.empty

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
    CB_Eq x y  -> CB_Eq (s `varUpd` x) (s `varUpd` y)
    c          -> c

{-
instance VarUpdatable B S where
  s `varUpd` c = case c of
    B_Eq x y -> B_Eq (s `varUpd` x) (s `varUpd` y)
-}

instance VarExtractable Tm where
  varFreeSet (Tm_Var v) = Set.singleton v
  varFreeSet (Tm_Con _ as) = Set.unions $ map varFreeSet as
  varFreeSet _ = Set.empty

instance VarExtractable G where
  varFreeSet (G_Eq x y) = Set.unions [varFreeSet x, varFreeSet y]

instance VarExtractable C where
  varFreeSet (C_Con _ as) = Set.unions $ map varFreeSet as
  varFreeSet (CB_Eq x y ) = Set.unions [varFreeSet x, varFreeSet y]
  varFreeSet _            = Set.empty

instance CHREmptySubstitution S where
  chrEmptySubst = Map.empty

instance IsConstraint C where
  cnstrSolvesVia (C_Con _ _) = ConstraintSolvesVia_Rule
  cnstrSolvesVia (CB_Eq _ _) = ConstraintSolvesVia_Solve
  cnstrSolvesVia (CB_Fail  ) = ConstraintSolvesVia_Fail

instance IsCHRGuard E G S where

instance IsCHRConstraint E C S where

instance IsCHRPrio E P S where

instance IsCHRBacktrackPrio E P S where

-- instance IsCHRBuiltin E B S where

instance CHRCheckable E G S where
  chrCheckM e g =
    case g of
      G_Eq t1 t2 -> chrUnifyM CHRMatchHow_Equal e t1 t2

instance CHRMatchable E Tm S where
  chrUnifyM how e t1 t2 = do
      case (t1, t2) of
        (Tm_Con c1 as1, Tm_Con c2 as2) | c1 == c2 && length as1 == length as2 
                                                                   -> sequence_ (zipWith (chrMatchToM e) as1 as2)
        (Tm_Int i1    , Tm_Int i2    ) | i1 == i2                  -> chrMatchSuccess
        (Tm_Var v1    , Tm_Var v2    ) | v1 == v2                  -> chrMatchSuccess
        (Tm_Var v1    , t2           ) | how == CHRMatchHow_Equal  -> varContinue chrMatchFail (\t1 -> chrUnifyM how e t1 t2) v1
                                       | how >= CHRMatchHow_Match  -> varContinue (chrMatchBind v1 t2) (\t1 -> chrUnifyM how e t1 t2) v1
        (t1           , Tm_Var v2    ) | how == CHRMatchHow_Equal  -> varContinue chrMatchFail (chrUnifyM how e t1) v2
                                       | how == CHRMatchHow_Match  -> chrMatchWait v2
                                       | otherwise {- unify -}     -> varContinue (chrMatchBind v2 t1) (chrUnifyM how e t1) v2
        _                                                          -> chrMatchFail
    where
      varContinue = varlookupResolveAndContinueM tmIsVar chrMatchSubst

instance CHRMatchable E C S where
  chrMatchToM e c1 c2 = do
    case (c1, c2) of
      (C_Con c1 as1, C_Con c2 as2) | c1 == c2 && length as1 == length as2 
                                                 -> sequence_ (zipWith (chrMatchToM e) as1 as2)
      _                                          -> chrMatchFail
  chrBuiltinSolveM e b = case b of
    CB_Eq x y -> chrUnifyM CHRMatchHow_Unify e x y

instance CHRMatchable E P S where
  chrMatchToM e p1 p2 = do
    case (p1, p2) of
      (P_Tm   t1     , P_Tm   t2     ) -> chrMatchToM e t1  t2
      (P_Op _ p11 p12, P_Op _ p21 p22) -> chrMatchToM e p11 p21 >> chrMatchToM e p12 p22
      _                                -> chrMatchFail

{-
instance CHRBuiltinSolvable E C S where
  chrBuiltinSolveM e b = case b of
    CB_Eq x y -> chrUnifyM CHRMatchHow_Unify e x y

instance CHRBuiltinSolvable E B S where
  chrBuiltinSolveM e b = case b of
    B_Eq x y -> chrUnifyM CHRMatchHow_Unify e x y
-}

type instance CHRPrioEvaluatableVal Tm = Prio

instance CHRPrioEvaluatable E Tm S where
  chrPrioEval e s t = case t of
    Tm_Int i -> fromIntegral i
    Tm_Var v -> maybe minBound (chrPrioEval e s) $ varlookupResolveVar tmIsVar v s
    _        -> minBound

type instance CHRPrioEvaluatableVal P = Prio

instance CHRPrioEvaluatable E P S where
  chrPrioEval e s p = case p of
    P_Tm t -> chrPrioEval e s t
    P_Op o p1 p2 -> case o of
        POp_Add -> p1' + p2'
        POp_Sub -> p1' - p2'
        POp_Mul -> p1' * p2'
      where p1' = chrPrioEval e s p1
            p2' = chrPrioEval e s p2

-- instance M.IsCHRSolvable E C G S where

--------------------------------------------------------
-- leq example, backtrack prio specific

instance MBP.IsCHRSolvable E C G P P S where

instance MBP.MonoBacktrackPrio C G P P S E IO


-- mainMBP = MBP.runCHRMonoBacktrackPrioT (MBP.emptyCHRGlobState) (MBP.emptyCHRBackState) mbp2
