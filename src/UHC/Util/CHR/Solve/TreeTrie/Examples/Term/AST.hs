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
import           UHC.Util.Pretty as PP
import           UHC.Util.Serialize
import           UHC.Util.CHR.Key
import           UHC.Util.CHR.Base
import           UHC.Util.CHR.Rule
import           UHC.Util.Utils
import           UHC.Util.AssocL
import           UHC.Util.Lens
import           Data.Typeable
import           Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Applicative
import qualified UHC.Util.CHR.Solve.TreeTrie.Mono as M
import qualified UHC.Util.CHR.Solve.TreeTrie.MonoBacktrackPrio as MBP

import           UHC.Util.Debug


type Var = String -- Int

data Key
  = Key_Int     !Int            
  | Key_Var     !Var            
  | Key_Str     !String   
  | Key_Op      !POp   
  deriving (Eq, Ord, Show)

instance PP Key where
  pp (Key_Int i) = "ki" >|< ppParens i
  pp (Key_Var v) = "kv" >|< ppParens v
  pp (Key_Str s) = "ks" >|< ppParens s
  pp (Key_Op  o) = "ko" >|< ppParens o

-- | Terms
data Tm
  = Tm_Var Var              -- ^ variable (to be substituted)
  | Tm_Int Int              -- ^ int value (for arithmetic)
  | Tm_Con String [Tm]      -- ^ general term structure
  | Tm_Op  POp    [Tm]      -- ^ interpretable (when solving) term structure
  deriving (Show, Eq, Ord, Typeable, Generic)

tmIsVar :: Tm -> Maybe Var
tmIsVar (Tm_Var v) = Just v
tmIsVar _          = Nothing

instance PP Tm where
  pp (Tm_Var v        ) = pp v -- "v" >|< v
  pp (Tm_Con c []     ) = pp c
  pp (Tm_Con c as     ) = ppParens $ c >#< ppSpaces as
  pp (Tm_Op  o [a    ]) = ppParens $ o >#< a
  pp (Tm_Op  o [a1,a2]) = ppParens $ a1 >#< o >#< a2
  pp (Tm_Int i        ) = pp i

instance Serialize Tm

-- | Constraint
data C
  = C_Con String [Tm]
  | CB_Eq Tm Tm          -- ^ builtin: unification
  | CB_Ne Tm Tm          -- ^ builtin: non unification
  | CB_Fail              -- ^ explicit fail
  deriving (Show, Eq, Ord, Typeable, Generic)

instance PP C where
  pp (C_Con c as) = c >#< ppSpaces as
  pp (CB_Eq x y ) = "unify" >#< ppSpaces [x,y]
  pp (CB_Ne x y ) = "not-unify" >#< ppSpaces [x,y]
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
  | G_Ne Tm Tm          -- ^ check for inequality
  deriving (Show, Typeable, Generic)

instance PP G where
  pp (G_Eq x y) = "is-eq" >#< ppParensCommas [x,y]
  pp (G_Ne x y) = "is-ne" >#< ppParensCommas [x,y]

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
  toTTKeyParentChildren' o (Tm_Op op as) = (TT1K_One $ Key_Op op, ttkChildren $ map (toTTKey' o) as)

instance TTKeyable C where
  -- Only necessary for non-builtin constraints
  toTTKeyParentChildren' o (C_Con c as) = (TT1K_One $ Key_Str c, ttkChildren $ map (toTTKey' o) as)

type E = ()

-- | Binary operator
data POp
  = 
    -- binary
    PBOp_Add
  | PBOp_Sub
  | PBOp_Mul
  
    -- unary
  | PUOp_Abs
  deriving (Eq, Ord, Show, Generic)

instance PP POp where
  pp PBOp_Add = pp "+"
  pp PBOp_Sub = pp "-"
  pp PBOp_Mul = pp "*"
  pp PUOp_Abs = pp "abs"

data P
  = P_Tm Tm
  | P_Op POp P P
  deriving (Eq, Ord, Show, Generic)

instance PP P where
  pp (P_Tm t) = pp t
  pp (P_Op o x y) = (x >#< o >#< y)

instance Serialize POp

instance Serialize P

instance Bounded P where
  minBound = P_Tm $ Tm_Int $ fromIntegral $ unPrio $ minBound
  maxBound = P_Tm $ Tm_Int $ fromIntegral $ unPrio $ maxBound

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
  pp = ppAssocLH . Map.toList

type instance ExtrValVarKey G = Var
type instance ExtrValVarKey C = Var
type instance ExtrValVarKey Tm = Var
type instance ExtrValVarKey P = Var

type instance CHRMatchableKey S = Key

instance VarLookup S Var Tm where
  varlookupWithMetaLev _ = Map.lookup
  varlookupKeysSetWithMetaLev _ = Map.keysSet

instance VarLookupCmb S S where
  (|+>) = Map.union

instance VarUpdatable S S where
  varUpd = (|+>)

instance VarUpdatable Tm S where
  s `varUpd` t = case fromJust $ varlookupResolveVal tmIsVar t s <|> return t of
      Tm_Con c as -> Tm_Con c $ map (s `varUpd`) as
      Tm_Op  o as -> Tm_Op  o $ map (s `varUpd`) as
      t -> t

instance VarUpdatable P S where
  s `varUpd` p = case p of
    P_Tm t -> P_Tm (s `varUpd` t)
    P_Op o x1 x2 -> P_Op o (s `varUpd` x1) (s `varUpd` x2)

instance VarUpdatable G S where
  s `varUpd` G_Eq x y = G_Eq (s `varUpd` x) (s `varUpd` y)
  s `varUpd` G_Ne x y = G_Ne (s `varUpd` x) (s `varUpd` y)

instance VarUpdatable C S where
  s `varUpd` c = case c of
    C_Con c as -> C_Con c $ map (s `varUpd`) as
    CB_Eq x y  -> CB_Eq (s `varUpd` x) (s `varUpd` y)
    CB_Ne x y  -> CB_Ne (s `varUpd` x) (s `varUpd` y)
    c          -> c

{-
instance VarUpdatable B S where
  s `varUpd` c = case c of
    B_Eq x y -> B_Eq (s `varUpd` x) (s `varUpd` y)
-}

instance VarExtractable Tm where
  varFreeSet (Tm_Var v) = Set.singleton v
  varFreeSet (Tm_Con _ as) = Set.unions $ map varFreeSet as
  varFreeSet (Tm_Op  _ as) = Set.unions $ map varFreeSet as
  varFreeSet _ = Set.empty

instance VarExtractable G where
  varFreeSet (G_Eq x y) = Set.unions [varFreeSet x, varFreeSet y]
  varFreeSet (G_Ne x y) = Set.unions [varFreeSet x, varFreeSet y]

instance VarExtractable C where
  varFreeSet (C_Con _ as) = Set.unions $ map varFreeSet as
  varFreeSet (CB_Eq x y ) = Set.unions [varFreeSet x, varFreeSet y]
  varFreeSet _            = Set.empty

instance VarExtractable P where
  varFreeSet (P_Tm t) = varFreeSet t
  varFreeSet (P_Op o x1 x2) = Set.unions [varFreeSet x1, varFreeSet x2]

instance CHREmptySubstitution S where
  chrEmptySubst = Map.empty

instance IsConstraint C where
  cnstrSolvesVia (C_Con _ _) = ConstraintSolvesVia_Rule
  cnstrSolvesVia (CB_Eq _ _) = ConstraintSolvesVia_Solve
  cnstrSolvesVia (CB_Ne _ _) = ConstraintSolvesVia_Solve
  cnstrSolvesVia (CB_Fail  ) = ConstraintSolvesVia_Fail

instance IsCHRGuard E G S where

instance IsCHRConstraint E C S where

instance IsCHRPrio E P S where

instance IsCHRBacktrackPrio E P S where

instance CHRCheckable E G S where
  chrCheckM e g =
    case g of
      G_Eq t1 t2 -> chrUnifyM CHRMatchHow_Check e t1 t2
      G_Ne t1 t2 -> do
        menv <- getl chrmatcherstateEnv
        s <- getl chrmatcherstateVarLookup
        chrmatcherRun'
          (\e -> case e of {CHRMatcherFailure -> chrMatchSuccess; _ -> chrMatchFail})
          (\_ _ -> chrMatchFail)
          (chrCheckM e (G_Eq t1 t2)) menv s

instance CHRMatchable E Tm S where
  chrUnifyM how e t1 t2 = do
      menv <- getl chrmatcherstateEnv
      case (t1, t2) of
        (Tm_Con c1 as1, Tm_Con c2 as2) | c1 == c2 && length as1 == length as2 
                                                                          -> sequence_ (zipWith (chrUnifyM how e) as1 as2)
        (Tm_Op  o1 as1, Tm_Op  o2 as2) | how < CHRMatchHow_Unify && o1 == o2 && length as1 == length as2 
                                                                          -> sequence_ (zipWith (chrUnifyM how e) as1 as2)
        (Tm_Op  o1 as1, t2           ) | how == CHRMatchHow_Unify         -> evop o1 as1 >>= \t1 -> chrUnifyM how e t1 t2
        (t1           , Tm_Op  o2 as2) | how == CHRMatchHow_Unify         -> evop o2 as2 >>= \t2 -> chrUnifyM how e t1 t2
        (Tm_Int i1    , Tm_Int i2    ) | i1 == i2                         -> chrMatchSuccess
        (Tm_Var v1    , Tm_Var v2    ) | v1 == v2                         -> chrMatchSuccess
                                       | how == CHRMatchHow_Check         -> varContinue
                                                                               (varContinue (waitv v1 >> waitv v2) (chrUnifyM how e t1) v2)
                                                                               (\t1 -> varContinue (waitt t1 >> waitv v2) (\t2 -> chrUnifyM how e t1 t2) v2)
                                                                               v1
                                       where waitv v = unless (chrmatchenvMetaMayBind menv v) $ chrMatchWait v
                                             waitt (Tm_Var v) = waitv v
                                             waitt  _         = return ()
        (Tm_Var v1    , t2           ) | how == CHRMatchHow_Check         -> varContinue (if maybind then chrMatchFail else chrMatchWait v1) (\t1 -> chrUnifyM how e t1 t2) v1
                                       | how >= CHRMatchHow_Match && maybind
                                                                          -> varContinue (chrMatchBind menv v1 t2) (\t1 -> chrUnifyM how e t1 t2) v1
                                       | otherwise                        -> varContinue chrMatchFail {- chrMatchFailNoBinding -} (\t1 -> chrUnifyM how e t1 t2) v1
                                       where maybind = chrmatchenvMetaMayBind menv v1
        (t1           , Tm_Var v2    ) | how == CHRMatchHow_Check         -> varContinue (if maybind then chrMatchFail else chrMatchWait v2) (chrUnifyM how e t1) v2
                                       | how == CHRMatchHow_MatchAndWait  -> varContinue (chrMatchWait v2) (chrUnifyM how e t1) v2
                                       | how == CHRMatchHow_Unify && maybind
                                                                          -> varContinue (chrMatchBind menv v2 t1) (chrUnifyM how e t1) v2
                                       | otherwise                        -> varContinue chrMatchFail {- chrMatchFailNoBinding -} (chrUnifyM how e t1) v2
                                       where maybind = chrmatchenvMetaMayBind menv v2
        _                                                                 -> chrMatchFail
    where
      varContinue = varlookupResolveAndContinueM tmIsVar chrMatchSubst
      evop o xs = do
          xs <- forM xs ev 
          case (o, xs) of
            (PUOp_Abs, [Tm_Int x]) -> ret $ abs x
            (PBOp_Add, [Tm_Int x, Tm_Int y]) -> ret $ x + y
            (PBOp_Sub, [Tm_Int x, Tm_Int y]) -> ret $ x - y
            (PBOp_Mul, [Tm_Int x, Tm_Int y]) -> ret $ x * y
        where ret x = return $ Tm_Int x
      ev x = case x of
          Tm_Int _    -> return x
          Tm_Var v    -> varContinue chrMatchFailNoBinding ev v
          Tm_Op  o xs -> evop o xs
          _           -> chrMatchFail

instance CHRMatchable E C S where
  chrUnifyM how e c1 c2 = do
    case (c1, c2) of
      (C_Con c1 as1, C_Con c2 as2) | c1 == c2 && length as1 == length as2 
                                                 -> sequence_ (zipWith (chrUnifyM how e) as1 as2)
      _                                          -> chrMatchFail
  chrBuiltinSolveM e b = case b of
    CB_Eq x y -> chrUnifyM CHRMatchHow_Unify e x y
    CB_Ne x y -> do -- chrUnifyM CHRMatchHow_Unify e x y
        menv <- getl chrmatcherstateEnv
        s <- getl chrmatcherstateVarLookup
        chrmatcherRun' (\_ -> chrMatchSuccess) (\_ _ -> chrMatchFail) (chrBuiltinSolveM e (CB_Eq x y)) menv s

instance CHRMatchable E P S where
  chrUnifyM how e p1 p2 = do
    case (p1, p2) of
      (P_Tm   t1     , P_Tm   t2     ) -> chrUnifyM how e t1  t2
      (P_Op _ p11 p12, P_Op _ p21 p22) -> chrUnifyM how e p11 p21 >> chrUnifyM how e p12 p22
      _                                -> chrMatchFail

type instance CHRPrioEvaluatableVal Tm = Prio

instance CHRPrioEvaluatable E Tm S where
  chrPrioEval e s t = case t of
    Tm_Int i -> fromIntegral i
    Tm_Var v -> maybe minBound (chrPrioEval e s) $ varlookupResolveVar tmIsVar v s
    _        -> minBound
  chrPrioLift = Tm_Int . fromIntegral

type instance CHRPrioEvaluatableVal P = Prio

instance CHRPrioEvaluatable E P S where
  chrPrioEval e s p = case p of
    P_Tm t -> chrPrioEval e s t
    P_Op o p1 p2 -> case o of
        PBOp_Add -> p1' + p2'
        PBOp_Sub -> p1' - p2'
        PBOp_Mul -> p1' * p2'
      where p1' = chrPrioEval e s p1
            p2' = chrPrioEval e s p2
  chrPrioLift = P_Tm . chrPrioLift

-- instance M.IsCHRSolvable E C G S where

--------------------------------------------------------
-- leq example, backtrack prio specific

instance MBP.IsCHRSolvable E C G P P S where

instance MBP.MonoBacktrackPrio C G P P S E IO


-- mainMBP = MBP.runCHRMonoBacktrackPrioT (MBP.emptyCHRGlobState) (MBP.emptyCHRBackState) mbp2
