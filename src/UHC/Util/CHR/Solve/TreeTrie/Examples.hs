{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}

module UHC.Util.CHR.Solve.TreeTrie.Examples 
  (
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
import           Data.Typeable
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Control.Monad.IO.Class
import qualified UHC.Util.CHR.Solve.TreeTrie.Mono as M
import qualified UHC.Util.CHR.Solve.TreeTrie.MonoBacktrackPrio as MBP

--------------------------------------------------------
-- leq example, e.g. see https://sicstus.sics.se/sicstus/docs/3.12.4/html/sicstus/CHR-Introductory-Examples.html
type Var = Int

data Key
  = Key_Int     !Int            
  | Key_Var     !Var            
  | Key_Str     !String   
  deriving (Eq, Ord, Show)

instance PP Key where
  pp (Key_Int i) = "ki" >|< ppParens i
  pp (Key_Var v) = "kv" >|< ppParens v
  pp (Key_Str s) = "ks" >|< ppParens s

data Tm
  = Tm_Var Var
  | Tm_Str String
  deriving (Show, Eq, Ord, Typeable, Generic)

instance PP Tm where
  pp (Tm_Var v) = "v" >|< v
  pp (Tm_Str s) = pp s

instance Serialize Tm

data C
  = C_Leq Tm Tm
  | C_Eq Tm Tm
  | C_True
  deriving (Show, Eq, Ord, Typeable, Generic)

instance PP C where
  pp (C_Leq x y) = "leq" >#< x >#< y
  pp (C_Eq x y) = "eq" >#< x >#< y
  pp (C_True) = pp "true"

instance Serialize C

infix   2 `leq`
leq = C_Leq
eq = C_Eq
true = C_True
none :: [C]
none = []

data G
  = G_Eq Tm Tm
  deriving (Show, Typeable, Generic)

instance PP G where
  pp (G_Eq x y) = "eq_grd" >#< x >#< y

instance Serialize G

infix   2 `eq`
geq = G_Eq

type instance TrTrKey Tm = Key
type instance TrTrKey C = Key
type instance TTKey Tm = Key
type instance TTKey C = Key

instance MkSolverConstraint C C where
  toSolverConstraint = id
  fromSolverConstraint = Just

instance TTKeyable Tm where
  toTTKey' o (Tm_Var v) | ttkoptsVarsAsWild o = ttkSingleton TT1K_Any
                        | otherwise           = ttkSingleton (TT1K_One $ Key_Var v)
  toTTKey' o (Tm_Str s) = ttkSingleton $ TT1K_One $ Key_Str s

instance TTKeyable C where
  toTTKeyParentChildren' o (C_Leq x y) = (TT1K_One $ Key_Str "leq", ttkChildren [toTTKey' o x, toTTKey' o y])
  toTTKeyParentChildren' o (C_Eq x y) = (TT1K_One $ Key_Str "eq", ttkChildren [toTTKey' o x, toTTKey' o y])
  toTTKeyParentChildren' o (C_True   ) = (TT1K_One $ Key_Str "true", [])

{-
     :- use_module(library(chr)).
     
     handler leq.
     constraints leq/2.
     :- op(500, xfx, leq).
     
     reflexivity  @ X leq Y <=> X=Y | true.
     antisymmetry @ X leq Y , Y leq X <=> X=Y.
     idempotence  @ X leq Y \ X leq Y <=> true.
     transitivity @ X leq Y , Y leq Z ==> X leq Z.
-}

type E = ()
type P = ()

x = Tm_Var 0
y = Tm_Var 1
z = Tm_Var 2

a = Tm_Str "A"
b = Tm_Str "B"
c = Tm_Str "C"

str :: M.CHRStore C G P
str = M.chrStoreFromElems
  [ [x `leq` y] <==> [x `eq` y] |> [x `geq` y]
  , [x `leq` y, y `leq` x] <==> [x `eq` y]
  , ([x `leq` y], [x `leq` y]) <\=> none
  , [x `leq` y, y `leq` z] ==> [x `leq` z]
  ]

type S = Map.Map Var Tm
sLkup :: Var -> S -> Maybe Tm
sLkup v s = Map.lookup v s >>= \t -> case t of
  Tm_Var v -> sLkup v s
  t        -> Just t

type instance ExtrValVarKey G = Var
type instance ExtrValVarKey C = Var
type instance ExtrValVarKey Tm = Var
type instance CHRMatchableKey S = Key

instance VarLookupCmb S S where
  (|+>) = Map.union

instance VarUpdatable S S where
  varUpd = (|+>)

instance VarUpdatable Tm S where
  s `varUpd` t = case t of
    Tm_Var v -> maybe t id $ sLkup v s
    _ -> t 

instance VarUpdatable G S where
  s `varUpd` G_Eq x y = G_Eq (s `varUpd` x) (s `varUpd` y)

instance VarUpdatable C S where
  s `varUpd` c = case c of
    C_Eq x y -> C_Eq (s `varUpd` x) (s `varUpd` y)
    C_Leq x y -> C_Leq (s `varUpd` x) (s `varUpd` y)
    c -> c

instance VarExtractable Tm where
  varFreeSet (Tm_Var v) = Set.singleton v
  varFreeSet _ = Set.empty

instance VarExtractable G where
  varFreeSet (G_Eq x y) = Set.unions [varFreeSet x, varFreeSet y]

instance VarExtractable C where
  varFreeSet (C_Eq x y) = Set.unions [varFreeSet x, varFreeSet y]
  varFreeSet (C_Leq x y) = Set.unions [varFreeSet x, varFreeSet y]
  varFreeSet _ = Set.empty

instance CHREmptySubstitution S where
  chrEmptySubst = Map.empty

instance IsConstraint C where
  cnstrRequiresSolve C_True = False
  cnstrRequiresSolve (C_Eq _ _) = False
  cnstrRequiresSolve _      = True

instance IsCHRGuard E G S where

instance IsCHRConstraint E C S where

instance CHRCheckable E G S where
  chrCheck _ s g =
    case s `varUpd` g of
      G_Eq (Tm_Str s1) (Tm_Str s2) | s1 == s2 -> return chrEmptySubst
      G_Eq (Tm_Var v1) (Tm_Var v2) | v1 == v2 -> return chrEmptySubst
      G_Eq (Tm_Var v1) (t2       )            -> return $ Map.singleton v1 t2
      G_Eq (t1       ) (Tm_Var v2)            -> return $ Map.singleton v2 t1
      _                                       -> Nothing

instance CHRMatchable E Tm S where
  chrMatchTo _ s t1 t2 = case (s `varUpd` t1, s `varUpd` t2) of
      (Tm_Str s1, Tm_Str s2) | s1 == s2 -> return chrEmptySubst
      (Tm_Var v1, Tm_Var v2) | v1 == v2 -> return chrEmptySubst
      (Tm_Var v1, t2       )            -> return $ Map.singleton v1 t2
      _                                 -> Nothing

instance CHRMatchable E C S where
  chrMatchTo e s c1 c2 = case (s `varUpd` c1, s `varUpd` c2) of
      (C_Leq x1 y1, C_Leq x2 y2) -> m x1 y1 x2 y2
      (C_Eq x1 y1, C_Eq x2 y2) -> m x1 y1 x2 y2
      _ -> Nothing
    where
      m x1 y1 x2 y2 = do
        s1 <- chrMatchTo e s x1 x2
        let s' = s1 |+> s
        s2 <- chrMatchTo e s' y1 y2
        let s'' = s2 |+> s'
        return s''

instance M.IsCHRSolvable E C G P S where

cSolve@(cUnresolved, cResidue, cTrace) =
  M.chrSolve' [CHRTrOpt_Lookup] () str [a `leq` b, b `leq` c, c `leq` a]

mainMono = do
  putPPLn $ "cUnresolved:" >#< vlist cUnresolved
  putPPLn $ "cResidue:" >#< vlist cResidue
  putPPLn $ "cTrace:" >#< vlist cTrace

--------------------------------------------------------
-- leq example, backtrack prio specific

instance MBP.IsCHRSolvable E C G P S where

instance MBP.MonoBacktrackPrio C G P S E IO

mbp :: MBP.CHRMonoBacktrackPrioT C G P S E IO ()
mbp = do
    mapM_ MBP.addRule
      [ [x `leq` y] <==> [x `eq` y] |> [x `geq` y]
      , [x `leq` y, y `leq` x] <==> [x `eq` y]
      , ([x `leq` y], [x `leq` y]) <\=> none
      , [x `leq` y, y `leq` z] ==> [x `leq` z]
      ]
    mapM_ MBP.addConstraintAsWork
      [ a `leq` b
      , b `leq` c
      , c `leq` a
      ]
    MBP.chrSolve
    MBP.getSolveTrace >>= (liftIO . putPPLn)

mainMBP = MBP.runCHRMonoBacktrackPrioT (MBP.emptyCHRGlobState) (MBP.emptyCHRBackState) mbp
