{-# LANGUAGE CPP, StandaloneDeriving, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}

-------------------------------------------------------------------------------------------
--- Constraint Handling Rules: Constraint language for UHC
-------------------------------------------------------------------------------------------

module UHC.Util.CHR.Constraint.UHC
  ( Constraint(..)
  , mkReduction
  
  , cnstrReducablePart
  
  , UnresolvedTrace(..)
  
  , cnstrMpSingletonL,cnstrMpFromList
  , ConstraintToInfoTraceMp
  , cnstrTraceMpSingleton
  , cnstrTraceMpLiftTrace
  , cnstrTraceMpElimTrace
  , cnstrTraceMpFromList
  , ConstraintToInfoMap
  , emptyCnstrMp
  , cnstrMpUnion
  , cnstrMpUnions
  )
  where

import           UHC.Util.CHR
import           UHC.Util.TreeTrie
import           UHC.Util.Substitutable
import           UHC.Util.Pretty as PP
import           UHC.Util.Utils
import qualified Data.Set as Set
import qualified Data.Map as Map
import           UHC.Util.VarMp
import           Control.Monad
import           UHC.Util.Binary
import           UHC.Util.Serialize
-- import({%{EH}Opts.Base})

-------------------------------------------------------------------------------------------
--- Constraint
-------------------------------------------------------------------------------------------

-- | A Constraint is abstracted over the exact predicate, but differentiates on the role: to prove, can be assumed, and side effect of reduction
data Constraint p info
  = Prove           { cnstrPred :: !p }             -- proof obligation
  | Assume          { cnstrPred :: !p }             -- assumed constraint
  | Reduction                                       -- 'side effect', residual info used by (e.g.) codegeneration
                    { cnstrPred :: !p               -- the pred to which reduction was done
                    , cnstrInfo :: !info            -- additional reduction specific info w.r.t. codegeneration
                    , cnstrFromPreds :: ![p]        -- the preds from which reduction was done
                    -- , cnstrVarMp :: VarMp' (SubstVarKey p) (SubstVarVal p)           -- additional bindings for type (etc.) variables, i.e. improving substitution
                    }
  deriving (Eq, Ord, Show)

type instance TTKey (Constraint p info) = TTKey p

instance IsConstraint (Constraint p info) where
  cnstrRequiresSolve (Reduction {}) = False
  cnstrRequiresSolve _              = True

{-
deriving instance (Eq p, Eq info, Eq (SubstVarKey p), Eq (SubstVarVal p)) => Eq (Constraint p info)
deriving instance (Ord p, Ord info, Ord (SubstVarKey p), Ord (SubstVarVal p)) => Ord (Constraint p info)
-- deriving instance Ord (Constraint p info)

instance Eq p => Eq (Constraint p info) where
  Prove  p1 == Prove  p2 = p1 == p2
  Assume p1 == Assume p2 = p1 == p2
  Reduction {cnstrPred=p1} == Reduction {cnstrPred=p2} = p1 == p2

instance Ord p => Ord (Constraint p info) where
  Prove                p1  `compare` Prove                p2  = p1 `compare` p2
  Prove     {}             `compare` _                        = LT
  Assume               p1  `compare` Assume               p2  = p1 `compare` p2
  Assume               p1  `compare` Prove     {}             = GT
  Assume               p1  `compare` _                        = LT
  Reduction {cnstrPred=p1} `compare` Reduction {cnstrPred=p2} = p1 `compare` p2
  _                        `compare` Reduction {cnstrPred=p2} = GT
-}

mkReduction :: p -> info -> [p] -> Constraint p info
mkReduction p i ps
  = Reduction p i ps
              -- varlookupEmpty

#if __GLASGOW_HASKELL__ >= 708
deriving instance Typeable  Constraint
#else
deriving instance Typeable2 Constraint
#endif
deriving instance (Data x, Data y) => Data (Constraint x y)

-- | Dissection of Constraint, including reconstruction function
cnstrReducablePart :: Constraint p info -> Maybe (String,p,p->Constraint p info)
cnstrReducablePart (Prove  p) = Just ("Prf",p,Prove)
cnstrReducablePart (Assume p) = Just ("Ass",p,Assume)
cnstrReducablePart _          = Nothing

{-
instance (CHRMatchable env p s) => CHRMatchable env (Constraint p info) s where
  type CHRMatchableKey s = Key
  chrMatchTo env s c1 c2
    = do { (_,p1,_) <- cnstrReducablePart c1
         ; (_,p2,_) <- cnstrReducablePart c2
         ; chrMatchTo env s p1 p2
         }

instance (TTKeyable p, TTKey (Constraint p info) ~ TTKey p) => TTKeyable (Constraint p info) where
  type TTKey (Constraint p info) = Key
  toTTKey' o c -- = maybe [] (\(s,p,_) -> ttkAdd (TT1K_One $ Key_Str s) [toTTKey' o p]) $ cnstrReducablePart c
    = case cnstrReducablePart c of
        Just (s,p,_) -> ttkAdd' (TT1K_One $ Key_Str s) cs
                     where (_,cs) = toTTKeyParentChildren' o p
        _            -> panic "TTKeyable (Constraint p info).toTTKey'" -- ttkEmpty
-}

type instance ExtrValVarKey (Constraint p info) = ExtrValVarKey p

instance (VarExtractable p) => VarExtractable (Constraint p info) where
  varFreeSet c
    = case cnstrReducablePart c of
        Just (_,p,_) -> varFreeSet p
        _            -> Set.empty

instance (VarUpdatable p s,VarUpdatable info s) => VarUpdatable (Constraint p info) s where
  varUpd s      (Prove     p       ) = Prove      (varUpd s p)
  varUpd s      (Assume    p       ) = Assume     (varUpd s p)
  varUpd s      r@(Reduction {cnstrPred=p, cnstrInfo=i, cnstrFromPreds=ps})
                                     = r {cnstrPred=varUpd s p, cnstrInfo=varUpd s i, cnstrFromPreds=map (varUpd s) ps}

-------------------------------------------------------------------------------------------
--- Resolution trace reification, for error reporting
-------------------------------------------------------------------------------------------

-- | The trace of an unresolved predicate
data UnresolvedTrace p info
  = UnresolvedTrace_None                                    -- no trace required when all is resolved
  | UnresolvedTrace_Red                                     -- ok reduction, with failure deeper down
      { utraceRedFrom       :: p
      , utraceInfoTo2From   :: info
      , utraceRedTo         :: [UnresolvedTrace p info]
      }
  | UnresolvedTrace_Fail                                    -- failed reduction
      { utraceRedFrom       :: p
      -- , utraceInfoTo2From    :: info
      , utraceRedTo         :: [UnresolvedTrace p info]
      }
  | UnresolvedTrace_Overlap                                 -- choice could not be made
      { utraceRedFrom       :: p
      , utraceRedChoices    :: [(info,[UnresolvedTrace p info])]
      }
  deriving Show

instance Eq p => Eq (UnresolvedTrace p info) where
  t1 == t2 = True -- utraceRedFrom t1 == utraceRedFrom t2

instance (PP p, PP info) => PP (UnresolvedTrace p info) where
  pp x = case x of
           UnresolvedTrace_None             -> PP.empty
           UnresolvedTrace_Red      p i us  -> p >|< ":" >#< i >-< indent 2 (vlist $ map pp us)
           UnresolvedTrace_Fail     p   us  -> p >|< ": FAIL" >-< indent 2 (vlist $ map pp us)
           UnresolvedTrace_Overlap  p uss   -> p >|< ": OVERLAP" >-< indent 2 (vlist $ map (\(i,u) -> i >-< indent 2 (vlist $ map pp u)) uss)

-------------------------------------------------------------------------------------------
--- Mapping: constraint -> info (in varieties)
-------------------------------------------------------------------------------------------

-- | Map from constraint to something
type ConstraintMp' p info x = Map.Map (Constraint p info) [x]

cnstrMpSingletonL :: Constraint p i -> [x] -> ConstraintMp' p i x
cnstrMpSingletonL c xs = Map.singleton c xs

cnstrMpSingleton :: Constraint p i -> x -> ConstraintMp' p i x
cnstrMpSingleton c x = cnstrMpSingletonL c [x]

cnstrMpFromList :: (Ord p, Ord i) => [(Constraint p i,x)] -> ConstraintMp' p i x
cnstrMpFromList l = Map.fromListWith (++) [ (c,[x]) | (c,x) <- l ]

cnstrMpMap :: (Ord p, Ord i) => (x -> y) -> ConstraintMp' p i x -> ConstraintMp' p i y
cnstrMpMap f = Map.map (map f)

-- | Map from constraint to info + trace
type ConstraintToInfoTraceMp p info = ConstraintMp' p info (info,[UnresolvedTrace p info])

cnstrTraceMpFromList :: (Ord p, Ord i) => [(Constraint p i,(i,[UnresolvedTrace p i]))] -> ConstraintToInfoTraceMp p i
cnstrTraceMpFromList = cnstrMpFromList

cnstrTraceMpSingleton :: Constraint p i -> i -> [UnresolvedTrace p i] -> ConstraintToInfoTraceMp p i
cnstrTraceMpSingleton c i ts = cnstrMpSingleton c (i,ts)

cnstrTraceMpElimTrace :: (Ord p, Ord i) => ConstraintToInfoTraceMp p i -> ConstraintToInfoMap p i
cnstrTraceMpElimTrace = cnstrMpMap fst

cnstrTraceMpLiftTrace :: (Ord p, Ord i) => ConstraintToInfoMap p i -> ConstraintToInfoTraceMp p i
cnstrTraceMpLiftTrace = cnstrMpMap (\x -> (x,[]))

-- | Map from constraint to info
type ConstraintToInfoMap     p info = ConstraintMp' p info info

emptyCnstrMp :: ConstraintMp' p info x
emptyCnstrMp = Map.empty

cnstrMpUnion :: (Ord p, Ord i) => ConstraintMp' p i x -> ConstraintMp' p i x -> ConstraintMp' p i x
cnstrMpUnion = Map.unionWith (++)

cnstrMpUnions :: (Ord p, Ord i) => [ConstraintMp' p i x] -> ConstraintMp' p i x
cnstrMpUnions = Map.unionsWith (++)

-------------------------------------------------------------------------------------------
--- Pretty printing
-------------------------------------------------------------------------------------------

instance (PP p, PP info) => PP (Constraint p info) where
  pp (Prove     p     ) = "Prove"  >#< p
  pp (Assume    p     ) = "Assume" >#< p
  pp (Reduction {cnstrPred=p, cnstrInfo=i, cnstrFromPreds=ps})
                        = "Red"    >#< p >#< "<" >#< i >#< "<" >#< ppBracketsCommas ps

-------------------------------------------------------------------------------------------
--- Instances: Binary, Serialize
-------------------------------------------------------------------------------------------

instance (Serialize p, Serialize i) => Serialize (Constraint p i) where
  sput (Prove     a      ) = sputWord8 0 >> sput a
  sput (Assume    a      ) = sputWord8 1 >> sput a
  -- sput (Reduction a b c d) = sputWord8 2 >> sput a >> sput b >> sput c >> sput d
  sput (Reduction a b c  ) = sputWord8 2 >> sput a >> sput b >> sput c
  sget = do t <- sgetWord8
            case t of
              0 -> liftM  Prove     sget
              1 -> liftM  Assume    sget
              -- 2 -> liftM4 Reduction sget sget sget sget
              2 -> liftM3 Reduction sget sget sget

