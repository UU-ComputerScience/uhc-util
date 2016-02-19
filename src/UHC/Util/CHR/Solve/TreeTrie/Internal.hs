{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, UndecidableInstances, NoMonomorphismRestriction, MultiParamTypeClasses #-}

-------------------------------------------------------------------------------------------
-- | CHR TreeTrie based solver shared internals
-------------------------------------------------------------------------------------------

module UHC.Util.CHR.Solve.TreeTrie.Internal
  ( CHRTrie
  , CHRTrieKey
  , CHRLookupHow
  
  , chrLookupHowExact
  , chrLookupHowWildAtTrie
  , chrLookupHowWildAtKey
  
  , emptyCHRTrie
  
  , chrToKey
  , chrToWorkKey
  , chrTrieDeleteListByKey
  , chrTrieElems
  , chrTrieFromListByKeyWith
  , chrTrieFromListPartialExactWith
  , chrTrieLookup
  , chrTrieToListByKey
  , chrTrieUnion
  , chrTrieUnionWith

  , CHRKey
  , UsedByKey
  , ppUsedByKey
  
  , WorkTime
  , initWorkTime
  
  , WorkKey
  , WorkUsedInMap
  , WorkTrie

  , Work(..)
  
  , WorkList(..)
  , emptyWorkList
  , wlUsedInUnion
  , wlToList
  , wlCnstrToIns
  , wlDeleteByKeyAndInsert'
  , wlInsert
  
  , SolveCount
  , scntInc
  
  , SolveMatchCache'

  , LastQuery
  , emptyLastQuery
  , lqUnion
  , lqSingleton
  , lqLookupW
  , lqLookupC
  
  , SolveStep'(..)
  , SolveTrace'
  , ppSolveTrace
  
  , SolveState'(..)
  , emptySolveState
  , stDoneCnstrs
  , solveStateResetDone
  , chrSolveStateDoneConstraints
  , chrSolveStateTrace
  
  , slvCombine
  
  , module UHC.Util.CHR.Rule
  )
  where

import           UHC.Util.CHR.Base
import           UHC.Util.CHR.Key
import           UHC.Util.CHR.Rule
-- import           UHC.Util.CHR.Constraint.UHC
import           UHC.Util.Substitutable
import           UHC.Util.VarLookup
import           UHC.Util.VarMp
import           UHC.Util.AssocL
import           UHC.Util.TreeTrie as TreeTrie
import qualified Data.Set as Set
import qualified Data.Map as Map
import           Data.List as List
import           Data.Typeable
import           Data.Data
import           Data.Maybe
import           UHC.Util.Pretty as Pretty
import           UHC.Util.Serialize
import           Control.Monad
import           Control.Monad.State.Strict
import           UHC.Util.Utils

-------------------------------------------------------------------------------------------
--- Choice of Trie structure
-------------------------------------------------------------------------------------------

type CHRTrie v = TreeTrie.TreeTrie (TTKey v) v
type CHRTrieKey v = TreeTrie.TreeTrieKey (TTKey v)
type CHRLookupHow = TreeTrieLookup

chrLookupHowExact      = TTL_Exact
chrLookupHowWildAtTrie = TTL_WildInTrie
chrLookupHowWildAtKey  = TTL_WildInKey

emptyCHRTrie = TreeTrie.empty

chrTrieFromListByKeyWith :: (Ord (TTKey v)) => (v -> v -> v) -> [(CHRTrieKey v,v)] -> CHRTrie v
chrTrieFromListByKeyWith = TreeTrie.fromListByKeyWith
{-# INLINE chrTrieFromListByKeyWith #-}

chrTrieToListByKey :: (Ord (TTKey v)) => CHRTrie v -> [(CHRTrieKey v,v)]
chrTrieToListByKey = TreeTrie.toListByKey
{-# INLINE chrTrieToListByKey #-}

chrTrieUnionWith :: (Ord (TTKey v)) => (v -> v -> v) -> CHRTrie v -> CHRTrie v -> CHRTrie v
chrTrieUnionWith = TreeTrie.unionWith
{-# INLINE chrTrieUnionWith #-}

chrTrieUnion :: (Ord (TTKey v)) => CHRTrie v -> CHRTrie v -> CHRTrie v
chrTrieUnion = TreeTrie.union
{-# INLINE chrTrieUnion #-}

chrTrieElems :: CHRTrie v -> [v]
chrTrieElems = TreeTrie.elems
{-# INLINE chrTrieElems #-}

chrTrieDeleteListByKey :: (Ord (TTKey v)) => [CHRTrieKey v] -> CHRTrie v -> CHRTrie v
chrTrieDeleteListByKey = TreeTrie.deleteListByKey
{-# INLINE chrTrieDeleteListByKey #-}

chrTrieFromListPartialExactWith :: (Ord (TTKey v)) => (v -> v -> v) -> [(CHRTrieKey v,v)] -> CHRTrie v
chrTrieFromListPartialExactWith = TreeTrie.fromListByKeyWith
{-# INLINE chrTrieFromListPartialExactWith #-}

chrTrieLookup' :: (Ord (TTKey v), PP (TTKey v)) => (CHRTrieKey v -> v -> v') -> CHRLookupHow -> CHRTrieKey v -> CHRTrie v -> ([v'],Maybe v')
chrTrieLookup' = TreeTrie.lookupPartialByKey'
{-# INLINE chrTrieLookup' #-}

chrTrieLookup :: (Ord (TTKey v), PP (TTKey v)) => CHRLookupHow -> CHRTrieKey v -> CHRTrie v -> ([v],Maybe v)
chrTrieLookup = TreeTrie.lookupPartialByKey
{-# INLINE chrTrieLookup #-}

chrToKey :: (TTKeyable x, TrTrKey x ~ TTKey x) => x -> CHRTrieKey x
chrToKey = ttkFixate . toTTKey
{-# INLINE chrToKey #-}

chrToWorkKey :: (TTKeyable x) => x -> CHRTrieKey x
chrToWorkKey = ttkFixate . toTTKey' (defaultTTKeyableOpts {ttkoptsVarsAsWild = False})
{-# INLINE chrToWorkKey #-}

-------------------------------------------------------------------------------------------
--- CHR store, with fast search
-------------------------------------------------------------------------------------------

-- type CHRKey = CHRTrieKey
type CHRKey v = CHRTrieKey v
type UsedByKey v = (CHRKey v,Int)

-- ppUsedByKey :: UsedByKey v -> PP_Doc
ppUsedByKey (k,i) = ppTreeTrieKey k >|< "/" >|< i

{-
-- | A CHR as stored in a CHRStore, requiring additional info for efficiency
data StoredCHR e s
  = StoredCHR
      { storedChr       :: !(CHRRule e s)      -- the Rule
      , storedKeyedInx  :: !Int                             -- index of constraint for which is keyed into store
      , storedKeys      :: ![Maybe (CHRKey (CHRConstraint e s))]                  -- keys of all constraints; at storedKeyedInx: Nothing
      , storedIdent     :: !(UsedByKey (CHRConstraint e s))                       -- the identification of a CHR, used for propagation rules (see remark at begin)
      }
  deriving (Typeable)
-}

{-
deriving instance (Data (TTKey c), Data c, Data g) => Data (StoredCHR c g)

type instance TTKey (StoredCHR c g) = TTKey c

instance (TTKeyable (Rule c g p)) => TTKeyable (StoredCHR c g) where
  toTTKey' o schr = toTTKey' o $ storedChr schr

-- | The size of the simplification part of a CHR
storedSimpSz :: StoredCHR c g -> Int
storedSimpSz = ruleSimpSz . storedChr
{-# INLINE storedSimpSz #-}

-- | A CHR store is a trie structure
newtype CHRStore cnstr guard
  = CHRStore
      { chrstoreTrie    :: CHRTrie [StoredCHR cnstr guard]
      }
  deriving (Typeable)

deriving instance (Data (TTKey cnstr), Ord (TTKey cnstr), Data cnstr, Data guard) => Data (CHRStore cnstr guard)

mkCHRStore trie = CHRStore trie

emptyCHRStore :: CHRStore cnstr guard
emptyCHRStore = mkCHRStore emptyCHRTrie

-- | Combine lists of stored CHRs by concat, adapting their identification nr to be unique
cmbStoredCHRs :: [StoredCHR c g] -> [StoredCHR c g] -> [StoredCHR c g]
cmbStoredCHRs s1 s2
  = map (\s@(StoredCHR {storedIdent=(k,nr)}) -> s {storedIdent = (k,nr+l)}) s1 ++ s2
  where l = length s2

instance Show (StoredCHR c g) where
  show _ = "StoredCHR"

ppStoredCHR :: (PP (TTKey c), PP c, PP g) => StoredCHR c g -> PP_Doc
ppStoredCHR c@(StoredCHR {storedIdent=(idKey,idSeqNr)})
  = storedChr c
    >-< indent 2
          (ppParensCommas
            [ pp $ storedKeyedInx c
            , pp $ storedSimpSz c
            , "keys" >#< (ppBracketsCommas $ map (maybe (pp "?") ppTreeTrieKey) $ storedKeys c)
            , "ident" >#< ppParensCommas [ppTreeTrieKey idKey,pp idSeqNr]
            ])

instance (PP (TTKey c), PP c, PP g) => PP (StoredCHR c g) where
  pp = ppStoredCHR

-- | Convert from list to store
chrStoreFromElems :: (TTKeyable c, Ord (TTKey c), TTKey c ~ TrTrKey c) => [Rule c g p] -> CHRStore c g p
chrStoreFromElems chrs
  = mkCHRStore
    $ chrTrieFromListByKeyWith cmbStoredCHRs
        [ (k,[StoredCHR chr i ks' (concat ks,0)])
        | chr <- chrs
        , let cs = ruleHead chr
              simpSz = ruleSimpSz chr
              ks = map chrToKey cs
        , (c,k,i) <- zip3 cs ks [0..]
        , let (ks1,(_:ks2)) = splitAt i ks
              ks' = map Just ks1 ++ [Nothing] ++ map Just ks2
        ]

chrStoreSingletonElem :: (TTKeyable c, Ord (TTKey c), TTKey c ~ TrTrKey c) => Rule c g p -> CHRStore c g p
chrStoreSingletonElem x = chrStoreFromElems [x]

chrStoreUnion :: (Ord (TTKey c)) => CHRStore c g p -> CHRStore c g p -> CHRStore c g p
chrStoreUnion cs1 cs2 = mkCHRStore $ chrTrieUnionWith cmbStoredCHRs (chrstoreTrie cs1) (chrstoreTrie cs2)
{-# INLINE chrStoreUnion #-}

chrStoreUnions :: (Ord (TTKey c)) => [CHRStore c g p] -> CHRStore c g p
chrStoreUnions []  = emptyCHRStore
chrStoreUnions [s] = s
chrStoreUnions ss  = foldr1 chrStoreUnion ss
{-# INLINE chrStoreUnions #-}

chrStoreToList :: (Ord (TTKey c)) => CHRStore c g p -> [(CHRKey c,[Rule c g p])]
chrStoreToList cs
  = [ (k,chrs)
    | (k,e) <- chrTrieToListByKey $ chrstoreTrie cs
    , let chrs = [chr | (StoredCHR {storedChr = chr, storedKeyedInx = 0}) <- e]
    , not $ Prelude.null chrs
    ]

chrStoreElems :: (Ord (TTKey c)) => CHRStore c g p -> [Rule c g p]
chrStoreElems = concatMap snd . chrStoreToList

ppCHRStore :: (PP c, PP g, Ord (TTKey c), PP (TTKey c)) => CHRStore c g p -> PP_Doc
ppCHRStore = ppCurlysCommasBlock . map (\(k,v) -> ppTreeTrieKey k >-< indent 2 (":" >#< ppBracketsCommasBlock v)) . chrStoreToList

ppCHRStore' :: (PP c, PP g, Ord (TTKey c), PP (TTKey c)) => CHRStore c g p -> PP_Doc
ppCHRStore' = ppCurlysCommasBlock . map (\(k,v) -> ppTreeTrieKey k >-< indent 2 (":" >#< ppBracketsCommasBlock v)) . chrTrieToListByKey . chrstoreTrie

-}

-------------------------------------------------------------------------------------------
--- WorkTime, the time/history counter
-------------------------------------------------------------------------------------------

type WorkTime = Int

initWorkTime :: WorkTime
initWorkTime = 0

-------------------------------------------------------------------------------------------
--- Solver worklist
-------------------------------------------------------------------------------------------


type WorkKey       v = CHRKey v
type WorkUsedInMap v = Map.Map (Set.Set (CHRKey v)) (Set.Set (UsedByKey v))
type WorkTrie      c = CHRTrie (Work c)

-- | A chunk of work to do when solving, a constraint + sequence nr
data Work c
  = Work
      { workKey     :: WorkKey c
      , workCnstr   :: !c            -- the constraint to be reduced
      , workTime    :: WorkTime                     -- the history count at which the work was added
      -- , workUsedIn  :: Set.Set (CHRKey c)              -- marked with the propagation rules already applied to it
      }

type instance TTKey (Work c) = TTKey c

-- | The work to be done (wlQueue), also represented as a trie (wlTrie) because efficient check on already worked on is needed.
--   A done set (wlDoneSet) remembers which CHRs (itself a list of constraints) have been solved.
--   To prevent duplicate propagation a mapping from CHRs to a map (wlUsedIn) to the CHRs it is used in is maintained.
data WorkList c
  = WorkList
      { wlTrie      :: !(WorkTrie c)
      , wlDoneSet   :: !(Set.Set (WorkKey c))                   -- accumulative store of all keys added, set semantics, thereby avoiding double entry
      , wlQueue     :: !(AssocL (WorkKey c) (Work c))
      , wlScanned   :: !(AssocL (WorkKey c) (Work c))         -- tried but could not solve, so retry when other succeeds
      , wlUsedIn    :: !(WorkUsedInMap c)                       -- which work items are used in which propagation constraints
      }

emptyWorkList = WorkList emptyCHRTrie Set.empty [] [] Map.empty

-- wlUsedInUnion :: (Ord k, k ~ TTKey c) => WorkUsedInMap c -> WorkUsedInMap c -> WorkUsedInMap c
wlUsedInUnion = Map.unionWith Set.union
{-# INLINE wlUsedInUnion #-}

instance Show (Work c) where
  show _ = "SolveWork"

instance (PP c) => PP (Work c) where
  pp w = pp $ workCnstr w



wlToList :: {- (PP p, PP i) => -} WorkList c -> [c]
wlToList wl = map workCnstr $ chrTrieElems $ wlTrie wl

wlCnstrToIns :: (TTKeyable c, TTKey c ~ TrTrKey c, Ord (TTKey c)) => WorkList c -> [c] -> AssocL (WorkKey c) c
wlCnstrToIns wl@(WorkList {wlDoneSet = ds}) inscs
  = [(chrToWorkKey c,c) | c <- inscs, let k = chrToKey c, not (k `Set.member` ds)]

wlDeleteByKeyAndInsert' :: (Ord (TTKey c)) => WorkTime -> [WorkKey c] -> AssocL (WorkKey c) c -> WorkList c -> WorkList c
wlDeleteByKeyAndInsert' wtm delkeys inskeycs wl@(WorkList {wlQueue = wlq, wlTrie = wlt, wlDoneSet = ds})
  = wl { wlQueue   = Map.toList inswork ++ [ w | w@(k,_) <- wlq, not (k `elem` delkeys) ]
       , wlTrie    = instrie `chrTrieUnion` chrTrieDeleteListByKey delkeys wlt
       , wlDoneSet = Map.keysSet inswork `Set.union` ds
       }
  where inswork = Map.fromList [ (k,Work k c wtm) | (k,c) <- inskeycs ]
        instrie = chrTrieFromListPartialExactWith const $ Map.toList inswork

wlDeleteByKeyAndInsert :: (TTKeyable c, Ord (TTKey c), TTKey c ~ TrTrKey c) => WorkTime -> [WorkKey c] -> [c] -> WorkList c -> WorkList c
wlDeleteByKeyAndInsert wtm delkeys inscs wl
  = wlDeleteByKeyAndInsert' wtm delkeys (wlCnstrToIns wl inscs) wl

wlInsert :: (TTKeyable c, Ord (TTKey c), TrTrKey c ~ TTKey c) => WorkTime -> [c] -> WorkList c -> WorkList c
wlInsert wtm = wlDeleteByKeyAndInsert wtm []
{-# INLINE wlInsert #-}

-------------------------------------------------------------------------------------------
--- Solver counting
-------------------------------------------------------------------------------------------

type SolveCount a b = Map.Map a (Map.Map b Int)

scntUnion :: (Ord a,Ord b) => SolveCount a b -> SolveCount a b -> SolveCount a b
scntUnion = Map.unionWith (Map.unionWith (+))
{-# INLINE scntUnion #-}

scntInc :: (Ord a,Ord b) => a -> b -> SolveCount a b -> SolveCount a b
scntInc a b c1 = Map.singleton a (Map.singleton b 1) `scntUnion` c1
{-# INLINE scntInc #-}

-------------------------------------------------------------------------------------------
--- Cache for maintaining which WorkKey has already had a match
-------------------------------------------------------------------------------------------

type SolveMatchCache' c schr s = Map.Map (WorkKey c) [((schr,([WorkKey c],[Work c])),s)]

-------------------------------------------------------------------------------------------
--- WorkTime of last search
-------------------------------------------------------------------------------------------


type LastQueryW v = Map.Map (WorkKey v) WorkTime
type LastQuery v = Map.Map (CHRKey v) (LastQueryW v)

-- emptyLastQuery :: LastQuery v
emptyLastQuery = Map.empty
{-# INLINE emptyLastQuery #-}

-- lqSingleton :: CHRKey v -> Set.Set (WorkKey v) -> WorkTime -> LastQuery v
lqSingleton ck wks wtm = Map.singleton ck $ Map.fromList [ (w,wtm) | w <- Set.toList wks ]
{-# INLINE lqSingleton #-}

-- lqUnion :: LastQuery v -> LastQuery v -> LastQuery v
lqUnion = Map.unionWith Map.union
{-# INLINE lqUnion #-}

-- lqLookupC :: CHRKey v -> LastQuery v -> LastQueryW v
lqLookupC = Map.findWithDefault Map.empty
{-# INLINE lqLookupC #-}

-- lqLookupW :: WorkKey v -> LastQueryW v -> WorkTime
lqLookupW = Map.findWithDefault initWorkTime
{-# INLINE lqLookupW #-}

-------------------------------------------------------------------------------------------
--- Solver trace
-------------------------------------------------------------------------------------------

-- | A trace step
data SolveStep' c r s
  = SolveStep
      { stepChr         :: r
      , stepSubst       :: s
      , stepNewTodo     :: [c]
      , stepNewDone     :: [c]
      }
  | SolveStats
      { stepStats       :: Map.Map String PP_Doc
      }
  | SolveDbg
      { stepPP          :: PP_Doc
      }

type SolveTrace' c r s = [SolveStep' c r s]

instance Show (SolveStep' c r s) where
  show _ = "SolveStep"

instance (PP r, PP c) => {- (PP c, PP g) => -} PP (SolveStep' c r s) where
  pp (SolveStep   step _ todo done) = "STEP" >#< (step >-< "new todo:" >#< ppBracketsCommas todo >-< "new done:" >#< ppBracketsCommas done)
  pp (SolveStats  stats           ) = "STATS"  >#< (ppAssocLV (Map.toList stats))
  pp (SolveDbg    p               ) = "DBG"  >#< p

ppSolveTrace :: (PP r, PP c) => {- (PP s, PP c, PP g) => -} SolveTrace' c r s -> PP_Doc
ppSolveTrace tr = ppBracketsCommasBlock [ pp st | st <- tr ]

-------------------------------------------------------------------------------------------
--- Solve state
-------------------------------------------------------------------------------------------


data SolveState' c r sr s
  = SolveState
      { stWorkList      :: !(WorkList c)
      , stDoneCnstrSet  :: !(Set.Set c)
      , stTrace         :: SolveTrace' c r s
      , stCountCnstr    :: SolveCount (WorkKey c) String
      , stMatchCache    :: !(SolveMatchCache' c sr s)
      , stHistoryCount  :: WorkTime
      , stLastQuery     :: (LastQuery c)
      }

stDoneCnstrs :: SolveState' c r sr s -> [c]
stDoneCnstrs = Set.toList . stDoneCnstrSet
{-# INLINE stDoneCnstrs #-}

emptySolveState :: SolveState' c r sr s
emptySolveState = SolveState emptyWorkList Set.empty [] Map.empty Map.empty initWorkTime emptyLastQuery
{-# INLINE emptySolveState #-}

solveStateResetDone :: SolveState' c r sr s -> SolveState' c r sr s
solveStateResetDone s = s {stDoneCnstrSet = Set.empty}
{-# INLINE solveStateResetDone #-}

chrSolveStateDoneConstraints :: SolveState' c r sr s -> [c]
chrSolveStateDoneConstraints = stDoneCnstrs
{-# INLINE chrSolveStateDoneConstraints #-}

chrSolveStateTrace :: SolveState' c r sr s -> SolveTrace' c r s
chrSolveStateTrace = stTrace
{-# INLINE chrSolveStateTrace #-}

-------------------------------------------------------------------------------------------
--- Solver
-------------------------------------------------------------------------------------------

slvCombine :: Eq k => ([([Assoc k v], [Assoc k v])], t) -> [AssocL k v]
slvCombine ([],_) = []
slvCombine ((lh:lt),_)
  = concatMap combineToDistinguishedElts l2
  where l2 = g2 [] lh lt
           where g2 ll l []           = [mk ll l []]
                 g2 ll l lr@(lrh:lrt) = mk ll l lr : g2 (ll ++ [l]) lrh lrt
                 mk ll (bef,aft) lr   = map fst ll ++ [aft] ++ map cmb lr
                                      where cmb (a,b) = a++b
{-# INLINE slvCombine #-}

