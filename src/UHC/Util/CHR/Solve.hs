{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, UndecidableInstances, NoMonomorphismRestriction #-}

-------------------------------------------------------------------------------------------
--- CHR solver
-------------------------------------------------------------------------------------------

{-|
Derived from work by Gerrit vd Geest, but greatly adapted to use more efficient searching.

Assumptions (to be documented further)
- The key [Trie.TrieKey Key] used to lookup a constraint in a CHR should be distinguishing enough to be used for the prevention
  of the application of a propagation rule for a 2nd time.
-}

module UHC.Util.CHR.Solve
  ( CHRStore
  , emptyCHRStore
  
  , chrStoreFromElems
  , chrStoreUnion
  , chrStoreUnions
  , chrStoreSingletonElem
  , chrStoreToList
  , chrStoreElems
  
  , ppCHRStore
  , ppCHRStore'
  
  , SolveStep(..)
  , SolveTrace
  , ppSolveTrace
  
  , SolveState
  , emptySolveState
  , solveStateResetDone
  , chrSolveStateDoneConstraints
  , chrSolveStateTrace
  
  -- , chrSolve
  , chrSolve'
  , chrSolve''
  )
  where

import           UHC.Util.CHR.Base
import           UHC.Util.CHR.Key
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

-- type CHRTrie k v = TreeTrie.TreeTrie k v
type CHRTrie v = TreeTrie.TreeTrie (TTKey v) v
-- type CHRTrieKey = TreeTrie.TreeTrieKey Key
type CHRTrieKey v = TreeTrie.TreeTrieKey (TTKey v)
type CHRLookupHow = TreeTrieLookup

chrLookupHowExact      = TTL_Exact
chrLookupHowWildAtTrie = TTL_WildInTrie
chrLookupHowWildAtKey  = TTL_WildInKey

emptyCHRTrie = TreeTrie.empty

{-
ppCHRTrieKey :: PP (TTKey v) => CHRTrieKey v -> PP_Doc
ppCHRTrieKey = ppTreeTrieKey
-}

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

-- | A CHR as stored in a CHRStore, requiring additional info for efficiency
data StoredCHR c g
  = StoredCHR
      { storedChr       :: !(Rule c g)      -- the Rule
      , storedKeyedInx  :: !Int                             -- index of constraint for which is keyed into store
      , storedKeys      :: ![Maybe (CHRKey c)]                  -- keys of all constraints; at storedKeyedInx: Nothing
      , storedIdent     :: !(UsedByKey c)                       -- the identification of a CHR, used for propagation rules (see remark at begin)
      }
  deriving (Typeable)

deriving instance (Data (TTKey c), Data c, Data g) => Data (StoredCHR c g)

type instance TTKey (StoredCHR c g) = TTKey c

instance (TTKeyable (Rule c g)) => TTKeyable (StoredCHR c g) where
  toTTKey' o schr = toTTKey' o $ storedChr schr

-- | The size of the simplification part of a CHR
storedSimpSz :: StoredCHR c g -> Int
storedSimpSz = chrSimpSz . storedChr
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
chrStoreFromElems :: (TTKeyable c, Ord (TTKey c), TTKey c ~ TrTrKey c) => [Rule c g] -> CHRStore c g
chrStoreFromElems chrs
  = mkCHRStore
    $ chrTrieFromListByKeyWith cmbStoredCHRs
        [ (k,[StoredCHR chr i ks' (concat ks,0)])
        | chr <- chrs
        , let cs = chrHead chr
              simpSz = chrSimpSz chr
              ks = map chrToKey cs
        , (c,k,i) <- zip3 cs ks [0..]
        , let (ks1,(_:ks2)) = splitAt i ks
              ks' = map Just ks1 ++ [Nothing] ++ map Just ks2
        ]

chrStoreSingletonElem :: (TTKeyable c, Ord (TTKey c), TTKey c ~ TrTrKey c) => Rule c g -> CHRStore c g
chrStoreSingletonElem x = chrStoreFromElems [x]

chrStoreUnion :: (Ord (TTKey c)) => CHRStore c g -> CHRStore c g -> CHRStore c g
chrStoreUnion cs1 cs2 = mkCHRStore $ chrTrieUnionWith cmbStoredCHRs (chrstoreTrie cs1) (chrstoreTrie cs2)
{-# INLINE chrStoreUnion #-}

chrStoreUnions :: (Ord (TTKey c)) => [CHRStore c g] -> CHRStore c g
chrStoreUnions []  = emptyCHRStore
chrStoreUnions [s] = s
chrStoreUnions ss  = foldr1 chrStoreUnion ss
{-# INLINE chrStoreUnions #-}

chrStoreToList :: (Ord (TTKey c)) => CHRStore c g -> [(CHRKey c,[Rule c g])]
chrStoreToList cs
  = [ (k,chrs)
    | (k,e) <- chrTrieToListByKey $ chrstoreTrie cs
    , let chrs = [chr | (StoredCHR {storedChr = chr, storedKeyedInx = 0}) <- e]
    , not $ Prelude.null chrs
    ]

chrStoreElems :: (Ord (TTKey c)) => CHRStore c g -> [Rule c g]
chrStoreElems = concatMap snd . chrStoreToList

ppCHRStore :: (PP c, PP g, Ord (TTKey c), PP (TTKey c)) => CHRStore c g -> PP_Doc
ppCHRStore = ppCurlysCommasBlock . map (\(k,v) -> ppTreeTrieKey k >-< indent 2 (":" >#< ppBracketsCommasBlock v)) . chrStoreToList

ppCHRStore' :: (PP c, PP g, Ord (TTKey c), PP (TTKey c)) => CHRStore c g -> PP_Doc
ppCHRStore' = ppCurlysCommasBlock . map (\(k,v) -> ppTreeTrieKey k >-< indent 2 (":" >#< ppBracketsCommasBlock v)) . chrTrieToListByKey . chrstoreTrie

-------------------------------------------------------------------------------------------
--- WorkTime, the time/history counter
-------------------------------------------------------------------------------------------

type WorkTime = Int

initWorkTime :: WorkTime
initWorkTime = 0

-------------------------------------------------------------------------------------------
--- Solver worklist
-------------------------------------------------------------------------------------------

-- type WorkKey = CHRKey
type WorkKey v = CHRKey v
-- type WorkUsedInMap = Map.Map (Set.Set CHRKey) (Set.Set UsedByKey)
type WorkUsedInMap v = Map.Map (Set.Set (CHRKey v)) (Set.Set (UsedByKey v))
type WorkTrie c = CHRTrie (Work c)

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

-- ppUsedByKey :: UsedByKey v -> PP_Doc
ppUsedByKey (k,i) = ppTreeTrieKey k >|< "/" >|< i

{-
mkWorkList :: (TTKeyable c, TrTrKey c ~ TTKey c) => WorkTime -> [c] -> WorkList c
mkWorkList wtm = flip (wlInsert wtm) emptyWorkList
-}

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
--- Solver trace
-------------------------------------------------------------------------------------------

-- | A trace step
data SolveStep c g s
  = SolveStep
      { stepChr         :: Rule c g
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

type SolveTrace c g s = [SolveStep c g s]

instance Show (SolveStep c g s) where
  show _ = "SolveStep"

instance (PP c, PP g) => PP (SolveStep c g s) where
  pp (SolveStep   step _ todo done) = "STEP" >#< (step >-< "new todo:" >#< ppBracketsCommas todo >-< "new done:" >#< ppBracketsCommas done)
  pp (SolveStats  stats           ) = "STATS"  >#< (ppAssocLV (Map.toList stats))
  pp (SolveDbg    p               ) = "DBG"  >#< p

ppSolveTrace :: (PP s, PP c, PP g) => SolveTrace c g s -> PP_Doc
ppSolveTrace tr = ppBracketsCommasBlock [ pp st | st <- tr ]

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

-- type SolveMatchCache c g s = Map.Map (CHRKey c) [((StoredCHR c g,([WorkKey c],[Work c])),s)]
type SolveMatchCache c g s = Map.Map (WorkKey c) [((StoredCHR c g,([WorkKey c],[Work c])),s)]

-------------------------------------------------------------------------------------------
--- WorkTime of last search
-------------------------------------------------------------------------------------------

-- type LastQueryW = Map.Map WorkKey WorkTime
type LastQueryW v = Map.Map (WorkKey v) WorkTime
-- type LastQuery = Map.Map CHRKey LastQueryW
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
--- Solve state
-------------------------------------------------------------------------------------------

data SolveState c g s
  = SolveState
      { stWorkList      :: !(WorkList c)
      , stDoneCnstrSet  :: !(Set.Set c)
      , stTrace         :: SolveTrace c g s
      , stCountCnstr    :: SolveCount (WorkKey c) String
      , stMatchCache    :: !(SolveMatchCache c g s)
      , stHistoryCount  :: WorkTime
      , stLastQuery     :: (LastQuery c)
      }

stDoneCnstrs :: SolveState c g s -> [c]
stDoneCnstrs = Set.toList . stDoneCnstrSet
{-# INLINE stDoneCnstrs #-}

emptySolveState :: SolveState c g s
emptySolveState = SolveState emptyWorkList Set.empty [] Map.empty Map.empty initWorkTime emptyLastQuery
{-# INLINE emptySolveState #-}

solveStateResetDone :: SolveState c g s -> SolveState c g s
solveStateResetDone s = s {stDoneCnstrSet = Set.empty}
{-# INLINE solveStateResetDone #-}

chrSolveStateDoneConstraints :: SolveState c g s -> [c]
chrSolveStateDoneConstraints = stDoneCnstrs
{-# INLINE chrSolveStateDoneConstraints #-}

chrSolveStateTrace :: SolveState c g s -> SolveTrace c g s
chrSolveStateTrace = stTrace
{-# INLINE chrSolveStateTrace #-}

-------------------------------------------------------------------------------------------
--- Solver
-------------------------------------------------------------------------------------------

{-
chrSolve
  :: forall env c g s .
     ( Ord c
     , Ord (TTKey c)
     , IsConstraint c
     , CHRMatchable env c s, CHRCheckable env g s
     , VarLookupCmb s s
     , VarUpdatable s s, VarUpdatable g s, VarUpdatable c s
     , CHREmptySubstitution s
     , PP g, PP c, PP (TTKey c) -- for debugging
     , TrTrKey c ~ TTKey c
     )
     => env
     -> CHRStore c g
     -> [c]
     -> [c]
chrSolve env chrStore cnstrs
  = work ++ done
  where (work, done, _ :: SolveTrace c g s) = chrSolve' env chrStore cnstrs
-}

chrSolve'
  :: ( Ord c
     , Ord (TTKey c)
     , IsConstraint c
     , CHRMatchable env c s, CHRCheckable env g s
     , VarLookupCmb s s
     , VarUpdatable s s, VarUpdatable g s, VarUpdatable c s
     , CHREmptySubstitution s
     , PP g, PP c, PP (TTKey c) -- for debugging
     , TrTrKey c ~ TTKey c
     )
     => env
     -> CHRStore c g
     -> [c]
     -> ([c],[c],SolveTrace c g s)
chrSolve' env chrStore cnstrs
  = (wlToList (stWorkList finalState), stDoneCnstrs finalState, stTrace finalState)
  where finalState = chrSolve'' env chrStore cnstrs emptySolveState

chrSolve''
  :: forall env c g s .
     ( Ord c
     , Ord (TTKey c)
     , IsConstraint c
     , CHRMatchable env c s, CHRCheckable env g s
     , VarLookupCmb s s
     , VarUpdatable s s, VarUpdatable g s, VarUpdatable c s
     , CHREmptySubstitution s
     , PP g, PP c, PP (TTKey c) -- for debugging
     , TrTrKey c ~ TTKey c
     )
     => env
     -> CHRStore c g
     -> [c]
     -> SolveState c g s
     -> SolveState c g s
chrSolve'' env chrStore cnstrs prevState
  = postState {stMatchCache = Map.empty}
  where postState
          = 
{-
            addStats Map.empty
                [ ("workMatches",ppAssocLV [(ppTreeTrieKey k,pp (fromJust l))
                | (k,c) <- Map.toList $ stCountCnstr st, let l = Map.lookup "workMatched" c, isJust l])
                ]
-}
            st
          where st = execState iter $ initState prevState
        iter = do
          st <- get
          case st of
            (SolveState {stWorkList = wl@(WorkList {wlQueue = (workHd@(workHdKey,_) : workTl)})}) ->
                case matches of
                  (_:_) -> do
                      put 
{-   
                          $ addStats Map.empty
                                [ ("(0) yes work", ppTreeTrieKey workHdKey)
                                ]
                          $
-}    
                          stmatch
                      expandMatch matches
                    where -- expandMatch :: SolveState c g s -> [((StoredCHR c g, ([WorkKey c], [Work c])), s)] -> SolveState c g s
                          expandMatch ( ( ( schr@(StoredCHR {storedIdent = chrId, storedChr = chr@(Rule {chrBody = b, chrSimpSz = simpSz})})
                                          , (keys,works)
                                          )
                                        , subst
                                        ) : tlMatch
                                      ) = do
                              st@(SolveState {stWorkList = wl, stHistoryCount = histCount}) <- get
                              let (tlMatchY,tlMatchN) = partition (\(r@(_,(ks,_)),_) -> not (any (`elem` keysSimp) ks || slvIsUsedByPropPart (wlUsedIn wl') r)) tlMatch
                                  (keysSimp,keysProp) = splitAt simpSz keys
                                  usedIn              = Map.singleton (Set.fromList keysProp) (Set.singleton chrId)
                                  (bTodo,bDone)       = splitDone $ map (varUpd subst) b
                                  bTodo'              = wlCnstrToIns wl bTodo
                                  wl' = wlDeleteByKeyAndInsert' histCount keysSimp bTodo'
                                        $ wl { wlUsedIn  = usedIn `wlUsedInUnion` wlUsedIn wl
                                             , wlScanned = []
                                             , wlQueue   = wlQueue wl ++ wlScanned wl
                                             }
                                  st' = st { stWorkList       = wl'
{-  
                                           , stTrace          = SolveStep chr' subst (assocLElts bTodo') bDone : {- SolveDbg (ppwork >-< ppdbg) : -} stTrace st
-}    
                                           , stDoneCnstrSet   = Set.unions [Set.fromList bDone, Set.fromList $ map workCnstr $ take simpSz works, stDoneCnstrSet st]
                                           , stMatchCache     = if List.null bTodo' then stMatchCache st else Map.empty
                                           , stHistoryCount   = histCount + 1
                                           }
{-   
                                  chr'= subst `varUpd` chr
                                  ppwork = "workkey" >#< ppTreeTrieKey workHdKey >#< ":" >#< (ppBracketsCommas (map (ppTreeTrieKey . fst) workTl) >-< ppBracketsCommas (map (ppTreeTrieKey . fst) $ wlScanned wl))
                                             >-< "workkeys" >#< ppBracketsCommas (map ppTreeTrieKey keys)
                                             >-< "worktrie" >#< wlTrie wl
                                             >-< "schr" >#< schr
                                             >-< "usedin" >#< (ppBracketsCommasBlock $ map (\(k,s) -> ppKs k >#< ppBracketsCommas (map ppUsedByKey $ Set.toList s)) $ Map.toList $ wlUsedIn wl)
                                             >-< "usedin'" >#< (ppBracketsCommasBlock $ map (\(k,s) -> ppKs k >#< ppBracketsCommas (map ppUsedByKey $ Set.toList s)) $ Map.toList $ wlUsedIn wl')
                                         where ppKs ks = ppBracketsCommas $ map ppTreeTrieKey $ Set.toList ks
-}   
                              put
{-   
                                  $ addStats Map.empty
                                        [ ("chr",pp chr')
                                        , ("leftover sz", pp (length tlMatchY))
                                        , ("filtered out sz", pp (length tlMatchN))
                                        , ("new done sz", pp (length bDone))
                                        , ("new todo sz", pp (length bTodo))
                                        , ("wl queue sz", pp (length (wlQueue wl')))
                                        , ("wl usedin sz", pp (Map.size (wlUsedIn wl')))
                                        , ("done sz", pp (Set.size (stDoneCnstrSet st')))
                                        , ("hist cnt", pp histCount)
                                        ]
                                  $
-}   
                                  st'
                              expandMatch tlMatchY

                          expandMatch _ 
                            = iter
                          
                  _ -> do
                      put
{-   
                          $ addStats Map.empty
                                [ ("no match work", ppTreeTrieKey workHdKey)
                                , ("wl queue sz", pp (length (wlQueue wl')))
                                ]
                          $
-}    
                          st'
                      iter
                    where wl' = wl { wlScanned = workHd : wlScanned wl, wlQueue = workTl }
                          st' = stmatch { stWorkList = wl', stTrace = SolveDbg (ppdbg) : {- -} stTrace stmatch }
              where (matches,lastQuery,ppdbg,stats) = workMatches st
{-  
                    stmatch = addStats stats [("(a) workHd", ppTreeTrieKey workHdKey), ("(b) matches", ppBracketsCommasBlock [ s `varUpd` storedChr schr | ((schr,_),s) <- matches ])]
-}
                    stmatch =  
                                (st { stCountCnstr = scntInc workHdKey "workMatched" $ stCountCnstr st
                                    , stMatchCache = Map.insert workHdKey [] (stMatchCache st)
                                    , stLastQuery  = lastQuery
                                    })
            _ -> do
                return ()

        mkStats  stats new    = stats `Map.union` Map.fromList (assocLMapKey showPP new)
{-
        addStats stats new st = st { stTrace = SolveStats (mkStats stats new) : stTrace st }
-}
        addStats _     _   st = st

        workMatches st@(SolveState {stWorkList = WorkList {wlQueue = (workHd@(workHdKey,Work {workTime = workHdTm}) : _), wlTrie = wlTrie, wlUsedIn = wlUsedIn}, stHistoryCount = histCount, stLastQuery = lastQuery})
          | isJust mbInCache  = ( fromJust mbInCache
                                , lastQuery
                                , Pretty.empty, mkStats Map.empty [("cache sz",pp (Map.size (stMatchCache st)))]
                                )
          | otherwise         = ( r5
                                , foldr lqUnion lastQuery [ lqSingleton ck wks histCount | (_,(_,(ck,wks))) <- r23 ]
{-
                                -- , Pretty.empty
                                , pp2 >-< {- pp2b >-< pp2c >-< -} pp3
                                , mkStats Map.empty [("(1) lookup sz",pp (length r2)), ("(2) cand sz",pp (length r3)), ("(3) unused cand sz",pp (length r4)), ("(4) final cand sz",pp (length r5))]
-}
                                , Pretty.empty
                                , Map.empty
                                )
          where -- cache result, if present use that, otherwise the below computation
                mbInCache = Map.lookup workHdKey (stMatchCache st)
                
                -- results, stepwise computed for later reference in debugging output
                -- basic search result
                r2 :: [StoredCHR c g]                                       -- CHRs matching workHdKey
                r2  = concat                                                    -- flatten
                        $ TreeTrie.lookupResultToList                                   -- convert to list
                        $ chrTrieLookup chrLookupHowWildAtTrie workHdKey        -- lookup the store, allowing too many results
                        $ chrstoreTrie chrStore
                
                -- lookup further info in wlTrie, in particular to find out what has been done already
                r23 :: [( StoredCHR c g                                     -- the CHR
                        , ( [( [(CHRKey c, Work c)]                             -- for each CHR the list of constraints, all possible work matches
                             , [(CHRKey c, Work c)]
                             )]
                          , (CHRKey c, Set.Set (CHRKey c))
                        ) )]
                r23 = map (\c -> (c, slvCandidate workHdKey lastQuery wlTrie c)) r2
                
                -- possible matches
                r3, r4
                    :: [( StoredCHR c g                                     -- the matched CHR
                        , ( [CHRKey c]                                            -- possible matching constraints (matching with the CHR constraints), as Keys, as Works
                          , [Work c]
                        ) )]
                r3  = concatMap (\(c,cands) -> zip (repeat c) (map unzip $ slvCombine cands)) $ r23
                
                -- same, but now restricted to not used earlier as indicated by the worklist
                r4  = filter (not . slvIsUsedByPropPart wlUsedIn) r3
                
                -- finally, the 'real' match of the 'real' constraint, yielding (by tupling) substitutions instantiating the found trie matches
                r5  :: [( ( StoredCHR c g
                          , ( [CHRKey c]          
                            , [Work c]
                          ) )
                        , s
                        )]
                r5  = mapMaybe (\r@(chr,kw@(_,works)) -> fmap (\s -> (r,s)) $ slvMatch env chr (map workCnstr works)) r4
{-
                -- debug info
                pp2  = "lookups"    >#< ("for" >#< ppTreeTrieKey workHdKey >-< ppBracketsCommasBlock r2)
                -- pp2b = "cand1"      >#< (ppBracketsCommasBlock $ map (ppBracketsCommasBlock . map (ppBracketsCommasBlock . map (\(k,w) -> ppTreeTrieKey k >#< w)) . fst . candidate) r2)
                -- pp2c = "cand2"      >#< (ppBracketsCommasBlock $ map (ppBracketsCommasBlock . map (ppBracketsCommasBlock) . combineToDistinguishedElts . fst . candidate) r2)
                pp3  = "candidates" >#< (ppBracketsCommasBlock $ map (\(chr,(ks,ws)) -> "chr" >#< chr >-< "keys" >#< ppBracketsCommas (map ppTreeTrieKey ks) >-< "works" >#< ppBracketsCommasBlock ws) $ r3)
-}
        initState st = st { stWorkList = wlInsert (stHistoryCount st) wlnew $ stWorkList st, stDoneCnstrSet = Set.unions [Set.fromList done, stDoneCnstrSet st] }
                     where (wlnew,done) = splitDone cnstrs
        splitDone  = partition cnstrRequiresSolve

-- | Extract candidates matching a CHRKey.
--   Return a list of CHR matches,
--     each match expressed as the list of constraints (in the form of Work + Key) found in the workList wlTrie, thus giving all combis with constraints as part of a CHR,
--     partititioned on before or after last query time (to avoid work duplication later)
slvCandidate
  :: (Ord (TTKey c), PP (TTKey c))
     => CHRKey c
     -> LastQuery c
     -> WorkTrie c
     -> StoredCHR c g
     -> ( [( [(CHRKey c, Work c)]
           , [(CHRKey c, Work c)]
           )]
        , (CHRKey c, Set.Set (CHRKey c))
        )
slvCandidate workHdKey lastQuery wlTrie (StoredCHR {storedIdent = (ck,_), storedKeys = ks, storedChr = chr})
  = ( map (maybe (lkup chrLookupHowExact workHdKey) (lkup chrLookupHowWildAtKey)) ks
    , ( ck
      , Set.fromList $ map (maybe workHdKey id) ks
    ) )
  where lkup how k = partition (\(_,w) -> workTime w < lastQueryTm) $ map (\w -> (workKey w,w)) $ TreeTrie.lookupResultToList $ chrTrieLookup how k wlTrie
                   where lastQueryTm = lqLookupW k $ lqLookupC ck lastQuery
{-# INLINE slvCandidate #-}

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

-- | Check whether the CHR propagation part of a match already has been used (i.e. propagated) earlier,
--   this to avoid duplicate propagation.
slvIsUsedByPropPart
  :: (Ord k, Ord (TTKey c))
     => Map.Map (Set.Set k) (Set.Set (UsedByKey c))
     -> (StoredCHR c g, ([k], t))
     -> Bool
slvIsUsedByPropPart wlUsedIn (chr,(keys,_))
  = fnd $ drop (storedSimpSz chr) keys
  where fnd k = maybe False (storedIdent chr `Set.member`) $ Map.lookup (Set.fromList k) wlUsedIn
{-# INLINE slvIsUsedByPropPart #-}

-- | Match the stored CHR with a set of possible constraints, giving a substitution on success
slvMatch
  :: ( CHREmptySubstitution s
     , CHRMatchable env c s
     , CHRCheckable env g s
     , VarLookupCmb s s
     )
     => env -> StoredCHR c g -> [c] -> Maybe s
slvMatch env chr cnstrs
  = foldl cmb (Just chrEmptySubst) $ matches chr cnstrs ++ checks chr
  where matches (StoredCHR {storedChr = Rule {chrHead = hc}}) cnstrs
          = zipWith mt hc cnstrs
          where mt cFr cTo subst = chrMatchTo env subst cFr cTo
        checks (StoredCHR {storedChr = Rule {chrGuard = gd}})
          = map chk gd
          where chk g subst = chrCheck env subst g
        cmb (Just s) next = fmap (|+> s) $ next s
        cmb _        _    = Nothing
{-# INLINE slvMatch #-}

-------------------------------------------------------------------------------------------
--- Instances: Serialize
-------------------------------------------------------------------------------------------

instance (Ord (TTKey c), Serialize (TTKey c), Serialize c, Serialize g) => Serialize (CHRStore c g) where
  sput (CHRStore a) = sput a
  sget = liftM CHRStore sget
  
instance (Ord (TTKey c), Serialize (TTKey c), Serialize c, Serialize g) => Serialize (StoredCHR c g) where
  sput (StoredCHR a b c d) = sput a >> sput b >> sput c >> sput d
  sget = liftM4 StoredCHR sget sget sget sget

