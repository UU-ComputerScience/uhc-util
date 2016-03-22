{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, UndecidableInstances, NoMonomorphismRestriction, MultiParamTypeClasses, TemplateHaskell, FunctionalDependencies #-}

-------------------------------------------------------------------------------------------
--- CHR solver
-------------------------------------------------------------------------------------------

{-|
Under development (as of 20160218).

Solver is:
- Monomorphic, i.e. the solver is polymorph but therefore can only work on 1 type of constraints, rules, etc.
- Knows about variables for which substitutions can be found, substitutions are part of found solutions.
- Backtracking (on variable bindings/substitutions), multiple solution alternatives are explored.
- Found rules are applied in an order described by priorities associated with rules. Priorities can be dynamic, i.e. depend on terms in rules.
-}

module UHC.Util.CHR.Solve.TreeTrie.MonoBacktrackPrio
  ( CHRGlobState(..)
  , emptyCHRGlobState
  
  , CHRBackState(..)
  , emptyCHRBackState
  
  , emptyCHRStore
  
  , CHRMonoBacktrackPrioT
  , MonoBacktrackPrio
  , runCHRMonoBacktrackPrioT
  
  , addRule
  
  , addConstraintAsWork
  
  , chrSolve
  
  , getSolveTrace
  
{-
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
  
  , SolveStep'(..)
  , SolveStep
  , SolveTrace
  , ppSolveTrace
  
  , SolveState
  , emptySolveState
  , solveStateResetDone
  , chrSolveStateDoneConstraints
  , chrSolveStateTrace
-}
  
  , IsCHRSolvable(..)
{-
  , chrSolve'
  , chrSolve''
  , chrSolveM
  )
-}
  )
  where

import           UHC.Util.CHR.Base
import           UHC.Util.CHR.Key
import           UHC.Util.CHR.Rule
import           UHC.Util.CHR.Solve.TreeTrie.Internal.Shared
import           UHC.Util.Substitutable
import           UHC.Util.VarLookup
import           UHC.Util.VarMp
import           UHC.Util.AssocL
import           UHC.Util.TreeTrie as TreeTrie
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Sequence as Seq
import           Data.List as List
import           Data.Typeable
-- import           Data.Data
import           Data.Maybe
import           UHC.Util.Pretty as Pretty
import           UHC.Util.Serialize
import           Control.Monad
import           Control.Monad.State.Strict
import           UHC.Util.Utils
import           UHC.Util.Lens
import           Control.Monad.LogicState

-------------------------------------------------------------------------------------------
--- A CHR as stored
-------------------------------------------------------------------------------------------

-- | Index into table of CHR's, allowing for indirection required for sharing of rules by search for different constraints in the head
type CHRInx = Int

-- | Index into rule and head constraint
data CHRConstraintInx = CHRConstraintInx {-# UNPACK #-} !CHRInx !Int
  deriving Show

instance PP CHRConstraintInx where
  pp (CHRConstraintInx i j) = i >|< "." >|< j

-- | A CHR as stored in a CHRStore, requiring additional info for efficiency
data StoredCHR c g p
  = StoredCHR
      { _storedChr       :: !(Rule c g p)                          -- ^ the Rule
      , _storedCHRInx    :: !CHRInx                                -- ^ index of constraint for which is keyed into store
      -- , storedKeys      :: ![Maybe (CHRKey c)]                  -- ^ keys of all constraints; at storedCHRInx: Nothing
      -- , storedIdent     :: !(UsedByKey c)                       -- ^ the identification of a CHR, used for propagation rules (see remark at begin)
      }
  deriving (Typeable)

mkLabel ''StoredCHR

type instance TTKey (StoredCHR c g p) = TTKey c

{-
instance (TTKeyable (Rule c g p)) => TTKeyable (StoredCHR c g p) where
  toTTKey' o schr = toTTKey' o $ storedChr schr

-- | The size of the simplification part of a CHR
storedSimpSz :: StoredCHR c g p -> Int
storedSimpSz = ruleSimpSz . storedChr
{-# INLINE storedSimpSz #-}
-}

-- | A CHR store is a trie structure
data CHRStore cnstr guard prio
  = CHRStore
      { _chrstoreTrie    :: CHRTrie' cnstr [CHRConstraintInx]                       -- ^ map from the search key of a rule to the index into tabl
      , _chrstoreTable   :: IntMap.IntMap (StoredCHR cnstr guard prio)      -- ^ (possibly multiple) rules for a key
      }
  deriving (Typeable)

mkLabel ''CHRStore

emptyCHRStore :: CHRStore cnstr guard prio
emptyCHRStore = CHRStore TreeTrie.empty IntMap.empty

-------------------------------------------------------------------------------------------
--- Store holding work, split up in global and backtrackable part
-------------------------------------------------------------------------------------------

type WorkInx = WorkTime

data WorkStore cnstr
  = WorkStore
      { _wkstoreTrie     :: CHRTrie' cnstr [WorkInx]                -- ^ map from the search key of a constraint to index in table
      , _wkstoreTable    :: IntMap.IntMap (Work cnstr)      -- ^ all the work ever entered
      }
  deriving (Typeable)

mkLabel ''WorkStore

emptyWorkStore :: WorkStore cnstr
emptyWorkStore = WorkStore TreeTrie.empty IntMap.empty

data WorkQueue
  = WorkQueue
      { _wkqueueQueue    :: Seq.Seq WorkInx                -- ^ queue holding the work to be done, as index into work table
      }
  deriving (Typeable)

mkLabel ''WorkQueue

emptyWorkQueue :: WorkQueue
emptyWorkQueue = WorkQueue Seq.empty

-------------------------------------------------------------------------------------------
--- Index into CHR and head constraint
-------------------------------------------------------------------------------------------


-------------------------------------------------------------------------------------------
--- The CHR monad, state, etc. Used to interact with store and solver
-------------------------------------------------------------------------------------------

-- | Global state
data CHRGlobState cnstr guard prio subst
  = CHRGlobState
      { _chrgstStore                 :: !(CHRStore cnstr guard prio)                     -- ^ Actual database of rules, to be searched
      , _chrgstNextFreeRuleInx       :: !CHRInx                                          -- ^ Next free rule identification, used by solving to identify whether a rule has been used for a constraint.
                                                                                         --   The numbering is applied to constraints inside a rule which can be matched.
      , _chrgstNextFreshVarId        :: !(ExtrValVarKey (Rule cnstr guard prio))         -- ^ The next free id used for a fresh variable
      , _chrgstWorkStore             :: !(WorkStore cnstr)                               -- ^ Actual database of solvable constraints
      , _chrgstNextFreeWorkInx       :: !WorkTime                                        -- ^ Next free work/constraint identification, used by solving to identify whether a rule has been used for a constraint.
      , _chrgstTrace                 :: SolveTrace' cnstr (StoredCHR cnstr guard prio) subst
      }
  deriving (Typeable)

mkLabel ''CHRGlobState

emptyCHRGlobState :: Num (ExtrValVarKey c) => CHRGlobState c g p s
emptyCHRGlobState = CHRGlobState emptyCHRStore 0 0 emptyWorkStore initWorkTime emptySolveTrace

-- | Backtrackable state
data CHRBackState subst
  = CHRBackState
      { _chrbstSubst                 :: !subst                           -- ^ subst for variable bindings
      , _chrbstWorkQueue             :: !WorkQueue                       -- ^ work queue
      }
  deriving (Typeable)

mkLabel ''CHRBackState

emptyCHRBackState :: CHREmptySubstitution s => CHRBackState s
emptyCHRBackState = CHRBackState chrEmptySubst emptyWorkQueue

-- | Monad for CHR, taking from 'LogicStateT' the state and backtracking behavior
type CHRMonoBacktrackPrioT cnstr guard prio subst env m a = LogicStateT (CHRGlobState cnstr guard prio subst) (CHRBackState subst) m a

-- | All required behavior, as class alias
class ( IsCHRSolvable env cnstr guard prio subst
      , Monad m
      , Ord (TTKey cnstr)
      , TTKeyable cnstr
      -- , TTKey cnstr ~ TrTrKey cnstr
      ) => MonoBacktrackPrio cnstr guard prio subst env m
         | cnstr guard prio subst -> env

runCHRMonoBacktrackPrioT :: Monad m => CHRGlobState cnstr guard prio subst -> CHRBackState subst -> CHRMonoBacktrackPrioT cnstr guard prio subst env m a -> m [a]
runCHRMonoBacktrackPrioT gs bs m = observeAllT (gs,bs) m

getSolveTrace :: (PP c, PP g, MonoBacktrackPrio c g p s e m) => CHRMonoBacktrackPrioT c g p s e m PP_Doc
getSolveTrace = fmap (ppSolveTrace . reverse) $ getl $ fstl ^* chrgstTrace

-------------------------------------------------------------------------------------------
--- CHR store, API for adding rules
-------------------------------------------------------------------------------------------


-- deriving instance (Data (TTKey cnstr), Ord (TTKey cnstr), Data cnstr, Data guard) => Data (CHRStore cnstr guard prio)

{-
-- | Combine lists of stored CHRs by concat, adapting their identification nr to be unique
cmbStoredCHRs :: [StoredCHR c g p] -> [StoredCHR c g p] -> [StoredCHR c g p]
cmbStoredCHRs s1 s2
  = map (\s@(StoredCHR {storedIdent=(k,nr)}) -> s {storedIdent = (k,nr+l)}) s1 ++ s2
  where l = length s2
-}

instance Show (StoredCHR c g p) where
  show _ = "StoredCHR"

ppStoredCHR :: (PP c, PP g, PP p) => StoredCHR c g p -> PP_Doc
ppStoredCHR c@(StoredCHR {})
  = _storedChr c
    >-< indent 2
          (ppParensCommas
            [ pp $ _storedCHRInx c
            -- , pp $ storedSimpSz c
            -- , "keys" >#< (ppBracketsCommas $ map (maybe (pp "?") ppTreeTrieKey) $ storedKeys c)
            -- , "ident" >#< ppParensCommas [ppTreeTrieKey idKey,pp idSeqNr]
            ])

instance (PP c, PP g, PP p) => PP (StoredCHR c g p) where
  pp = ppStoredCHR

{-
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
-}

-- | Add a rule as a CHR
addRule :: MonoBacktrackPrio c g p s e m => Rule c g p -> CHRMonoBacktrackPrioT c g p s e m ()
addRule chr = do
    i <- modifyAndGet (fstl ^* chrgstNextFreeRuleInx) $ \i -> (i, i + 1)
{-
    focus (fstl ^* chrgstStore) $ do
      chrstoreTable =$: IntMap.insert i (StoredCHR chr i)
      chrstoreTrie =$: \t ->
        foldr (TreeTrie.unionWith (++)) t [ TreeTrie.singleton (chrToKey c) [CHRConstraintInx i j] | (c,j) <- zip (ruleHead chr) [0..] ]
-}
    fstl ^* chrgstStore ^* chrstoreTable =$: IntMap.insert i (StoredCHR chr i)
    fstl ^* chrgstStore ^* chrstoreTrie =$: \t ->
      foldr (TreeTrie.unionWith (++)) t [ TreeTrie.singleton (chrToKey c) [CHRConstraintInx i j] | (c,j) <- zip (ruleHead chr) [0..] ]
    return ()

-- | Add a constraint to be solved
addConstraintAsWork :: MonoBacktrackPrio c g p s e m => c -> CHRMonoBacktrackPrioT c g p s e m ()
addConstraintAsWork c = do
    i <- modifyAndGet (fstl ^* chrgstNextFreeWorkInx) $ \i -> (i, i + 1)
    let k = chrToWorkKey c
        w = Work k c i
    fstl ^* chrgstWorkStore ^* wkstoreTable =$: IntMap.insert i w
    fstl ^* chrgstWorkStore ^* wkstoreTrie =$: TreeTrie.insertByKeyWith (++) k [i]
    sndl ^* chrbstWorkQueue ^* wkqueueQueue =$: (Seq.|> i)
    return ()

{-

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
    , let chrs = [chr | (StoredCHR {storedChr = chr, storedCHRInx = 0}) <- e]
    , not $ Prelude.null chrs
    ]

chrStoreElems :: (Ord (TTKey c)) => CHRStore c g p -> [Rule c g p]
chrStoreElems = concatMap snd . chrStoreToList

ppCHRStore :: (PP c, PP g, PP p, Ord (TTKey c), PP (TTKey c)) => CHRStore c g p -> PP_Doc
ppCHRStore = ppCurlysCommasBlock . map (\(k,v) -> ppTreeTrieKey k >-< indent 2 (":" >#< ppBracketsCommasBlock v)) . chrStoreToList

ppCHRStore' :: (PP c, PP g, PP p, Ord (TTKey c), PP (TTKey c)) => CHRStore c g p -> PP_Doc
ppCHRStore' = ppCurlysCommasBlock . map (\(k,v) -> ppTreeTrieKey k >-< indent 2 (":" >#< ppBracketsCommasBlock v)) . chrTrieToListByKey . chrstoreTrie

-}

-------------------------------------------------------------------------------------------
--- Solver trace
-------------------------------------------------------------------------------------------

{-
type SolveStep  c g p s = SolveStep'  c (Rule c g p) s
type SolveTrace c g p s = SolveTrace' c (Rule c g p) s
-}

-------------------------------------------------------------------------------------------
--- Cache for maintaining which WorkKey has already had a match
-------------------------------------------------------------------------------------------

{-
-- type SolveMatchCache c g p s = Map.Map (CHRKey c) [((StoredCHR c g p,([WorkKey c],[Work c])),s)]
-- type SolveMatchCache c g p s = Map.Map (WorkKey c) [((StoredCHR c g p,([WorkKey c],[Work c])),s)]
type SolveMatchCache c g p s = SolveMatchCache' c (StoredCHR c g p) s
-}

-------------------------------------------------------------------------------------------
--- Solve state
-------------------------------------------------------------------------------------------

{-
type SolveState c g p s = SolveState' c (Rule c g p) (StoredCHR c g p) s
-}

-------------------------------------------------------------------------------------------
--- Solver
-------------------------------------------------------------------------------------------

-- | (Class alias) API for solving requirements
class ( IsCHRConstraint env c s
      , IsCHRGuard env g s
      , IsCHRPrio env p s
      , VarLookupCmb s s
      , VarUpdatable s s
      , CHREmptySubstitution s
      , TrTrKey c ~ TTKey c
      ) => IsCHRSolvable env c g p s
{-
-}

-- | (Dev) solve
chrSolve :: MonoBacktrackPrio c g p s e m => CHRMonoBacktrackPrioT c g p s e m ()
chrSolve = do
    wq <- getl $ sndl ^* chrbstWorkQueue ^* wkqueueQueue
    case Seq.viewl wq of
      Seq.EmptyL -> return ()
      workInx Seq.:< _ -> do
        work <- lkupWork workInx
        foundChrInxs <- fmap (Map.unionsWith (++) . map (\(CHRConstraintInx i j) -> Map.singleton i [j]) . concat . TreeTrie.lookupResultToList . TreeTrie.lookupPartialByKey TTL_WildInTrie (workKey work))
          $ getl $ fstl ^* chrgstStore ^* chrstoreTrie
        foundChrs <- forM (Map.toList foundChrInxs) $ \(chrInx,rlInxs) -> do
          chr <- lkupChr chrInx
          return (chrInx, chr, rlInxs)
        fstl ^* chrgstTrace =$: (SolveDbg
          ("wk" >#< work >-< "chrs" >#< vlist [ ci >|< ppParensCommas is >|< ":" >#< c | (ci,c,is) <- foundChrs ])
           :)
  where
    lkupWork i = fmap (IntMap.findWithDefault (panic "MBP.chrSolve.wkstoreTable.lookup") i) $ getl $ fstl ^* chrgstWorkStore ^* wkstoreTable
    lkupChr  i = fmap (IntMap.findWithDefault (panic "MBP.chrSolve.chrstoreTable.lookup") i) $ getl $ fstl ^* chrgstStore ^* chrstoreTable

{-
chrSolve
  :: forall env c g p s .
     ( IsCHRSolvable env c g p s
     )
     => env
     -> CHRStore c g p
     -> [c]
     -> [c]
chrSolve env chrStore cnstrs
  = work ++ done
  where (work, done, _ :: SolveTrace c g p s) = chrSolve' [] env chrStore cnstrs
-}

{-
-- | Solve
chrSolve'
  :: forall env c g p s .
     ( IsCHRSolvable env c g p s
     )
     => [CHRTrOpt]
     -> env
     -> CHRStore c g p
     -> [c]
     -> ([c],[c],SolveTrace c g p s)
chrSolve' tropts env chrStore cnstrs
  = (wlToList (stWorkList finalState), stDoneCnstrs finalState, stTrace finalState)
  where finalState = chrSolve'' tropts env chrStore cnstrs emptySolveState

-- | Solve
chrSolve''
  :: forall env c g p s .
     ( IsCHRSolvable env c g p s
     )
     => [CHRTrOpt]
     -> env
     -> CHRStore c g p
     -> [c]
     -> SolveState c g p s
     -> SolveState c g p s
chrSolve'' tropts env chrStore cnstrs prevState
  = flip execState prevState $ chrSolveM tropts env chrStore cnstrs

-- | Solve
chrSolveM
  :: forall env c g p s .
     ( IsCHRSolvable env c g p s
     )
     => [CHRTrOpt]
     -> env
     -> CHRStore c g p
     -> [c]
     -> State (SolveState c g p s) ()
chrSolveM tropts env chrStore cnstrs = do
    modify initState
    iter
{-
    modify $
            addStats Map.empty
                [ ("workMatches",ppAssocLV [(ppTreeTrieKey k,pp (fromJust l))
                | (k,c) <- Map.toList $ stCountCnstr st, let l = Map.lookup "workMatched" c, isJust l])
                ]
-}
    modify $ \st -> st {stMatchCache = Map.empty}
  where iter = do
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
                    where -- expandMatch :: SolveState c g p s -> [((StoredCHR c g p, ([WorkKey c], [Work c])), s)] -> SolveState c g p s
                          expandMatch ( ( ( schr@(StoredCHR {storedIdent = chrId, storedChr = chr@(Rule {ruleBody = b, ruleSimpSz = simpSz})})
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
                r2 :: [StoredCHR c g p]                                       -- CHRs matching workHdKey
                r2  = concat                                                    -- flatten
                        $ TreeTrie.lookupResultToList                                   -- convert to list
                        $ chrTrieLookup chrLookupHowWildAtTrie workHdKey        -- lookup the store, allowing too many results
                        $ chrstoreTrie chrStore
                
                -- lookup further info in wlTrie, in particular to find out what has been done already
                r23 :: [( StoredCHR c g p                                     -- the CHR
                        , ( [( [(CHRKey c, Work c)]                             -- for each CHR the list of constraints, all possible work matches
                             , [(CHRKey c, Work c)]
                             )]
                          , (CHRKey c, Set.Set (CHRKey c))
                        ) )]
                r23 = map (\c -> (c, slvCandidate workHdKey lastQuery wlTrie c)) r2
                
                -- possible matches
                r3, r4
                    :: [( StoredCHR c g p                                     -- the matched CHR
                        , ( [CHRKey c]                                            -- possible matching constraints (matching with the CHR constraints), as Keys, as Works
                          , [Work c]
                        ) )]
                r3  = concatMap (\(c,cands) -> zip (repeat c) (map unzip $ slvCombine cands)) $ r23
                
                -- same, but now restricted to not used earlier as indicated by the worklist
                r4  = filter (not . slvIsUsedByPropPart wlUsedIn) r3
                
                -- finally, the 'real' match of the 'real' constraint, yielding (by tupling) substitutions instantiating the found trie matches
                r5  :: [( ( StoredCHR c g p
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
     -> StoredCHR c g p
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

-- | Check whether the CHR propagation part of a match already has been used (i.e. propagated) earlier,
--   this to avoid duplicate propagation.
slvIsUsedByPropPart
  :: (Ord k, Ord (TTKey c))
     => Map.Map (Set.Set k) (Set.Set (UsedByKey c))
     -> (StoredCHR c g p, ([k], t))
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
     => env -> StoredCHR c g p -> [c] -> Maybe s
slvMatch env chr cnstrs
  = foldl cmb (Just chrEmptySubst) $ matches chr cnstrs ++ checks chr
  where matches (StoredCHR {storedChr = Rule {ruleHead = hc}}) cnstrs
          = zipWith mt hc cnstrs
          where mt cFr cTo subst = chrMatchTo env subst cFr cTo
        checks (StoredCHR {storedChr = Rule {ruleGuard = gd}})
          = map chk gd
          where chk g subst = chrCheck env subst g
        cmb (Just s) next = fmap (|+> s) $ next s
        cmb _        _    = Nothing
{-# INLINE slvMatch #-}

-}

-------------------------------------------------------------------------------------------
--- Instances: Serialize
-------------------------------------------------------------------------------------------

{-
instance (Ord (TTKey c), Serialize (TTKey c), Serialize c, Serialize g, Serialize p) => Serialize (CHRStore c g p) where
  sput (CHRStore a) = sput a
  sget = liftM CHRStore sget
  
instance (Serialize c, Serialize g, Serialize p, Serialize (TTKey c)) => Serialize (StoredCHR c g p) where
  sput (StoredCHR a b c d) = sput a >> sput b >> sput c >> sput d
  sget = liftM4 StoredCHR sget sget sget sget

-}
