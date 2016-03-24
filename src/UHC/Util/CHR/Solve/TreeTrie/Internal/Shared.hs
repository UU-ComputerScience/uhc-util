{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, UndecidableInstances, NoMonomorphismRestriction, MultiParamTypeClasses #-}

-------------------------------------------------------------------------------------------
-- | CHR TreeTrie based solver shared internals, for all solvers
-------------------------------------------------------------------------------------------

module UHC.Util.CHR.Solve.TreeTrie.Internal.Shared
  ( CHRTrie'
  , CHRTrieKey

  , chrToKey
  , chrToWorkKey

  , CHRKey

  , WorkTime
  , initWorkTime
  
  , WorkKey
  , Work(..)
  
  , SolveStep'(..)
  , SolveTrace'
  , emptySolveTrace
  , ppSolveTrace
  
  )
  where

import           UHC.Util.CHR.Key
import           UHC.Util.TreeTrie as TreeTrie

import           UHC.Util.Pretty as Pretty
import           UHC.Util.AssocL

import qualified Data.Map as Map

-------------------------------------------------------------------------------------------
--- Choice of Trie structure
-------------------------------------------------------------------------------------------

type CHRTrie' k v = TreeTrie.TreeTrie (TTKey k) v
type CHRTrieKey v = TreeTrie.TreeTrieKey (TTKey v)

-- | Obtain key for use in rule
chrToKey :: (TTKeyable x, TrTrKey x ~ TTKey x) => x -> CHRTrieKey x
chrToKey = ttkFixate . toTTKey
{-# INLINE chrToKey #-}

-- | Obtain key for use in to be solved context (i.e. work)
chrToWorkKey :: (TTKeyable x) => x -> CHRTrieKey x
chrToWorkKey = ttkFixate . toTTKey' (defaultTTKeyableOpts {ttkoptsVarsAsWild = False})
{-# INLINE chrToWorkKey #-}

-------------------------------------------------------------------------------------------
--- CHR key
-------------------------------------------------------------------------------------------

-- | Convenience alias for key into CHR store
type CHRKey v = CHRTrieKey v

-------------------------------------------------------------------------------------------
--- WorkTime, the time/history counter for solver work
-------------------------------------------------------------------------------------------

-- | All solver constraints are identified individually with a timestamp, also serving as its identification depending on the solver
type WorkTime = Int

initWorkTime :: WorkTime
initWorkTime = 0

-------------------------------------------------------------------------------------------
--- Solver work and/or residual (non)work
-------------------------------------------------------------------------------------------

type WorkKey       v = CHRKey v

-- | A chunk of work to do when solving, a constraint + sequence nr
data Work c
  = Work
      { workKey     :: WorkKey c                    -- ^ the key into the CHR store
      , workCnstr   :: !c                           -- ^ the constraint to be reduced
      , workTime    :: WorkTime                     -- ^ the timestamp identification at which the work was added
      }
  | Residue
      { workCnstr   :: !c                           -- ^ the residual constraint
      }

type instance TTKey (Work c) = TTKey c

instance Show (Work c) where
  show _ = "SolveWork"

instance (PP (TTKey c), PP c) => PP (Work c) where
  pp (Work    k c t) = ppParens k >|< "@" >|< t >#< c
  pp (Residue   c  ) = pp                           c

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

emptySolveTrace :: SolveTrace' c r s
emptySolveTrace = []

instance Show (SolveStep' c r s) where
  show _ = "SolveStep"

instance (PP r, PP c) => {- (PP c, PP g) => -} PP (SolveStep' c r s) where
  pp (SolveStep   step _ todo done) = "STEP" >#< (step >-< "new todo:" >#< ppBracketsCommas todo >-< "new done:" >#< ppBracketsCommas done)
  pp (SolveStats  stats           ) = "STATS"  >#< (ppAssocLV (Map.toList stats))
  pp (SolveDbg    p               ) = "DBG"  >#< p

ppSolveTrace :: (PP r, PP c) => {- (PP s, PP c, PP g) => -} SolveTrace' c r s -> PP_Doc
ppSolveTrace tr = ppBracketsCommasBlock [ pp st | st <- tr ]

