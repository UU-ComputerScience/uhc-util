module UHC.Util.CHR.Solve.TreeTrie.Examples.Term.Main
  ( RunOpt(..)
  , Verbosity(..)

  , runFile
  )
  where

import           Data.Maybe
import           System.IO
import           Control.Monad
import           Control.Monad.IO.Class
import qualified Data.Set as Set

import           UU.Parsing
import           UU.Scanner

import           UHC.Util.Substitutable
import           UHC.Util.Pretty
import           UHC.Util.CHR.Rule
import           UHC.Util.CHR.GTerm.Parser
import           UHC.Util.CHR.Solve.TreeTrie.MonoBacktrackPrio as MBP
import           UHC.Util.CHR.Solve.TreeTrie.Examples.Term.AST
-- import           UHC.Util.CHR.Solve.TreeTrie.Examples.Term.Parser

data RunOpt
  = RunOpt_DebugTrace               -- ^ include debugging trace in output
  | RunOpt_SucceedOnLeftoverWork    -- ^ left over unresolvable (non residue) work is also a successful result
  | RunOpt_SucceedOnFailedSolve     -- ^ failed solve is considered also a successful result, with the failed constraint as a residue
  | RunOpt_Verbosity Verbosity
  deriving (Eq)

mbRunOptVerbosity :: [RunOpt] -> Maybe Verbosity
mbRunOptVerbosity []                       = Nothing
mbRunOptVerbosity (RunOpt_Verbosity v : _) = Just v
mbRunOptVerbosity (_                  : r) = mbRunOptVerbosity r

-- | Run file with options
runFile :: [RunOpt] -> FilePath -> IO ()
runFile runopts f = do
    -- scan, parse
    msg $ "READ " ++ f    
    mbParse <- parseFile f
    case mbParse of
      Left e -> putPPLn e
      Right (prog, query) -> do
        let sopts = defaultCHRSolveOpts
                      { chrslvOptSucceedOnLeftoverWork = RunOpt_SucceedOnLeftoverWork `elem` runopts
                      , chrslvOptSucceedOnFailedSolve  = RunOpt_SucceedOnFailedSolve  `elem` runopts
                      }
            mbp :: CHRMonoBacktrackPrioT C G P P S E IO (SolverResult S)
            mbp = do
              -- print program
              liftIO $ putPPLn $ "Rules" >-< indent 2 (vlist $ map pp prog)
              -- freshen query vars
              query <- slvFreshSubst Set.empty query >>= \s -> return $ s `varUpd` query
              -- print query
              liftIO $ putPPLn $ "Query" >-< indent 2 (vlist $ map pp query)
              mapM_ addRule prog
              mapM_ addConstraintAsWork query
              -- solve
              liftIO $ msg $ "SOLVE " ++ f
              r <- chrSolve sopts ()
              let verbosity = maximum $ [Verbosity_Quiet] ++ maybeToList (mbRunOptVerbosity runopts) ++ (if RunOpt_DebugTrace `elem` runopts then [Verbosity_ALot] else [])
              ppSolverResult verbosity r >>= \sr -> liftIO $ putPPLn $ "Solution" >-< indent 2 sr
              return r
        runCHRMonoBacktrackPrioT (emptyCHRGlobState) (emptyCHRBackState {- _chrbstBacktrackPrio=0 -}) {- 0 -} mbp
    
        -- done
        msg $ "DONE " ++ f
    
  where
    msg m = putStrLn $ "---------------- " ++ m ++ " ----------------"
    dummy = undefined :: Rule C G P P

-- | run some test programs
mainTerm = do
  forM_
      [
        "bug2"
      -- , "queens"
      -- , "leq"
      -- , "var"
      -- , "ruleprio"
      -- , "backtrack3"
      -- , "unify"
      -- , "antisym"
      ] $ \f -> do
    let f' = "test/" ++ f ++ ".chr"
    runFile
      [ RunOpt_SucceedOnLeftoverWork
      , RunOpt_DebugTrace
      ] f'
  

{-
-}
