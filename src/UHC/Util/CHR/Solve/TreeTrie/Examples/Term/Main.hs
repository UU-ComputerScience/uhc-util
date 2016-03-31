module UHC.Util.CHR.Solve.TreeTrie.Examples.Term.Main
  ( RunOpt(..)

  , runFile
  )
  where

import           System.IO
import           Control.Monad
import           Control.Monad.IO.Class

import           UU.Parsing
import           UU.Scanner

import           UHC.Util.Pretty
import           UHC.Util.CHR.Rule
import           UHC.Util.CHR.Rule.Parser
import qualified UHC.Util.CHR.Solve.TreeTrie.MonoBacktrackPrio as MBP
import           UHC.Util.CHR.Solve.TreeTrie.Examples.Term.AST
import           UHC.Util.CHR.Solve.TreeTrie.Examples.Term.Parser

data RunOpt
  = RunOpt_DebugTrace       -- ^ include debugging trace in output
  deriving (Eq)

runFile :: [RunOpt] -> FilePath -> IO ()
runFile runopts f = do
    msg $ "READ " ++ f
    toks <- scanFile
      ([] ++ scanChrExtraKeywordsTxt dummy)
      (["==", "\\", "=>", "<=>", ".", "+", "*", "-", "::", "@", "|", "\\/", "?"] ++ scanChrExtraKeywordsOps dummy)
      ("()," ++ scanChrExtraSpecialChars dummy)
      ("=/\\><.+*-@:|?" ++ scanChrExtraOpChars dummy)
      f
    (prog, query) <- parseIOMessage show pProg toks
    putPPLn $ "Rules" >-< indent 2 (vlist $ map pp prog)
    putPPLn $ "Query" >-< indent 2 (vlist $ map pp query)
    msg $ "SOLVE " ++ f
    let mbp :: MBP.CHRMonoBacktrackPrioT C G P P S E IO (MBP.SolverResult S)
        mbp = do
          mapM_ MBP.addRule prog
          mapM_ MBP.addConstraintAsWork query
          r <- MBP.chrSolve ()
          MBP.ppSolverResult (RunOpt_DebugTrace `elem` runopts) r >>= (liftIO . putPPLn)
          return r
    MBP.runCHRMonoBacktrackPrioT (MBP.emptyCHRGlobState) (MBP.emptyCHRBackState) mbp
    msg $ "DONE " ++ f
  where
    msg m = putStrLn $ "---------------- " ++ m ++ " ----------------"
    dummy = undefined :: Rule C G P P

mainTerm = do
  forM_
      [ "unify"
      -- , "antisym"
      ] $ \f -> do
    let f' = "test/" ++ f ++ ".chr"
    runFile [RunOpt_DebugTrace] f'
  

{-
-}
