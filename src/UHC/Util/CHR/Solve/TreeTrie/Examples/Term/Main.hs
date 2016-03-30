module UHC.Util.CHR.Solve.TreeTrie.Examples.Term.Main where

import           System.IO
import           Control.Monad
import           Control.Monad.IO.Class

import           UU.Parsing
import           UU.Scanner

import           UHC.Util.Pretty
import qualified UHC.Util.CHR.Solve.TreeTrie.MonoBacktrackPrio as MBP
import           UHC.Util.CHR.Solve.TreeTrie.Examples.Term.AST
import           UHC.Util.CHR.Solve.TreeTrie.Examples.Term.Parser



runFile f = do
    msg $ "READ " ++ f
    toks <- scanFile
      []
      ["==", "\\", "=>", "<=>", ".", "+", "*", "-", "::", "@", "|", "\\/", "?"]
      "(),"
      "=/\\><.+*-@:|?"
      f
    (prog, query) <- parseIOMessage show pProg toks
    putPPLn $ "Rules" >-< indent 2 (vlist $ map pp prog)
    putPPLn $ "Query" >-< indent 2 (vlist $ map pp query)
    msg $ "SOLVE " ++ f
    let mbp :: MBP.CHRMonoBacktrackPrioT C G B P S E IO (MBP.SolverResult S)
        mbp = do
          mapM_ MBP.addRule prog
          mapM_ MBP.addConstraintAsWork query
          r <- MBP.chrSolve ()
          MBP.ppSolverResult r >>= (liftIO . putPPLn)
          return r
    MBP.runCHRMonoBacktrackPrioT (MBP.emptyCHRGlobState) (MBP.emptyCHRBackState) mbp
    msg $ "DONE " ++ f
  where
    msg m = putStrLn $ "---------------- " ++ m ++ " ----------------"

mainTerm = do
  forM_
      [ "unify"
      -- , "antisym"
      ] $ \f -> do
    let f' = "test/" ++ f ++ ".chr"
    runFile f'
  

{-
-}
