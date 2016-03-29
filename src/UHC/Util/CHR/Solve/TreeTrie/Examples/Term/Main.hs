module UHC.Util.CHR.Solve.TreeTrie.Examples.Term.Main where

import           UHC.Util.CHR.Solve.TreeTrie.Examples.Term.Parser

-- import UHC.Util.ScanUtils
import           UU.Parsing
import           UU.Scanner

import           UHC.Util.Pretty

import           System.IO
import           Control.Monad


runFile f = do
  toks <- scanFile
    []
    ["==", "\\", "=>", "<=>", ".", "+", "*", "-", "::", "@", "|", "\\/"]
    "(),"
    "=/\\><.+*-@:|"
    f
  res <- parseIOMessage show pRules toks
  putPPLn $ vlist $ map pp res

mainTerm = do
  forM_ ["antisym"] $ \f -> do
    runFile $ "test/" ++ f ++ ".chr"
  

{-
scanFile :: [String] -> [String] -> String -> String -> FilePath -> IO [Token]
scanFile keywordstxt keywordsops specchars opchars fn =
        do txt <- readFile fn
           return (scan keywordstxt keywordsops specchars opchars (initPos fn) txt)
-}
