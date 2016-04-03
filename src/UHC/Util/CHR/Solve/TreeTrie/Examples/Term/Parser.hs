module UHC.Util.CHR.Solve.TreeTrie.Examples.Term.Parser
  ( pProg
  )
  where

import           UU.Parsing
import           UU.Scanner.TokenParser
import           UU.Scanner.Token

import           UHC.Util.ParseUtils
import           UHC.Util.ScanUtils

import           UHC.Util.CHR.Solve.TreeTrie.Examples.Term.AST
import           UHC.Util.CHR.Rule
import           UHC.Util.CHR.Rule.Parser

instance CHRParsable C G P P (Rule C G P P) where
  pChrConstraint              =   C_Con <$> pConid <*> pList pTm
  pChrBuiltinConstraint       =   CB_Eq <$> pTm <* pKey "==" <*> pTm
                              <|> CB_Fail <$ pKey "fail"
  pChrGuard                   =   G_Eq <$> pTm <* pKey "==" <*> pTm
  pChrBacktrackPrioVar        =   P_Tm <$> pTm_Var
  pChrBacktrackPrio           =   pP
  pChrRulePrio                =   pP
  
  scanChrExtraKeywordsTxt   _ = ["fail"]
  scanChrExtraKeywordsOps   _ = ["=="]
  scanChrExtraSpecialChars  _ =  ""
  scanChrExtraOpChars       _ =  ""

pTm_Var :: Pr Tm
pTm_Var = Tm_Var <$> pVarid

pTm :: Pr Tm
pTm =   pB
    where pB =   (Tm_Int . read) <$> pInteger
             <|> pTm_Var
             <|> pParens pT
          pT = Tm_Con <$> pConid <*> pList pB

pP :: Pr P
pP = pP
   where pB = P_Tm <$> pTm <|> pParens pP
         pP =   pChainr (P_Op <$> (POp_Add <$ pKey "+" <|> POp_Sub <$ pKey "-"))
              $ pChainr (P_Op <$> (POp_Mul <$ pKey "*"))
              $ pB
