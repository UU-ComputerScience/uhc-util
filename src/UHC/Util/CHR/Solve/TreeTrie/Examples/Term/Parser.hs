{-# LANGUAGE RankNTypes #-}

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
  pChrConstraint              =   C_Con <$> pConid <*> pList (pTm' (\_ p -> p))
  pChrBuiltinConstraint       =   pTm <**>
                                    ((flip CB_Eq <$ pKey "==" <|> flip CB_Ne <$ pKey "/=")
                                      <*> pTm
                                    )
                              <|> CB_Fail <$ pKey "fail"
  pChrGuard                   =   pTm <**>
                                    ((flip G_Eq <$ pKey "==" <|> flip G_Ne <$ pKey "/=")
                                      <*> pTm
                                    )
  pChrBacktrackPrioVar        =   P_Tm <$> pTm_Var
  pChrBacktrackPrio           =   pP
  pChrRulePrio                =   pP
  
  scanChrExtraKeywordsTxt   _ = ["fail", "abs", "mod"]
  scanChrExtraKeywordsOps   _ = ["==", "/=", "+", "*", "-", "<", "<="]
  scanChrExtraSpecialChars  _ =  ""
  scanChrExtraOpChars       _ =  ""

pTm_Var :: Pr Tm
pTm_Var = Tm_Var <$> pVarid

pTm_Base' :: Pr Tm -> Pr Tm
pTm_Base' pT =   pB
    where pB :: Pr Tm
          pB =   (Tm_Int . read) <$> pInteger
             <|> pTm_Var
             <|> flip Tm_Con [] <$> pConid
             <|> pParens pT

pTm' :: (Pr Tm -> Pr Tm -> Pr Tm) -> Pr Tm
pTm' addTmP =   pB
    where pB :: Pr Tm
          pB  =   pTm_Base' pT
          pT :: Pr Tm
          pT  =   addTmP pB $ Tm_Con <$> pConid <*> pList1_ng pB

pTm :: Pr Tm
pTm = pTm' addp
    where addp :: Pr Tm -> Pr Tm -> Pr Tm
          addp pB p =
                  p
              <|> Tm_Op  <$> (PUOp_Abs <$ pKey "abs") <*> ((:[]) <$> pB)
              <|> Tm_Op  <$> (PBOp_Mod <$ pKey "mod") <*> ((\x y -> [x,y]) <$> pB <*> pB)
              <|> pBOp (\o x y -> Tm_Op o [x,y]) pB

pBOp :: (POp -> x -> x -> x) -> Pr x -> Pr x
pBOp mkO pB
  = pChainr_ng (mkO <$> (PBOp_Lt  <$ pKey "<" <|> PBOp_Le  <$ pKey "<="))
  $ pChainr_ng (mkO <$> (PBOp_Add <$ pKey "+" <|> PBOp_Sub <$ pKey "-" ))
  $ pChainr_ng (mkO <$> (PBOp_Mul <$ pKey "*"))
  $ pB

pP :: Pr P
pP = pP
   where pB :: Pr P
         pB = P_Tm <$> pTm' (\_ p -> p) <|> pParens pP
         pP :: Pr P
         pP = pBOp P_Op pB
{-
         
         pChainr (P_Op <$> (PBOp_Add <$ pKey "+" <|> PBOp_Sub <$ pKey "-"))
              $ pChainr (P_Op <$> (PBOp_Mul <$ pKey "*"))
              $ pB
-}
