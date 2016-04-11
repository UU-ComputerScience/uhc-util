{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

module UHC.Util.CHR.Rule.Parser
  ( CHRParsable(..)
  
  , Pr
  
  , pProg
  )
  where

import           UU.Parsing
import           UU.Scanner.TokenParser
import           UU.Scanner.Token

import           UHC.Util.ParseUtils
import           UHC.Util.ScanUtils

import           UHC.Util.CHR.Rule

-------------------------------------------------------------------------------------------
--- API of parser for constraints etc
-------------------------------------------------------------------------------------------

-- | API of parser for constraints etc, to be used by rule parser
class CHRParsable cnstr guard bprio rprio rule | cnstr -> rule, guard -> rule, bprio -> rule, rprio -> rule, rule -> cnstr guard bprio rprio where
  pChrConstraint            :: Pr cnstr
  pChrBuiltinConstraint     :: Pr cnstr
  pChrGuard                 :: Pr guard
  pChrBacktrackPrioVar      :: Pr bprio
  pChrBacktrackPrio         :: Pr bprio
  pChrRulePrio              :: Pr rprio
 
{-
-}
  scanChrExtraKeywordsTxt   :: rule -> [String]
  scanChrExtraKeywordsOps   :: rule -> [String]
  scanChrExtraSpecialChars  :: rule ->  String 
  scanChrExtraOpChars       :: rule ->  String 
 
  -- defaults
  scanChrExtraKeywordsTxt   _ = []
  scanChrExtraKeywordsOps   _ = []
  scanChrExtraSpecialChars  _ = ""
  scanChrExtraOpChars       _ = ""

-------------------------------------------------------------------------------------------
--- Program is set of rules + optional queries
-------------------------------------------------------------------------------------------

type Pr p = PlainParser Token p

-- | CHR Program = rules + optional queries
pProg :: forall c g bp rp . CHRParsable c g bp rp (Rule c g bp rp) => Pr ([Rule c g bp rp], [c])
pProg =
    pRules <+> pQuery
  where
    pR :: Pr (Rule c g bp rp)
    pR = pPre <**>
           ( pHead <**>
               (   (   (\(g,b) h pre -> pre $ g $ mkR h (length h) b) <$ pKey "<=>"
                   <|> (\(g,b) h pre -> pre $ g $ mkR h 0          b) <$ (pKey "=>" <|> pKey "==>")
                   ) <*> pBody
               <|> (   (\hr (g,b) hk pre -> pre $ mkR (hr ++ hk) (length hr) b)
                       <$ pKey "\\" <*> pHead <* pKey "<=>" <*> pBody
                   )
               )
           )
       where pPre = (\(bp,rp) lbl -> lbl . bp . rp) 
                    <$> (pParens ((,) <$> (flip (=!) <$> pChrBacktrackPrioVar <|> pSucceed id)
                                      <*  pComma
                                      <*> (flip (=!!) <$> pChrRulePrio <|> pSucceed id)
                                 ) <* pKey "::" <|> pSucceed (id,id)
                        )
                    <*> ((@=) <$> pVarid <* pKey "@" <|> pSucceed id)
             pHead = pList1Sep pComma pChrConstraint
             pGrd = flip (=|) <$> pList1Sep_ng pComma pChrGuard <* pKey "|" <|> pSucceed id
             pBody = pGrd <+> pBodyAlts
             pBodyAlts = pListSep (pKey "\\/") pBodyAlt
             pBodyAlt
               = (\pre (c,b) -> pre $ (c ++ b) /\ [])
                 <$> (flip (\!) <$> pChrBacktrackPrio <* pKey "::" <|> pSucceed id)
                 <*> (foldr ($) ([],[]) <$> pList1Sep pComma ((\c (cs,bs) -> (c:cs,bs)) <$> pChrConstraint <|> (\b (cs,bs) -> (cs,b:bs)) <$> pChrBuiltinConstraint))
             mkR h len b = Rule h len [] b Nothing Nothing Nothing

    pRules :: Pr [Rule c g bp rp]
    pRules = pList (pR <* pKey ".")

    pQuery :: Pr [c]
    pQuery = concat <$> pList (pKey "?" *> pList1Sep pComma pChrConstraint <* pKey ".")

