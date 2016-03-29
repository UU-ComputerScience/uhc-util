{-# LANGUAGE RankNTypes #-}

module UHC.Util.CHR.Solve.TreeTrie.Examples.Term.Parser
  ( pRules
  )
  where

import           UU.Parsing
import           UU.Scanner.TokenParser
import           UU.Scanner.Token

import           UHC.Util.ParseUtils
import           UHC.Util.ScanUtils

import           UHC.Util.CHR.Solve.TreeTrie.Examples.Term.AST
import           UHC.Util.CHR.Rule

type Pr p = PlainParser Token p

pTm_Var :: Pr Tm
pTm_Var = Tm_Var <$> pVarid

pTm :: Pr Tm
pTm =   (Tm_Int . read) <$> pInteger
    <|> pTm_Var
    <|> Tm_Con <$> pConid <*> pParens (pList pTm)

pB :: Pr B
pB = B_Eq <$> pTm <* pKey "==" <*> pTm

pG :: Pr G
pG = G_Eq <$> pTm <* pKey "==" <*> pTm

pC :: Pr C
pC = C_Con <$> pConid <*> pParens (pList1Sep pComma pTm)

pP_Var :: Pr P
pP_Var = P_Tm <$> pTm_Var

pP :: Pr P
pP = pP 
   where pB = P_Tm <$> pTm <|> pParens pP
         pP =   pChainr (P_Op <$> (POp_Add <$ pKey "+" <|> POp_Sub <$ pKey "-"))
              $ pChainr (P_Op <$> (POp_Mul <$ pKey "*"))
              $ pB

pR :: Pr (Rule C G B P)
pR = pPre <**>
       ( pHead <**>
           (   (   (\(g,b) h pre -> pre $ g $ mkR h (length h) b) <$ pKey "<=>"
               <|> (\(g,b) h pre -> pre $ g $ mkR h 0          b) <$ pKey "=>"
               ) <*> pBody
           <|> (   (\hr (g,b) hk pre -> pre $ mkR (hr ++ hk) (length hr) b)
                   <$ pKey "\\" <*> pHead <* pKey "<=>" <*> pBody
               )
           )
       )
   where pPre = (\(bp,rp) lbl -> lbl . bp . rp) 
                <$> (pParens ((,) <$> (flip (=!) <$> pP_Var <|> pSucceed id)
                                  <*  pComma
                                  <*> (flip (=!!) <$> pP <|> pSucceed id)
                             ) <* pKey "::" <|> pSucceed (id,id)
                    )
                <*> ((@=) <$> pVarid <* pKey "@" <|> pSucceed id)
         pHead = pList1Sep pComma pC
         pGrd = flip (=|) <$> pList1Sep_ng pComma pG <* pKey "|" <|> pSucceed id
         pBody = pGrd <+> pBodyAlts
         pBodyAlts = pListSep (pKey "\\/") pBodyAlt
         pBodyAlt
           = (\pre (c,b) -> pre $ c /\ b)
             <$> (flip (\!) <$> pP <* pKey "::" <|> pSucceed id)
             <*> (foldr ($) ([],[]) <$> pList1Sep pComma ((\c (cs,bs) -> (c:cs,bs)) <$> pC <|> (\b (cs,bs) -> (cs,b:bs)) <$> pB))
         mkR h len b = Rule h len [] b Nothing Nothing Nothing

pRules :: Pr [Rule C G B P]
pRules = pList (pR <* pKey ".")

{-
data Rule cnstr guard builtin prio
  = Rule
      { ruleHead            :: ![cnstr]
      , ruleSimpSz          :: !Int                -- ^ length of the part of the head which is the simplification part
      , ruleGuard           :: ![guard]    
      , ruleBodyAlts        :: ![RuleBodyAlt cnstr builtin prio]
      , ruleBacktrackPrio   :: !(Maybe prio)       -- ^ backtrack priority, should be something which can be substituted with the actual prio, later to be referred to at backtrack prios of alternatives
      , rulePrio            :: !(Maybe prio)       -- ^ rule priority, to choose between rules with equal backtrack priority
      , ruleName            :: (Maybe String)
-}
