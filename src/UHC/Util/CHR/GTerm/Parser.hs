{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

module UHC.Util.CHR.GTerm.Parser
  ( {- CHRParsable(..)
  
  , Pr
  
  , -}
    parseFile
  )
  where

import qualified Data.Set as Set

import           Control.Monad

import           UU.Parsing
import           UU.Scanner
import           UU.Scanner.TokenParser
import           UU.Scanner.Token

import           UHC.Util.ParseUtils
import           UHC.Util.ScanUtils
import           UHC.Util.Pretty

import           UHC.Util.CHR.Rule
import           UHC.Util.CHR.GTerm.AST

-------------------------------------------------------------------------------------------
--- Scanning options for CHR parsing
-------------------------------------------------------------------------------------------

-- | Scanning options for rule parser
scanOpts :: ScanOpts
scanOpts
  =  defaultScanOpts
        {   scoKeywordsTxt      =   Set.fromList []
        ,   scoKeywordsOps      =   Set.fromList ["\\", "=>", "==>", "<=>", ".", "::", "@", "|", "\\/", "?"]
        ,   scoOpChars          =   Set.fromList "!#$%&*+/<=>?@\\^|-:.~"
        ,   scoSpecChars        =   Set.fromList "(),`"
        }

-------------------------------------------------------------------------------------------
--- Parse interface
-------------------------------------------------------------------------------------------

-- | Parse a file as a CHR spec + queries
parseFile :: forall c g bp rp tm . GTermAs c g bp rp tm => FilePath -> IO (Either PP_Doc ([Rule c g bp rp], [c]))
parseFile f = do
    toks <- scanFile
      (Set.toList $ scoKeywordsTxt scanOpts)
      (Set.toList $ scoKeywordsOps scanOpts)
      (Set.toList $ scoSpecChars scanOpts)
      (Set.toList $ scoOpChars scanOpts)
      f
    (prog, query) <- parseIOMessage show pProg toks
    return $ do
      prog <- forM prog $ \r@(Rule {ruleHead=hcs, ruleGuard=gs, ruleBodyAlts=as, ruleBacktrackPrio=mbp, rulePrio=mrp}) -> do
        hcs <- forM hcs asHeadConstraint
        gs  <- forM gs  asGuard
        mbp <- maybe (return Nothing) (fmap Just . asHeadBacktrackPrio) mbp
        mrp <- maybe (return Nothing) (fmap Just . asRulePrio) mrp
        as  <- forM as $ \a@(RuleBodyAlt {rbodyaltBacktrackPrio=mbp, rbodyaltBody=bs}) -> do
          bs  <- forM bs asBodyConstraint
          mbp <- maybe (return Nothing) (fmap Just . asAltBacktrackPrio) mbp
          return $ a {rbodyaltBacktrackPrio=mbp, rbodyaltBody=bs}
        return $ r {ruleHead=hcs, ruleGuard=gs, ruleBodyAlts=as, ruleBacktrackPrio=mbp, rulePrio=mrp}
      query <- forM query asHeadConstraint
      return (prog,query)

-------------------------------------------------------------------------------------------
--- Program is set of rules + optional queries
-------------------------------------------------------------------------------------------

type Pr p = PlainParser Token p

-- | CHR Program = rules + optional queries
pProg :: Pr ([Rule GTm GTm GTm GTm], [GTm])
pProg =
    pRules <+> pQuery
  where
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
                    <$> (pParens ((,) <$> (flip (=!) <$> pTm_Var <|> pSucceed id)
                                      <*  pComma
                                      <*> (flip (=!!) <$> pTm <|> pSucceed id)
                                 ) <* pKey "::" <|> pSucceed (id,id)
                        )
                    <*> ((@=) <$> (pConid <|> pVarid) <* pKey "@" <|> pSucceed id)
             pHead = pList1Sep pComma pTm_Op
             pGrd = flip (=|) <$> pList1Sep_ng pComma pTm_Op <* pKey "|" <|> pSucceed id
             pBody = pGrd <+> pBodyAlts
             pBodyAlts = pListSep (pKey "\\/") pBodyAlt
             pBodyAlt
               = (\pre (c,b) -> pre $ (c ++ b) /\ [])
                 <$> (flip (\!) <$> pTm <* pKey "::" <|> pSucceed id)
                 <*> (foldr ($) ([],[]) <$> pList1Sep pComma ((\c (cs,bs) -> (c:cs,bs)) <$> pTm_Op <|> (\b (cs,bs) -> (cs,b:bs)) <$> pTm_Op))
             mkR h len b = Rule h len [] b Nothing Nothing Nothing

    pRules = pList (pR <* pKey ".")

    pQuery = concat <$> pList (pKey "?" *> pList1Sep pComma pTm_Op <* pKey ".")
    
    pTm
      = pTm_Op

    pTm_Op
      = pTm_App <**>
          (   (\o r l -> GTm_Con o [l,r]) <$> pOp <*> pTm_App
          <|> pSucceed id
          )
      where pOp = pVarsym <|> pKey "`" *> pConid <* pKey "`"

    pTm_App
      =   GTm_Con <$> pConid <*> pList pTm_Base
      <|> (\o l r -> GTm_Con o [l,r]) <$> pParens pVarsym <*> pTm_Base <*> pTm_Base
      <|> pTm_Base

    pTm_Base
      =   pTm_Var
      <|> (GTm_Int . read) <$> pInteger
      <|> GTm_Str <$> pString
      <|> pParens pTm

    pTm_Var
      = GTm_Var <$> pVarid


