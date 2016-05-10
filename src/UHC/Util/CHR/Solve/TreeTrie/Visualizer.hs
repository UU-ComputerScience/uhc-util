{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}

module UHC.Util.CHR.Solve.TreeTrie.Visualizer
  ( chrVisualize
  )
  where

import           Prelude
import           Data.List
import           UHC.Util.Pretty
import           UHC.Util.PrettySimple
import           UHC.Util.CHR.Rule
import           UHC.Util.CHR.GTerm.Parser
import           UHC.Util.CHR.Solve.TreeTrie.Mono
import           UHC.Util.CHR.Solve.TreeTrie.MonoBacktrackPrio as MBP
import           UHC.Util.CHR.Solve.TreeTrie.Examples.Term.AST
import           UHC.Util.CHR.Solve.TreeTrie.Internal
import           UHC.Util.CHR.Solve.TreeTrie.Internal.Shared

data Node =
  Node
    { nodeName        :: String
    , nodeVars        :: [Var]
    , nodeHeadVars    :: [Var]
    , nodeGuardVars   :: [Var]
    , nodeBodyAltVars :: [Var]
    }

stepToNode :: SolveStep' C (MBP.StoredCHR C G P P) S -> Node
stepToNode step
  = Node
    { nodeName = maybe "[untitled]" id (ruleName rule)
    , nodeVars = vars
    , nodeHeadVars = headVars
    , nodeGuardVars = guardVars
    , nodeBodyAltVars = bodyAltVars
    }
  where
    schr = stepChr step
    rule = MBP.storedChrRule' schr
    vars = nub $ headVars ++ guardVars ++ bodyAltVars
    headVars = nub $ concatMap variablesInConstraint (ruleHead rule)
    guardVars = nub $ concatMap variablesInGuard (ruleGuard rule)
    bodyAltVars = nub $ concatMap variablesInRuleBodyAlt (ruleBodyAlts rule)

variablesInTerm :: Tm -> [Var]
variablesInTerm (Tm_Var var)    = [var]
variablesInTerm (Tm_Con _ tms)  = variablesInTerms tms
variablesInTerm (Tm_Lst tms tm) = variablesInTerms tms ++ maybe [] variablesInTerm tm
variablesInTerm (Tm_Op _ tms)   = variablesInTerms tms
variablesInTerm _               = []

variablesInTerms :: [Tm] -> [Var]
variablesInTerms = concatMap variablesInTerm

variablesInConstraint :: C -> [Var]
variablesInConstraint (C_Con _ tms) = variablesInTerms tms
variablesInConstraint (CB_Eq x y)   = variablesInTerm x ++ variablesInTerm y
variablesInConstraint (CB_Ne x y)   = variablesInTerm x ++ variablesInTerm y
variablesInConstraint CB_Fail       = []

variablesInGuard :: G -> [Var]
variablesInGuard (G_Eq x y) = variablesInTerm x ++ variablesInTerm y
variablesInGuard (G_Ne x y) = variablesInTerm x ++ variablesInTerm y
variablesInGuard (G_Tm x)   = variablesInTerm x

variablesInRuleBodyAlt :: RuleBodyAlt C bprio -> [Var]
variablesInRuleBodyAlt = (concatMap variablesInConstraint) . rbodyaltBody

first :: [a] -> Maybe a
first (x:_) = Just x
first _     = Nothing

tag :: String -> PP_Doc -> PP_Doc -> PP_Doc
-- tag name Emp  = (text ("<" ++ name)                 >|<) . end
-- tag name attr = (text ("<" ++ name ++ " ") >|< attr >|<) . end
tag name attr content = (text ("<" ++ name)) >|< attributes attr >|< body content
  where
    attributes Emp = Emp
    attributes a   = text " " >|< a
    body Emp       = text " />"
    body content   = text ">" >|< content >|< text ("</" ++ name ++ ">")

tag' :: String -> PP_Doc -> PP_Doc
tag' name = tag name Emp

showNode :: Node -> PP_Doc
showNode node = tag "div" (text "class=\"" >|< className >|< text "\"") (
    hlist (map (showUsage "usage constraint") (nodeHeadVars node))
    >|< hlist (map (showUsage "usage guard") (nodeGuardVars node))
    >|< tag "div" (text "class=\"rule-text\"") (
      (text $ nodeName node)
      >|< (hlist (map ((" " >|<) . pp) (nodeVars node)))
    )
  )
  where
    className = text "rule" >|< maybe Emp ((text " var-" >|<)) (first $ nodeVars node)
    showUsage name var = tag "div" (text $ "class=\"" ++ className ++ "\"") (text " ")
      where
        className = name ++ " var-" ++ var

chrVisualize :: SolveTrace' C (MBP.StoredCHR C G P P) S -> PP_Doc
chrVisualize trace = tag' "html" $
  tag' "head" (
    tag' "title" (text "CHR visualization")
    >|< tag' "style" (text styles)
  )
  >|< tag' "body" (
    hlist (map showNode nodes)
  )
  where
    nodes = map stepToNode trace

styles :: String
styles = "body {\n\
        \  font-size: 9pt;\n\
        \  font-family: Arial;\n\
        \}\n\
        \.usage {\n\
        \  background-color: #ccc;\n\
        \  width: 8px;\n\
        \  height: 8px;\n\
        \  border-radius: 4px;\n\
        \}\n\
        \.rule {\n\
        \  border: 1px solid #333;\n\
        \}\n\
        \"
