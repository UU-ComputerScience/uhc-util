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

tag :: String -> PP_Doc -> PP_Doc -> PP_Doc
tag name attr content = (text ("<" ++ name)) >|< attributes attr >|< body content
  where
    attributes Emp = Emp
    attributes a   = text " " >|< a
    body Emp       = text " />"
    body content   = text ">" >|< content >|< text ("</" ++ name ++ ">")

tag' :: String -> PP_Doc -> PP_Doc
tag' name = tag name Emp

firstVar :: [Var] -> [Var] -> Maybe Var
firstVar []     _    = Nothing
firstVar _      []   = Nothing
firstVar (x:xs) vars = if x `elem` vars then Just x else firstVar xs vars

showNode :: [Var] -> Node -> PP_Doc
showNode order node = tag "div" (text "class=\"rule\"") (
    hlist (map (showUsage "usage guard") (nodeGuardVars node))
    >|< hlist (map (showUsage "usage constraint") (nodeHeadVars node))
    >|< tag "div" (text "class=\"" >|< className >|< text "\"") (
      (text $ nodeName node)
      >|< (hlist (map ((" " >|<) . pp) (nodeVars node)))
    )
    >|< hlist (map (showUsage "usage body-alt") (nodeBodyAltVars node))
  )
  where
    className = text "rule-text" >|< maybe Emp ((text " var-" >|<)) (firstVar order $ nodeVars node)
    showUsage name var = tag "div" (text $ "class=\"" ++ className ++ "\"") (text " ")
      where
        className = name ++ " var-" ++ var

chrVisualize :: SolveTrace' C (MBP.StoredCHR C G P P) S -> PP_Doc
chrVisualize trace = tag' "html" $
  tag' "head" (
    tag' "title" (text "CHR visualization")
    >|< tag' "style" (styles order)
  )
  >|< tag' "body" (
    hlist (map (showNode order) nodes)
  )
  where
    nodes = map stepToNode trace
    vars = nub (concatMap nodeVars nodes)
    order = vars -- TODO: Sort vars to minimize crossings

styles :: [Var] -> PP_Doc
styles vars =
  text "body {\n\
       \  font-size: 9pt;\n\
       \  font-family: Arial;\n\
       \}\n\
       \.rule {\n\
       \  position: relative;\n\
       \}\n\
       \.usage {\n\
       \  border: 1px solid #ccc;\n\
       \  background-color: #eee;\n\
       \  width: 12px;\n\
       \  height: 12px;\n\
       \  border-radius: 8px;\n\
       \  position: absolute;\n\
       \  top: 0px;\n\
       \}\n\
       \.usage.constraint {\n\
       \  background-color: #6EAFC4;\n\
       \  border: 1px solid #578999;\n\
       \  top: 11px;\n\
       \}\n\
       \.usage.body-alt {\n\
       \  background-color: #D1BE4F;\n\
       \  border: 1px solid #A89942;\n\
       \  top: 38px;\n\
       \}\n\
       \.rule-text {\n\
       \  border: 1px solid #aaa;\n\
       \  background-color: #fff;\n\
       \  display: inline-block;\n\
       \  padding: 2px;\n\
       \  margin: 21px 0 12px;\n\
       \}\n\
       \"
  >|< hlist (map styleVar varIndices)
  where
    varIndices :: [(Var, Int)]
    varIndices = zip vars [0..]
    styleVar (var, id) =
      text ".var-"
      >|< text var
      >|< text "{\n"
      >|< text "  margin-left: "
      >|< pp (id * 20)
      >|< text "px;\n}\n"
