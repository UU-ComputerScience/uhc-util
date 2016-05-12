{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}

module UHC.Util.CHR.Solve.TreeTrie.Visualizer
  ( chrVisualize
  )
  where

import           Prelude
import           Data.List as List
import           Data.Map as Map
import           UHC.Util.Pretty
import           UHC.Util.PrettySimple
import           UHC.Util.CHR.Rule
import           UHC.Util.CHR.GTerm.Parser
import           UHC.Util.CHR.Solve.TreeTrie.Mono
import           UHC.Util.CHR.Solve.TreeTrie.MonoBacktrackPrio as MBP
import           UHC.Util.CHR.Solve.TreeTrie.Examples.Term.AST
import           UHC.Util.CHR.Solve.TreeTrie.Internal
import           UHC.Util.CHR.Solve.TreeTrie.Internal.Shared
import           Data.Graph.Inductive.Graph

data NodeData =
  NodeData
    { nodeName        :: String
    , nodeBody        :: [RuleBodyAlt C P]
    }

stateMap :: (a -> b -> (c, b)) -> b -> [a] -> ([c], b)
stateMap _  state []     = ([], state)
stateMap cb state (x:xs) = (y:ys, newState)
  where
    (ys,tmpState) = stateMap cb state xs
    (y,newState)  = cb x tmpState

data BuildState = BuildState [Edge] (Map.Map Tm Node) Int

emptyBuildState :: BuildState
emptyBuildState = BuildState [] Map.empty 0

tmInC :: C -> [Tm]
tmInC (C_Con s tms) = [Tm_Con s tms]
tmInC _             = []

tmsInG :: G -> [Tm]
tmsInG (G_Tm tm) = tmsInTm tm
tmsInG _         = []

precedentTms :: Rule C G P P -> [Tm]
precedentTms rule
  =  concatMap tmInC  (ruleHead rule)
  ++ concatMap tmsInG (ruleGuard rule)

tmsInBodyAlt :: RuleBodyAlt C bprio -> [Tm]
tmsInBodyAlt = concatMap tmInC . rbodyaltBody

tmsInTm :: Tm -> [Tm]
tmsInTm tm = tm : children tm
  where
    children (Tm_Lst as Nothing)  = as
    children (Tm_Lst as (Just a)) = as ++ [a]
    children _                    = [] 

addConstraints :: Node -> (Map.Map Tm Node) -> [Tm] -> (Map.Map Tm Node)
addConstraints node = List.foldl cb
  where
    cb m tm = Map.insert tm node m

stepToNode :: SolveStep' C (MBP.StoredCHR C G P P) S -> BuildState -> ((LNode NodeData), BuildState)
stepToNode step (BuildState edges nodeMap no)
  = ((no, NodeData
        { nodeName = maybe "[untitled]" id (ruleName rule)
        , nodeBody = ruleBodyAlts rule
        })
    , BuildState edges nodeMap (no + 1)
    )
  where
    schr = stepChr step
    rule = MBP.storedChrRule' schr

createGraph :: [SolveStep' C (MBP.StoredCHR C G P P) S] -> ([LNode NodeData], [Edge])
createGraph steps = (nodes, edges)
  where
    (nodes, (BuildState edges _ _)) = stateMap stepToNode emptyBuildState steps

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

addIndices :: [a] -> [(a, Int)]
addIndices as = zip as [0..]

{- showNode :: [Var] -> Node -> PP_Doc
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
        className = name ++ " var-" ++ var -}

chrVisualize :: SolveTrace' C (MBP.StoredCHR C G P P) S -> PP_Doc
chrVisualize trace = tag' "html" $
  tag' "head" (
    tag' "title" (text "CHR visualization")
    -- >|< tag "script" (text "type=\"text/javascript\"") (text scripts)
    -- >|< tag' "style" (styles order)
  )
  >|< tag' "body" (
    Emp
    -- hlist (map showVarHeader vars)
    -- >|< tag "div" (text "class=\"content\"") (hlistReverse (map (showNode order) nodes))
  )
  where
    -- nodes = map stepToNode trace
    -- vars = nub (concatMap nodeVars nodes)
    -- order = vars -- TODO: Sort vars to minimize crossings
    -- showVarHeader var =
    --  tag "a" (text $ "href=\"javascript:selectVar('" ++ var ++ "');\" class=\"varheader var-" ++ var ++ "\"") (text var)

scripts :: String
scripts =
  "(function(){\n\
  \  var selected = [];\n\
  \  function setClass() {\n\
  \    var name = selected.length\n\
  \      ? 'selected-var ' + selected.map(function(item) {\n\
  \          return 'selected-var-' + item;\n\
  \        }).join(' ')\n\
  \      : '';\n\
  \    document.body.className = name;\n\
  \  }\n\
  \  function select(name) {\n\
  \    var index = selected.indexOf(name);\n\
  \    if (index === -1) selected.push(name);\n\
  \    else selected.splice(index, 1);\n\
  \    setClass();\n\
  \  }\n\
  \  window.selectVar = select;\n\
  \}());\n\
  \"

styles :: [Var] -> PP_Doc
styles vars =
  text "body {\n\
       \  font-size: 9pt;\n\
       \  font-family: Arial;\n\
       \}\n\
       \.varheader {\n\
       \  width: 19px;\n\
       \  font-weight: 700;\n\
       \  position: absolute;\n\
       \  top: 5px;\n\
       \}\n\
       \.content {\n\
       \  margin-top: 25px;\n\
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
       \.selected-var .usage, .selected-var .varheader {\n\
       \  opacity: 0.4;\n\
       \}\n\
       \"
  >|< hlist (fmap styleVar varIndices)
  where
    varIndices = addIndices vars
    styleVar (var, id) =
      text ".var-"
      >|< text var
      >|< text "{\n"
      >|< text "  margin-left: "
      >|< pp (id * 20)
      >|< text "px;\n}\n"
      >|< text ".selected-var-"
      >|< text var
      >|< text " .usage.var-"
      >|< text var
      >|< text ", .selected-var-"
      >|< text var
      >|< text " .varheader.var-"
      >|< text var
      >|< text "{\n  opacity: 1;\n}\n"
