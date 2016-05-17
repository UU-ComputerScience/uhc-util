{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}

module UHC.Util.CHR.Solve.TreeTrie.Visualizer
  ( chrVisualize
  )
  where

import           Prelude
import           Data.Maybe as Maybe
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
import           UHC.Util.Substitutable
import           Data.Graph.Inductive.Graph
import           Data.Graph.Inductive.Tree

data NodeData =
  NodeData
    { nodeName        :: String
    , nodeVars        :: [Tm]
    , nodeAlt         :: [C]
    }
type Node' = LNode NodeData

stateMap :: (a -> b -> (c, b)) -> b -> [a] -> ([c], b)
stateMap _  state []     = ([], state)
stateMap cb state (x:xs) = (y:ys, newState)
  where
    (ys,tmpState) = stateMap cb state xs
    (y,newState)  = cb x tmpState

data BuildState = BuildState [Edge] (Map.Map Tm Node) Int

emptyBuildState :: BuildState
emptyBuildState = BuildState [] Map.empty 0

tmsInC :: C -> [Tm]
tmsInC (C_Con s tms) = [Tm_Con s tms]
tmsInC _             = []

tmsInG :: G -> [Tm]
tmsInG (G_Tm tm) = tmsInTm tm
tmsInG _         = []

precedentTms :: Rule C G P P -> [Tm]
precedentTms rule
  =  concatMap tmsInC  (ruleHead rule)
  ++ concatMap tmsInG (ruleGuard rule)

tmsInBodyAlt :: RuleBodyAlt C bprio -> [Tm]
tmsInBodyAlt = concatMap tmsInC . rbodyaltBody

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

stepToNode :: SolveStep' C (MBP.StoredCHR C G P P) S -> BuildState -> ((Node'), BuildState)
stepToNode step (BuildState edges nodeMap nodeId)
  = ( (nodeId
      , NodeData
        { nodeName = maybe "[untitled]" id (ruleName rule)
        , nodeVars = Map.elems (stepSubst step)
        , nodeAlt  = alt
        }
      )
    , BuildState edges' nodeMap' (nodeId + 1)
    )
  where
    schr = stepChr step
    rule = MBP.storedChrRule' schr
    updRule = varUpd (stepSubst step) rule
    alt = maybe [] (fmap $ varUpd $ stepSubst step) $ stepAlt step
    altTms = concatMap tmsInC alt
    nodeMap' = addConstraints nodeId nodeMap altTms
    edges' =
      ( List.map (\n -> (n, nodeId))
        $ Maybe.mapMaybe (\tm -> Map.lookup tm nodeMap) (precedentTms updRule)
      )
      ++ edges

createGraph :: [SolveStep' C (MBP.StoredCHR C G P P) S] -> Gr NodeData ()
createGraph steps = mkGraph nodes (fmap ((flip toLEdge) ()) edges)
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

showNode :: (Node -> (Int, Int)) -> Node' -> PP_Doc
showNode pos (node, nodeData) = tag "div"
  (
    text "class=\"rule\" style=\"top: "
    >|< pp y 
    >|< text "px; left: "
    >|< pp x
    >|< text "px;\""
  )
  (
    tag "span" (text "class=\"" >|< className >|< text "\"") (
      (text $ nodeName nodeData)
      >|< (hlist (fmap ((" " >|<) . pp) (nodeVars nodeData)))
    )
    >|< tag' "br" Emp
    >|< text "&#8627;"
    >|< tag "span" (text "class=\"rule-alt\"") altText
  )
  where
    (x, y) = pos node
    alt = nodeAlt nodeData
    altText = case alt of
      []   -> text "."
      x:xs -> showAlt x >|< (hlist . fmap ((text ", " >|<) . pp)) xs
    showAlt = tag' "div" . pp 
    className = text "rule-text"
    showUsage name var = tag "div" (text $ "class=\"" ++ className ++ "\"") (text " ")
      where
        className = name ++ " var-" ++ var

showEdge :: (Node -> (Int, Int)) -> Edge -> PP_Doc
showEdge pos (from, to) =
  tag "div"
    (
      text "class=\"edge-ver\" style=\"top: "
      >|< pp y1
      >|< "px; left: "
      >|< pp x1
      >|< "px; height: "
      >|< (y2 - y1)
      >|< "px;\""
    )
    (text " ")
  >|< tag "div"
    (
      text "class=\"edge-hor\" style=\"top: "
      >|< pp y2
      >|< "px; left: "
      >|< pp x1
      >|< "px; width: "
      >|< (x2 - x1)
      >|< "px;\""
    )
    (text " ")
  where
    (x1, y1) = pos from
    (x2, y2) = pos to

chrVisualize :: SolveTrace' C (MBP.StoredCHR C G P P) S -> PP_Doc
chrVisualize trace = tag' "html" $
  tag' "head" (
    tag' "title" (text "CHR visualization")
    -- >|< tag "script" (text "type=\"text/javascript\"") (text scripts)
    >|< tag' "style" styles
  )
  >|< tag' "body" (
    body
    -- hlist (map showVarHeader vars)
    -- >|< tag "div" (text "class=\"content\"") (hlistReverse (map (showNode order) nodes))
  )
  where
    graph = createGraph trace
    body = ufold reduce Emp graph >|< hlist (fmap (showEdge pos) $ edges graph)
    reduce (inn, id, node, out) right = showNode pos (id, node) >|< right
    pos :: Node -> (Int, Int)
    pos node = (node * 30, node * 38)
      -- text "margin-left: " >|< pp (node * 30) >|< text "px"
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

styles :: PP_Doc
styles =
  text "body {\n\
       \  font-size: 9pt;\n\
       \  font-family: Arial;\n\
       \}\n\
       \.rule {\n\
       \  position: absolute;\n\
       \}\n\
       \.rule-text {\n\
       \  border: 1px solid #aaa;\n\
       \  background-color: #fff;\n\
       \  display: inline-block;\n\
       \  padding: 2px;\n\
       \  margin: 3px 1px 0;\n\
       \}\n\
       \.rule-alt {\n\
       \  display: inline-block;\n\
       \  color: #A89942;\n\
       \}\n\
       \.edge-ver, .edge-hor {\n\
       \  position: absolute;\n\
       \  width: 6px;\n\
       \  height: 6px;\n\
       \  background-color: #578999;\n\
       \  opacity: 0.6;\n\
       \  margin-left: 15px;\n\
       \  margin-top: 8px;\n\
       \  z-index: -1;\n\
       \}\n\
       \"
  {- >|< hlist (fmap styleVar varIndices)
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
      >|< text "{\n  opacity: 1;\n}\n" -}
