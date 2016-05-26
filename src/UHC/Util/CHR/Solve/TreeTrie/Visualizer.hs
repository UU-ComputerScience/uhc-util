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

data NodeData
  = NodeRule -- Rule with first alt
    { nrLevel       :: Int
    , nrColumn      :: Int
    , nrName        :: String
    , nrRuleVars    :: [Tm]
    , nrFirstAlt    :: Maybe C
    }
  | NodeAlt  -- Additional alts of a rule
    { naLevel       :: Int
    , naColumn      :: Int
    , naConstraint  :: C
    }
  | NodeSynthesized -- Added node to make a proper layered graph
    { nsLevel       :: Int
    , nsColumn      :: Int
    , nsEdgeKind    :: EdgeKind
    }

data EdgeKind
  = EdgeGuard -- Usage of term in guard of rule.
  | EdgeHead  -- Usage of term in head of rule.
  | EdgeUnify -- Usage of other term that required unification of this node.
  | EdgeAlt   -- Link between NodeRule and NodeAlt. Both nodes have same level.
  deriving Eq

nodeLevel, nodeColumn :: Node' -> Int
nodeLevel (_, NodeRule{nrLevel = level})        = level
nodeLevel (_, NodeAlt{naLevel = level})         = level
nodeLevel (_, NodeSynthesized{nsLevel = level}) = level
nodeColumn (_, NodeRule{nrColumn = col})        = col
nodeColumn (_, NodeAlt{naColumn = col})         = col
nodeColumn (_, NodeSynthesized{nsColumn = col}) = col

nodeSetColumn :: Node' -> Int -> Node'
nodeSetColumn (n, d@NodeRule{}) col        = (n, d{nrColumn = col})
nodeSetColumn (n, d@NodeAlt{}) col         = (n, d{naColumn = col})
nodeSetColumn (n, d@NodeSynthesized{}) col = (n, d{nsColumn = col})

type Node' = LNode NodeData
type Edge' = LEdge EdgeKind

stateMap :: (a -> b -> (c, b)) -> b -> [a] -> ([c], b)
stateMap _  state []     = ([], state)
stateMap cb state (x:xs) = (y:ys, newState)
  where
    (ys,tmpState) = stateMap cb state xs
    (y,newState)  = cb x tmpState

type NodeMap = Map.Map Tm (Node, [Node])
data BuildState = BuildState [Edge'] NodeMap Int Int

replaceInTm :: Tm -> Tm -> Tm -> [Tm]
replaceInTm a b tm
  | tm == a || tm == b = [a, b]
  | otherwise          = case tm of
    Tm_Con name tms -> fmap (Tm_Con name) (replaceList tms)
    Tm_Lst tms ltm  -> do
      tms' <- replaceList tms
      ltm' <- replaceMaybe ltm
      return $ Tm_Lst tms' ltm'
    Tm_Op op tms    -> fmap (Tm_Op op) (replaceList tms)
    x               -> [x]
    where
      replaceList = sequence . fmap (replaceInTm a b)
      replaceMaybe Nothing  = [Nothing]
      replaceMaybe (Just y) = fmap Just $ replaceInTm a b y

emptyBuildState :: BuildState
emptyBuildState = BuildState [] Map.empty 0 0

tmsInC :: C -> [Tm]
tmsInC (C_Con s tms) = [Tm_Con s tms]
tmsInC _             = []

tmsInG :: G -> [Tm]
tmsInG (G_Tm tm) = tmsInTm tm
tmsInG _         = []

precedentTms :: Rule C G P P -> [(Tm, EdgeKind)]
precedentTms rule
  =  fmap (\n -> (n, EdgeHead))  (concatMap tmsInC $ ruleHead rule)
  ++ fmap (\n -> (n, EdgeGuard)) (concatMap tmsInG $ ruleGuard rule)

tmsInBodyAlt :: RuleBodyAlt C bprio -> [Tm]
tmsInBodyAlt = concatMap tmsInC . rbodyaltBody

tmsInTm :: Tm -> [Tm]
tmsInTm tm = tm : children tm
  where
    children (Tm_Lst as Nothing)  = as
    children (Tm_Lst as (Just a)) = as ++ [a]
    children _                    = [] 

addConstraint :: C -> Node -> NodeMap -> NodeMap
addConstraint (CB_Eq a b)   = addUnify a b
addConstraint (C_Con s tms) = addTerm $ Tm_Con s tms
addConstraint c             = const id

addTerm :: Tm -> Node -> NodeMap -> NodeMap
addTerm tm node =  Map.insert tm (node, [])

addUnify :: Tm -> Tm -> Node -> NodeMap -> NodeMap
addUnify a b node map = Map.foldlWithKey cb map map
  where
    cb :: NodeMap -> Tm -> (Node, [Node]) -> NodeMap
    cb map' tm (n, nodes) = List.foldl (\map'' key -> insertWith compare key (n, node : nodes) map'') map' (replaceInTm a b tm)
    compare x@(_, nodes1) y@(_, nodes2)
      | length nodes1 <= length nodes2 = x
      | otherwise                      = y

first :: [a] -> Maybe a
first []    = Nothing
first (x:_) = Just x

stepToNodes :: SolveStep' C (MBP.StoredCHR C G P P) S -> BuildState -> ([Node'], BuildState)
stepToNodes step state@(BuildState edges nodeMap nodeId level)
  = ( nodes
    , BuildState edges'' nodeMap' nodeId' level'
    )
  where
    schr = stepChr step
    rule = MBP.storedChrRule' schr
    updRule = varUpd (stepSubst step) rule
    alt = maybe [] (fmap $ varUpd $ stepSubst step) $ stepAlt step
    (nodes, BuildState edges' nodeMap' nodeId' level') =
      createNodes
        (maybe "[untitled]" id (ruleName rule))
        (Map.elems (stepSubst step))
        alt
        state
    edges'' =
      ( List.map (\(n, kind) -> (n, nodeId, kind))
        $ concatMap (\(n, ns, kind) -> (n, kind) : fmap (\x -> (x, EdgeUnify)) ns)
        $ Maybe.mapMaybe
          (\(tm, kind) -> fmap
            (\(n, ns) -> (n, ns, kind))
            (Map.lookup tm nodeMap))
          (precedentTms updRule)
      )
      ++ edges'

createNodes :: String -> [Tm] -> [C] -> BuildState -> ([Node'], BuildState)
createNodes name vars alts (BuildState edges nodeMap nodeId level)
  = ( nodes
    , BuildState edges' nodeMap' (nodeId + max 1 (length alts)) (level + 1)
    )
  where
    nodes =
      (nodeId, NodeRule
        { nrLevel    = level
        , nrColumn   = 0
        , nrName     = name
        , nrRuleVars = vars
        , nrFirstAlt = first alts
        }
      )
      : altNodes
    altTms = concatMap tmsInC alts
    nodeMap' = List.foldl updateMap nodeMap nodes
    -- Updates node map for a new node
    updateMap :: NodeMap -> Node' -> NodeMap
    updateMap map (id, NodeRule{ nrFirstAlt = Just alt }) = addConstraint alt id map
    updateMap map (id, NodeAlt{ naConstraint = alt }) = addConstraint alt id map
    updateMap map _ = map
    
    altNode (constraint, i) = (nodeId + i, NodeAlt level 0 constraint)
    altNodes = fmap altNode (drop 1 $ addIndices alts)
    edges' =
      (fmap (\(n, _) -> (nodeId, n, EdgeAlt)) altNodes)
      ++ edges

createGraph :: [C] -> [SolveStep' C (MBP.StoredCHR C G P P) S] -> Gr NodeData EdgeKind
createGraph query steps = mkGraph (nodes ++ queryNodes) edges
  where
    (queryNodes, state) = createNodes "?" [] query emptyBuildState
    -- queryNode = (0, NodeRule 0 "?" [] $ first query)
    -- state     = BuildState [] (addConstraints 0 Map.empty $ concatMap tmsInC query) 1 1
    (nodes', (BuildState edges _ _ _)) = stateMap stepToNodes state steps
    nodes     = concat nodes'

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

showNode :: (Node' -> (Int, Int)) -> Node' -> PP_Doc
showNode pos node@(_, NodeRule{nrLevel = level, nrName = name, nrRuleVars = vars, nrFirstAlt = alt}) = tag "div"
  (
    text "class=\"rule\" style=\"top: "
    >|< pp y 
    >|< text "px; left: "
    >|< pp x
    >|< text "px;\""
  )
  (
    tag "span" (text "class=\"" >|< className >|< text "\"") (
      (text name)
      >|< (hlist (fmap ((" " >|<) . pp) vars))
    )
    >|< tag' "br" Emp
    >|< text "&#8627;"
    >|< tag "span" (text "class=\"rule-alt\"") altText
  )
  where
    (x, y) = pos node
    altText = maybe (text ".") pp alt
    className = text "rule-text"
    showUsage name var = tag "div" (text $ "class=\"" ++ className ++ "\"") (text " ")
      where
        className = name ++ " var-" ++ var
showNode pos node@(_, NodeAlt{ naConstraint = constraint }) = tag "div"
  (
    text "class=\"rule-additional-alt\" style=\"top: "
    >|< pp y 
    >|< text "px; left: "
    >|< pp x
    >|< text "px;\""
  )
  (
    text "&#8627;"
    >|< tag "span" (text "class=\"rule-alt\"") (pp constraint)
  )
  where
    (x, y) = pos node

showEdge :: (Node -> (Int, Int)) -> Edge' -> PP_Doc
showEdge pos (from, to, kind) =
  if kind == EdgeAlt then
    -- Edge between rule and alt of same rule
    tag "div"
      (
        text "class=\"edge-alt\" style=\"top: "
        >|< pp y1
        >|< "px; left: "
        >|< pp (min x1 x2)
        >|< "px; width: "
        >|< abs (x2 - x1 - 20)
        >|< "px;\""
      )
      (text " ")
  else
    tag "div"
      (
        text "class=\"edge-ver "
        >|< text className
        >|< text "\" style=\"top: "
        >|< pp (y1 + 17)
        >|< "px; left: "
        >|< pp x1
        >|< "px; height: "
        >|< (y2 - y1 - 37)
        >|< "px;\""
      )
      (text " ")
    >|< tag "div"
      (
        text "class=\"edge-hor edge-hor-"
        >|< text (if x2 > x1 then "left " else "right ")
        >|< text className
        >|< text "\" style=\"top: "
        >|< pp (y2 - 20)
        >|< "px; left: "
        >|< pp (min x1 x2)
        >|< "px; width: "
        >|< abs (x2 - x1)
        >|< "px;\""
      )
      (text " ")
  where
    (x1, y1)  = pos from
    (x2, y2)  = pos to
    className = case kind of
      EdgeAlt   -> ""
      EdgeGuard -> "edge-guard"
      EdgeHead  -> "edge-head"
      EdgeUnify -> "edge-unify"

chrVisualize :: [C] -> SolveTrace' C (MBP.StoredCHR C G P P) S -> PP_Doc
chrVisualize query trace = tag' "html" $
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
    graph = createGraph query trace
    body = ufold reduce Emp graph >|< hlist (fmap (showEdge posId) $ labEdges graph)
    reduce (inn, id, node, out) right = showNode pos (id, node) >|< right
    nodeCount = length $ nodes graph
    column :: Node -> Int
    column x
      | x `mod` 2 == 0         = x
      | nodeCount `mod` 2 == 0 = nodeCount - x
      | otherwise              = nodeCount - 1 - x
    pos :: Node' -> (Int, Int)
    pos (id, NodeRule{nrLevel = level}) = ((column id) * 70, level * 38)
    pos (id, NodeAlt{naLevel = level}) = ((column id) * 70, level * 38)
    posId :: Node -> (Int, Int)
    posId node = pos (node, fromJust $ lab graph node)
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
       \  white-space: nowrap;\n\
       \}\n\
       \.rule-text {\n\
       \  border: 1px solid #aaa;\n\
       \  background-color: #fff;\n\
       \  display: inline-block;\n\
       \  padding: 2px;\n\
       \  margin: 3px 1px 0;\n\
       \  min-width: 30px;\n\
       \  text-align: center;\n\
       \}\n\
       \.rule-alt {\n\
       \  display: inline-block;\n\
       \  color: #A89942;\n\
       \  background: #fff;\n\
       \}\n\
       \.rule-additional-alt {\n\
       \  position: absolute;\n\
       \  white-space: nowrap;\n\
       \  margin-top: 24px;\n\
       \}\n\
       \.edge-ver {\n\
       \  position: absolute;\n\
       \  width: 0px;\n\
       \  border-left: 6px solid #578999;\n\
       \  opacity: 0.4;\n\
       \  margin-left: 15px;\n\
       \  margin-top: 8px;\n\
       \  z-index: -1;\n\
       \}\n\
       \.edge-hor {\n\
       \  position: absolute;\n\
       \  height: 20px;\n\
       \  border-bottom: 6px solid #578999;\n\
       \  opacity: 0.4;\n\
       \  margin-left: 15px;\n\
       \  margin-top: 8px;\n\
       \  z-index: -1;\n\
       \}\n\
       \.edge-hor-left {\n\
       \  border-bottom-left-radius: 16px;\n\
       \  border-left: 6px solid #578999;\n\
       \}\n\
       \.edge-hor-right {\n\
       \  border-bottom-right-radius: 16px;\n\
       \  border-right: 6px solid #578999;\n\
       \}\n\
       \.edge-guard {\n\
       \  border-color: #69B5A7;\n\
       \}\n\
       \.edge-unify {\n\
       \  border-color: #8CBF7A;\n\
       \}\n\
       \.edge-alt {\n\
       \  height: 1px;\n\
       \  background-color: #aaa;\n\
       \  position: absolute;\n\
       \  margin-top: 19px;\n\
       \  z-index: -1;\n\
       \  padding-right: 22px;\n\
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
