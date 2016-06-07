{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}

module UHC.Util.CHR.Solve.TreeTrie.Visualizer
  ( chrVisualize
  )
  where

import           Prelude
import           Data.Maybe as Maybe
import           Data.List as List
import qualified Data.Map as Map
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
type Edge' = LEdge (EdgeKind, Bool)

stateMap :: (a -> b -> (c, b)) -> b -> [a] -> ([c], b)
stateMap _  state []     = ([], state)
stateMap cb state (x:xs) = (y:ys, newState)
  where
    (ys,tmpState) = stateMap cb state xs
    (y,newState)  = cb x tmpState

type NodeMap = Map.Map Tm (Node, [Node])
data BuildState = BuildState [Edge'] NodeMap Int Int

nodeLookup :: [Node'] -> Node -> Node'
nodeLookup nodes = fromJust . (flip Map.lookup) map
  where
    map :: Map.Map Node Node'
    map = foldl ins Map.empty nodes
    ins m node@(id, _) = Map.insert id node m

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
    cb map' tm (n, nodes) = List.foldl (\map'' key -> Map.insertWith compare key (n, node : nodes) map'') map' (replaceInTm a b tm)
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
      ( List.map (\(n, kind) -> (n, nodeId, (kind, True)))
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
      (fmap (\(n, _) -> (nodeId, n, (EdgeAlt, True))) altNodes)
      ++ edges

createSynthesizedNodes :: [Node'] -> [Edge'] -> Int -> ([Edge'], [Node'])
createSynthesizedNodes nodes es firstNode
  = create es firstNode [] []
  where
    create :: [Edge'] -> Node -> [Edge'] -> [Node'] -> ([Edge'], [Node'])
    create ((edge@(from, to, (kind, _))):edges) id accumEdges accumNodes
      = create edges id' (es ++ accumEdges) (ns ++ accumNodes)
      where
        (es, ns, id') = split (level from) edge id
    create _ _ accumEdges accumNodes = (accumEdges, accumNodes)
    split fromLevel edge@(from, to, (kind, _)) id
      | fromLevel + 1 >= level to = ([edge], [], id)
      | otherwise                 =
        ( (from, id, (kind, False)) : edges',
          (id, (NodeSynthesized (fromLevel + 1) 0 kind)) : nodes',
          id'
        )
        where
          (edges', nodes', id') = split (fromLevel + 1) (id, to, (kind, True)) (id + 1)
    find = nodeLookup nodes
    level = nodeLevel . find

createGraph :: [C] -> [SolveStep' C (MBP.StoredCHR C G P P) S] -> Gr NodeData (EdgeKind, Bool)
createGraph query steps = mkGraph sortedlayerednodes edges
  where
    sortedlayerednodes = flayer ++ sortNodes ([flayer] ++ (tail lnodes)) edges
    flayer = sortFirstLayer (head lnodes) 0
    lnodes = Map.elems $ layerednodes nodes
    layerednodes :: [Node'] -> Map.Map Int [Node']
    layerednodes ns = foldl (\m x -> Map.insertWith (++) (nodeLevel x) [x] m) Map.empty ns
    (queryNodes, state) = createNodes "?" [] query emptyBuildState
    (nodes'', (BuildState edges' _ id _)) = stateMap stepToNodes state steps
    nodes' = concat nodes'' ++ queryNodes
    (edges, synNodes) = createSynthesizedNodes nodes' edges' id
    nodes = nodes' ++ synNodes

sortFirstLayer :: [Node'] -> Int -> [Node']
sortFirstLayer [] i = []
sortFirstLayer (x:xs) i = nodeSetColumn x i : sortFirstLayer xs (i + 1)
    
sortNodes :: [[Node']] -> [Edge'] -> [Node']
sortNodes (x:[]) e = []
sortNodes (x:xs:xss) e = medianHeurstic x xs e ++ sortNodes (xs:xss) e
    
medianHeurstic :: [Node'] -> [Node'] -> [Edge'] -> [Node']
medianHeurstic l1 l2 e = unique sortedMedianList 0
  where
    sortedMedianList = sortOn nodeColumn medianList
    medianList = map (\x -> nodeSetColumn x (median x)) l2
    median n = coordinates n !! (ceiling (realToFrac (length (coordinates n)) / 2) - 1)
    coordinates n = map nodeColumn (neighbors n)
    neighbors n = map (nodelist . fst') (edges n)
    edges n = List.filter (\x -> snd' x == fst n) e 
    nodelist = nodeLookup l1

unique :: [a] -> Int -> [a]
unique l@(n:ns) i = nodeSetColumn n i : unique ns (i+1)
unique _ _ = []
    
fst' :: (a, b, c) -> a
fst' (a, _, _) = a
    
snd' :: (a, b, c) -> b
snd' (_, b, _) = b

tag :: String -> PP_Doc -> PP_Doc -> PP_Doc
tag name attr content = (text ("<" ++ name)) >|< attributes attr >|< body content
  where
    attributes Emp = Emp
    attributes a   = text " " >|< a
    body Emp       = text " />"
    body content   = text ">" >|< content >|< text ("</" ++ name ++ ">")

tag' :: String -> PP_Doc -> PP_Doc
tag' name = tag name Emp

addIndices :: [a] -> [(a, Int)]
addIndices = flip zip [0..]

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
showNode _ (_, NodeSynthesized{}) = Emp

showEdge :: (Node -> (Int, Int)) -> Edge' -> PP_Doc
showEdge pos (from, to, (kind, isEnd)) =
  if kind == EdgeAlt then
    -- Edge between rule and alt of same rule
    tag "div"
      (
        text "class=\"edge-alt\" style=\"top: "
        >|< pp y1
        >|< "px; left: "
        >|< pp (min x1 x2)
        >|< "px; width: "
        >|< abs (x2 - x1 - 16)
        >|< "px;\""
      )
      (text " ")
  else
    tag "div"
      (
        text "class=\"edge-ver "
        >|< text className
        >|< text "\" style=\"top: "
        >|< pp (y1 + 35)
        >|< "px; left: "
        >|< pp x1
        >|< "px; height: "
        >|< (y2 - y1 - 60 - 6)
        >|< "px;\""
      )
      (text " ")
    >|< tag "div"
      (
        text "class=\"edge-hor"
        >|< text (if x2 > x1 then " edge-hor-left " else if x2 < x1 then " edge-hor-right " else " edge-hor-no-curve ")
        >|< text className
        >|< text "\" style=\"top: "
        >|< pp (y2 - 19)
        >|< "px; left: "
        >|< pp (if x1 < x2 then x1 else x2 + (if isEnd then 0 else (abs (x2 - x1) + 1) `div` 2))
        >|< "px; width: "
        >|< pp (abs (x2 - x1) `div` (if isEnd then 1 else 2))
        >|< "px;\""
      )
      (text " ")
    >|< (if isEnd then Emp else tag "div"
        (
          text "class=\"edge-end edge-end-"
          >|< text (if x2 > x1 then "left " else if x2 < x1 then "right " else "no-curve ")
          >|< text className
          >|< text "\" style=\"top: "
          >|< pp (y2 - 3 + 11)
          >|< "px; left: "
          >|< pp (if x1 < x2 then x2 - 16 else x2)
          >|< pp "px; width: "
          >|< pp (if x1 == x2 then 0 else ((abs (x2 - x1) + 1) `div` 2) - 6)
          >|< "px;\""
        )
        (text " ")
    )
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
    >|< tag' "style" styles
  )
  >|< tag' "body" (
    body
  )
  where
    graph = createGraph query trace
    body = ufold reduce Emp graph >|< hlist (fmap (showEdge posId) $ labEdges graph)
    reduce (inn, id, node, out) right = showNode pos (id, node) >|< right
    nodeCount = length $ nodes graph
    pos :: Node' -> (Int, Int)
    pos n = ((nodeColumn n) * 200, (nodeLevel n) * 60)
    posId :: Node -> (Int, Int)
    posId node = pos (node, fromJust $ lab graph node)

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
       \  margin-top: 9px;\n\
       \  z-index: -1;\n\
       \}\n\
       \.edge-hor {\n\
       \  position: absolute;\n\
       \  height: 27px;\n\
       \  border-bottom: 6px solid #578999;\n\
       \  opacity: 0.4;\n\
       \  margin-left: 15px;\n\
       \  margin-top: 8px;\n\
       \  z-index: -1;\n\
       \}\n\
       \.edge-diag {\n\
       \  transform-origin: 50% 50%;\n\
       \  position: absolute;\n\
       \  height: 6px;\n\
       \}\n\
       \.edge-hor-left {\n\
       \  border-bottom-left-radius: 100% 33px;\n\
       \  border-left: 6px solid #578999;\n\
       \}\n\
       \.edge-hor-right {\n\
       \  border-bottom-right-radius: 100% 33px;\n\
       \  border-right: 6px solid #578999;\n\
       \}\n\
       \.edge-hor-no-curve {\n\
       \  border-right: 6px solid #578999;\n\
       \}\n\
       \.edge-end {\n\
       \  position: absolute;\n\
       \  height: 27px;\n\
       \  width: 16px;\n\
       \  border-top: 6px solid #578999;\n\
       \  opacity: 0.4;\n\
       \  margin-left: 15px;\n\
       \  margin-top: 8px;\n\
       \  z-index: -1;\n\
       \}\n\
       \.edge-end-left {\n\
       \  border-top-right-radius: 100% 33px;\n\
       \  border-right: 6px solid #578999;\n\
       \}\n\
       \.edge-end-no-curve {\n\
       \  border-right: 6px solid #578999;\n\
       \  margin-top: 14px;\n\
       \  height: 21px;\n\
       \}\n\
       \.edge-end-right {\n\
       \  border-top-left-radius: 100% 33px;\n\
       \  border-left: 6px solid #578999;\n\
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
