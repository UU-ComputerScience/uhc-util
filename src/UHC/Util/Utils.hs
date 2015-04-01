{-# LANGUAGE CPP #-}

module UHC.Util.Utils
  ( -- * Set
    unionMapSet

    -- * Map
  , inverseMap
  , showStringMapKeys
  
  , mapLookup2', mapLookup2
  
    -- * List
  , hdAndTl', hdAndTl
  , maybeNull, maybeHd
  , wordsBy
  , initlast, initlast2
  , last'
  , firstNotEmpty
  , listSaturate, listSaturateWith
  , spanOnRest
  
    -- * Tuple
  , tup123to1, tup123to2
  , tup123to12, tup123to23
  , tup12to123

    -- * String
  , strWhite
  , strPad
  , strCapitalize
  , strToInt
  
  , splitForQualified
  
    -- * Misc
  , panic
  
  , isSortedByOn
  , sortOn
  , sortByOn
  , groupOn
  , groupByOn
  , groupSortOn
  , groupSortByOn
  , nubOn
  
  , consecutiveBy
  
  , partitionAndRebuild
  
  , orderingLexic
  
    -- * Maybe
  , panicJust
  , ($?)
  , orMb
  , maybeAnd
  , maybeOr
  
    -- * Graph
  , scc
  
    -- * MOnad
  , firstMaybeM
  )
  where

-- import UHC.Util.Pretty
import Data.Char
import Data.List
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Graph as Graph

-------------------------------------------------------------------------
-- Set
-------------------------------------------------------------------------

-- | Union a set where each element itself is mapped to a set
unionMapSet :: Ord b => (a -> Set.Set b) -> (Set.Set a -> Set.Set b)
unionMapSet f = Set.unions . map f . Set.toList

-------------------------------------------------------------------------
-- Map
-------------------------------------------------------------------------

-- | Inverse of a map
inverseMap :: (Ord k, Ord v') => (k -> v -> (v',k')) -> Map.Map k v -> Map.Map v' k'
inverseMap mk = Map.fromList . map (uncurry mk) . Map.toList

-- | Show keys of map using a separator
showStringMapKeys :: Map.Map String x -> String -> String
showStringMapKeys m sep = concat $ intersperse sep $ Map.keys m

-------------------------------------------------------------------------
-- List
-------------------------------------------------------------------------

-- | Get head and tail, with default if empty list
hdAndTl' :: a -> [a] -> (a,[a])
hdAndTl' _ (a:as) = (a,as)
hdAndTl' n []     = (n,[])

-- | Get head and tail, with panic/error if empty list
hdAndTl :: [a] -> (a,[a])
hdAndTl = hdAndTl' (panic "hdAndTl")
{-# INLINE hdAndTl  #-}

maybeNull :: r -> ([a] -> r) -> [a] -> r
maybeNull n f l = if null l then n else f l
{-# INLINE maybeNull  #-}

maybeHd :: r -> (a -> r) -> [a] -> r
maybeHd n f = maybeNull n (f . head)
{-# INLINE maybeHd  #-}

-- | Split up in words by predicate
wordsBy :: (a -> Bool) -> [a] -> [[a]]
wordsBy p l
  = w l
  where w [] = []
        w l  = let (l',ls') = break p l
               in  l' : case ls' of []       -> []
                                    (_:[])   -> [[]]
                                    (_:ls'') -> w ls''

-- | Possibly last element and init
initlast :: [a] -> Maybe ([a],a)
initlast as
  = il [] as
  where il acc [a]    = Just (reverse acc,a)
        il acc (a:as) = il (a:acc) as
        il _   _      = Nothing

-- | variation on last which returns empty value instead of
last' :: a -> [a] -> a
last' e = maybe e snd . initlast

-- | Possibly last and preceding element and init
initlast2 :: [a] -> Maybe ([a],a,a)
initlast2 as
  = il [] as
  where il acc [a,b]  = Just (reverse acc,a,b)
        il acc (a:as) = il (a:acc) as
        il _   _      = Nothing

-- | First non empty list of list of lists
firstNotEmpty :: [[x]] -> [x]
firstNotEmpty = maybeHd [] id . filter (not . null)

-- | Saturate a list, that is:
-- for all indices i between min and max,
-- if there is no listelement x for which  get x  returns i,
-- add an element  mk i  to the list
listSaturate :: (Enum a,Ord a) => a -> a -> (x -> a) -> (a -> x) -> [x] -> [x]
listSaturate min max get mk xs
  = [ Map.findWithDefault (mk i) i mp | i <- [min..max] ]
  where mp = Map.fromList [ (get x,x) | x <- xs ]

-- | Saturate a list with values from assoc list, that is:
-- for all indices i between min and max,
-- if there is no listelement x for which  get x  returns i,
-- add a candidate from the associationlist (which must be present) to the list
listSaturateWith :: (Enum a,Ord a) => a -> a -> (x -> a) -> [(a,x)] -> [x] -> [x]
listSaturateWith min max get missing l
  = listSaturate min max get mk l
  where mp = Map.fromList missing
        mk a = panicJust "listSaturateWith" $ Map.lookup a mp

-- variant on span, predicate on full list
spanOnRest :: ([a] -> Bool) -> [a] -> ([a],[a])
spanOnRest p []       = ([],[])
spanOnRest p xs@(x:xs')
	 | p xs      = (x:ys, zs)
	 | otherwise = ([],xs)
					   where (ys,zs) = spanOnRest p xs'

-------------------------------------------------------------------------
-- Tupling, untupling
-------------------------------------------------------------------------

tup123to1  (a,_,_) = a			-- aka fst3
tup123to2  (_,a,_) = a			-- aka snd3
tup123to12 (a,b,_) = (a,b)
tup123to23 (_,a,b) = (a,b)
tup12to123 c (a,b) = (a,b,c)

{-# INLINE tup123to1  #-}
{-# INLINE tup123to2  #-}
{-# INLINE tup123to12 #-}
{-# INLINE tup123to23 #-}
{-# INLINE tup12to123 #-}

-------------------------------------------------------------------------
-- String
-------------------------------------------------------------------------

-- | Blanks
strWhite :: Int -> String
strWhite sz = replicate sz ' '
{-# INLINE strWhite #-}

-- | Pad upto size with blanks
strPad :: String -> Int -> String
strPad s sz = s ++ strWhite (sz - length s)

-- | Capitalize first letter
strCapitalize :: String -> String
strCapitalize s
  = case s of
      (c:cs) -> toUpper c : cs
      _      -> s

-- | Convert string to Int
strToInt :: String -> Int
strToInt = foldl (\i c -> i * 10 + ord c - ord '0') 0

-------------------------------------------------------------------------
-- Split for qualified name
-------------------------------------------------------------------------

-- | Split into fragments based on '.' convention for qualified Haskell names
splitForQualified :: String -> [String]
splitForQualified s
    = ws''
    where ws  = wordsBy (=='.') s
          ws' = case initlast2 ws of
                  Just (ns,n,"") -> ns ++ [n ++ "."]
                  _              -> ws
          ws''= case break (=="") ws' of
                  (nq,(_:ns)) -> nq ++ [concatMap ("."++) ns]
                  _ -> ws'

-------------------------------------------------------------------------
-- Misc
-------------------------------------------------------------------------

-- | Error, with message
panic m = error ("panic: " ++ m)

-------------------------------------------------------------------------
-- group/sort/nub combi's
-------------------------------------------------------------------------

isSortedByOn :: (b -> b -> Ordering) -> (a -> b) -> [a] -> Bool
isSortedByOn cmp sel l
  = isSrt l
  where isSrt (x1:tl@(x2:_)) = cmp (sel x1) (sel x2) /= GT && isSrt tl
        isSrt _              = True

#if __GLASGOW_HASKELL__ >= 710
#else
sortOn :: Ord b => (a -> b) -> [a] -> [a]
sortOn = sortByOn compare
{-# INLINE sortOn #-}
#endif

sortByOn :: (b -> b -> Ordering) -> (a -> b) -> [a] -> [a]
sortByOn cmp sel = sortBy (\e1 e2 -> sel e1 `cmp` sel e2)

groupOn :: Eq b => (a -> b) -> [a] -> [[a]]
groupOn sel = groupBy (\e1 e2 -> sel e1 == sel e2)

groupSortOn :: Ord b => (a -> b) -> [a] -> [[a]]
groupSortOn sel = groupOn sel . sortOn sel

groupByOn :: (b -> b -> Bool) -> (a -> b) -> [a] -> [[a]]
groupByOn eq sel = groupBy (\e1 e2 -> sel e1 `eq` sel e2)

groupSortByOn :: (b -> b -> Ordering) -> (a -> b) -> [a] -> [[a]]
groupSortByOn cmp sel = groupByOn (\e1 e2 -> cmp e1 e2 == EQ) sel . sortByOn cmp sel

nubOn :: Eq b => (a->b) -> [a] -> [a]
nubOn sel = nubBy (\a1 a2 -> sel a1 == sel a2)

-- | The 'consecutiveBy' function groups like groupBy, but based on a function which says whether 2 elements are consecutive
consecutiveBy                  :: (a -> a -> Bool) -> [a] -> [[a]]
consecutiveBy _        []      =  []
consecutiveBy isConsec (x:xs)  =  ys : consecutiveBy isConsec zs
  where (ys,zs) = consec x xs
        consec x []                        = ([x],[])
        consec x yys@(y:ys) | isConsec x y = let (yys',zs) = consec y ys in (x:yys',zs)
                            | otherwise    = ([x],yys)

-------------------------------------------------------------------------
-- Partitioning with rebuild
-------------------------------------------------------------------------

-- | Partition, but also return a function which will rebuild according to the original ordering of list elements
partitionAndRebuild :: (v -> Bool) -> [v] -> ([v], [v], [v'] -> [v'] -> [v'])
partitionAndRebuild f (v:vs)
  | f v                  = (v : vs1,     vs2, \(r:r1)   r2  -> r : mk r1 r2)
  | otherwise            = (    vs1, v : vs2, \   r1 (r:r2) -> r : mk r1 r2)
  where (vs1,vs2,mk) = partitionAndRebuild f vs
partitionAndRebuild _ [] = ([], [], \_ _ -> [])

-------------------------------------------------------------------------
-- Ordering
-------------------------------------------------------------------------

-- | Reduce compare results lexicographically to one compare result
orderingLexic :: [Ordering] -> Ordering
orderingLexic = foldr1 (\o1 o2 -> if o1 == EQ then o2 else o1)

-------------------------------------------------------------------------
-- Maybe
-------------------------------------------------------------------------

panicJust :: String -> Maybe a -> a
panicJust m = maybe (panic m) id
{-# INLINE panicJust #-}

infixr 0  $?

($?) :: (a -> Maybe b) -> Maybe a -> Maybe b
f $? mx = do x <- mx
             f x

orMb :: Maybe a -> Maybe a -> Maybe a
orMb m1 m2 = maybe m2 (const m1) m1
-- orMb = maybeOr Nothing Just Just

maybeAnd :: x -> (a -> b -> x) -> Maybe a -> Maybe b -> x
maybeAnd n jj ma mb
  = case ma of
      Just a
        -> case mb of {Just b -> jj a b ; _ -> n}
      _ -> n

maybeOr :: x -> (a -> x) -> (b -> x) -> Maybe a -> Maybe b -> x
maybeOr n fa fb ma mb
  = case ma of
      Just a -> fa a
      _      -> case mb of
                  Just b -> fb b
                  _      -> n

-------------------------------------------------------------------------
-- Strongly Connected Components
-------------------------------------------------------------------------

scc :: Ord n => [(n,[n])] -> [[n]]
scc = map Graph.flattenSCC . Graph.stronglyConnComp . map (\(n,ns) -> (n, n, ns))

-------------------------------------------------------------------------
-- Map
-------------------------------------------------------------------------

-- | double lookup, with transformer for 2nd map
mapLookup2' :: (Ord k1, Ord k2) => (v1 -> Map.Map k2 v2) -> k1 -> k2 -> Map.Map k1 v1 -> Maybe (Map.Map k2 v2, v2)
mapLookup2' f k1 k2 m1
  = do m2 <- Map.lookup k1 m1
       let m2' = f m2
       fmap ((,) m2') $ Map.lookup k2 m2'

-- | double lookup
mapLookup2 :: (Ord k1, Ord k2) => k1 -> k2 -> Map.Map k1 (Map.Map k2 v2) -> Maybe v2
mapLookup2 k1 k2 m1 = fmap snd $ mapLookup2' id k1 k2 m1
{-# INLINE mapLookup2 #-}

-------------------------------------------------------------------------
-- Monad
-------------------------------------------------------------------------

-- | loop over monads yielding a Maybe from a start value, yielding the first Just or the start (when no Just is returned)
firstMaybeM :: Monad m => a -> [a -> m (Maybe a)] -> m a
firstMaybeM x []     = return x
firstMaybeM x (s:ss) = do mx <- s x
                          maybe (firstMaybeM x ss) return mx
