{-| Relation via pair of maps for domain and range.
    Incomplete w.r.t. corresponding UHC.Util.Rel
-}
module UHC.Util.RelMap
  ( Rel
  , empty
  , toList, fromList
  , singleton
  , dom, rng
  , restrictDom, restrictRng
  -- , mapDom, mapRng
  -- , partitionDom, partitionRng
  -- , intersection, difference
  , union, unions
  , apply
  , toDomMap, toRngMap
  -- , mapDomRng
  )
  where

import qualified Data.Map as Map
import qualified Data.Set as Set

-------------------------------------------------------------------------
-- Relation
-------------------------------------------------------------------------

-- | Map used in a relation
type RelMap a b = Map.Map a (Set.Set b)

-- | Relation, represented as 2 maps from domain to range and the inverse, thus allowing faster lookup at the expense of some set like operations more expensive.
data Rel a b
  = Rel
     { relDomMp :: RelMap a b		-- ^ from domain to range
     , relRngMp :: RelMap b a		-- ^ from range to domain
     }

-- | As assocation list
toList :: Rel a b -> [(a,b)]
toList (Rel m _) = [ (d,r) | (d,rs) <- Map.toList m, r <- Set.toList rs ]

-- | From association list
fromList :: (Ord a, Ord b) => [(a,b)] -> Rel a b
fromList = unions . map (uncurry singleton)

-- | Singleton relation
singleton :: (Ord a, Ord b) => a -> b -> Rel a b
singleton a b = Rel (relMapSingleton a b) (relMapSingleton b a)

-- | Empty relation
empty :: Rel a b
empty = Rel Map.empty Map.empty

-- | Domain of relation
dom :: (Ord a, Ord b) => Rel a b -> Set.Set a
dom = Map.keysSet . relDomMp

-- | Range of relation
rng :: (Ord a, Ord b) => Rel a b -> Set.Set b
rng = Map.keysSet . relRngMp

-- | Filter on domain
restrictDom :: (Ord a, Ord b) => (a -> Bool) -> Rel a b -> Rel a b
restrictDom p (Rel d r) = Rel d' r'
  where d' = Map.filterWithKey (\d r -> p d) d
        r' = relMapInverse d'

-- | Filter on range
restrictRng :: (Ord a, Ord b) => (b -> Bool) -> Rel a b -> Rel a b
restrictRng p (Rel d r) = Rel d' r'
  where r' = Map.filterWithKey (\r d -> p r) r
        d' = relMapInverse r'

{-
-- | Map domain
mapDom :: (Ord a, Ord b, Ord x) => (a -> x) -> Rel a b -> Rel x b
mapDom f = Set.map (\(a,b) -> (f a,b))

-- | Map range
mapRng :: (Ord a, Ord b, Ord x) => (b -> x) -> Rel a b -> Rel a x
mapRng f = Set.map (\(a,b) -> (a,f b))

-- | Partition domain
partitionDom :: (Ord a, Ord b) => (a -> Bool) -> Rel a b -> (Rel a b,Rel a b)
partitionDom f = Set.partition (f . fst)

-- | Partition range
partitionRng :: (Ord a, Ord b) => (b -> Bool) -> Rel a b -> (Rel a b,Rel a b)
partitionRng f = Set.partition (f . snd)

-- | Intersect jointly on domain and range
intersection :: (Ord a, Ord b) => Rel a b -> Rel a b -> Rel a b
intersection = Set.intersection

-- | Difference jointly on domain and range
difference :: (Ord a, Ord b) => Rel a b -> Rel a b -> Rel a b
difference = Set.difference
-}

-- | Union
union :: (Ord a, Ord b) => Rel a b -> Rel a b -> Rel a b
union (Rel d1 r1) (Rel d2 r2) = Rel (Map.unionWith Set.union d1 d2) (Map.unionWith Set.union r1 r2)

-- | Union of list of relations
unions :: (Ord a, Ord b) => [Rel a b] -> Rel a b
unions [ ] = empty
unions [r] = r
unions rs  = foldr union empty rs

-- | Apply relation as a function
apply :: (Ord a, Ord b) => Rel a b -> a -> [b]
apply r a = maybe [] Set.toList $ Map.lookup a (relDomMp r)

-- | As a Map keyed on domain
toDomMap :: Ord a => Rel a b -> Map.Map a [b]
toDomMap = Map.map Set.toList . relDomMp

-- | As a Map keyed on range
toRngMap :: Ord b => Rel a b -> Map.Map b [a]
toRngMap = Map.map Set.toList . relRngMp

{-
-- | Map over domain and range
mapDomRng :: (Ord a, Ord b, Ord a', Ord b') => ((a,b) -> (a',b')) -> Rel a b -> Rel a' b'
mapDomRng = Set.map
-}

-------------------------------------------------------------------------
-- Util
-------------------------------------------------------------------------

-- | Singleton
relMapSingleton :: (Ord a, Ord b) => a -> b -> RelMap a b
relMapSingleton d r = Map.singleton d (Set.singleton r)

-- | Take the inverse of a map used in relation
relMapInverse :: (Ord a, Ord b) => RelMap a b -> RelMap b a
relMapInverse m = Map.unionsWith Set.union [ relMapSingleton r d | (d,rs) <- Map.toList m, r <- Set.toList rs ]
