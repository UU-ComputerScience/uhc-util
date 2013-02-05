{- |
VarLookup abstracts from a Map.
The purpose is to be able to combine maps only for the purpose of searching without actually merging the maps.
This then avoids the later need to unmerge such mergings.
The class interface serves to hide this.
-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}

module UHC.Util.VarLookup
	( VarLookup (..)
	, varlookupMap
	, VarLookupFix, varlookupFix
	, varlookupFixDel
	, VarLookupCmb (..)
	, VarLookupBase (..)
	, VarLookupCmbFix, varlookupcmbFix
	
	, MetaLev
	, metaLevVal
    )
  where

-- import EH100.Base.Common
import Data.Maybe

-- | Level to lookup into
type MetaLev = Int

-- | Base level (of values, usually)
metaLevVal :: MetaLev
metaLevVal = 0

class VarLookup m k v where
  varlookupWithMetaLev :: MetaLev -> k -> m -> Maybe v
  varlookup :: k -> m -> Maybe v

  -- defaults
  varlookup = varlookupWithMetaLev 0

instance (VarLookup m1 k v,VarLookup m2 k v) => VarLookup (m1,m2) k v where
  varlookupWithMetaLev l k (m1,m2)
    = case varlookupWithMetaLev l k m1 of
        r@(Just _) -> r
        _          -> varlookupWithMetaLev l k m2

instance VarLookup m k v => VarLookup [m] k v where
  varlookupWithMetaLev l k ms = listToMaybe $ catMaybes $ map (varlookupWithMetaLev l k) ms

varlookupMap :: VarLookup m k v => (v -> Maybe res) -> k -> m -> Maybe res
varlookupMap get k m
  = do { v <- varlookup k m
       ; get v
       }

type VarLookupFix k v = k -> Maybe v

-- | fix looking up to be for a certain var mapping
varlookupFix :: VarLookup m k v => m -> VarLookupFix k v
varlookupFix m = \k -> varlookup k m

-- | simulate deletion
varlookupFixDel :: Ord k => [k] -> VarLookupFix k v -> VarLookupFix k v
varlookupFixDel ks f = \k -> if k `elem` ks then Nothing else f k

infixr 7 |+>

class VarLookupCmb m1 m2 where
  (|+>) :: m1 -> m2 -> m2

instance VarLookupCmb m1 m2 => VarLookupCmb m1 [m2] where
  m1 |+> (m2:m2s) = (m1 |+> m2) : m2s

instance (VarLookupCmb m1 m1, VarLookupCmb m1 m2) => VarLookupCmb [m1] [m2] where
  m1 |+> (m2:m2s) = (foldr1 (|+>) m1 |+> m2) : m2s

class VarLookupBase m k v | m -> k v where
  varlookupEmpty :: m
  -- varlookupTyUnit :: k -> v -> m

type VarLookupCmbFix m1 m2 = m1 -> m2 -> m2

-- | fix combining up to be for a certain var mapping
varlookupcmbFix :: VarLookupCmb m1 m2 => VarLookupCmbFix m1 m2
varlookupcmbFix m1 m2 = m1 |+> m2

