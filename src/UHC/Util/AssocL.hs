module UHC.Util.AssocL
    ( -- * Assoc list
      Assoc, AssocL
    , assocLMapElt, assocLMapKey
    , assocLElts, assocLKeys
    , assocLGroupSort
    , assocLMapUnzip
    , ppAssocL, ppAssocL', ppAssocLV
    , ppCurlysAssocL
    
      -- * Utils
    , combineToDistinguishedElts
    )
  where
import UHC.Util.Pretty
import UHC.Util.Utils
import Data.List
import Data.Maybe

-------------------------------------------------------------------------------------------
--- AssocL
-------------------------------------------------------------------------------------------

type Assoc k v = (k,v)
type AssocL k v = [Assoc k v]

ppAssocL' :: (PP k, PP v, PP s) => ([PP_Doc] -> PP_Doc) -> s -> AssocL k v -> PP_Doc
ppAssocL' ppL sep al = ppL (map (\(k,v) -> pp k >|< sep >#< pp v) al)

ppAssocL :: (PP k, PP v) => AssocL k v -> PP_Doc
ppAssocL = ppAssocL' (ppBlock "[" "]" ",") ":"

ppAssocLV :: (PP k, PP v) => AssocL k v -> PP_Doc
ppAssocLV = ppAssocL' vlist ":"

-- | intended for parsing
ppCurlysAssocL :: (k -> PP_Doc) -> (v -> PP_Doc) -> AssocL k v -> PP_Doc
ppCurlysAssocL pk pv = ppCurlysCommasBlock . map (\(k,v) -> pk k >#< "=" >#< pv v)

assocLMap :: (k -> v -> (k',v')) -> AssocL k v -> AssocL k' v'
assocLMap f = map (uncurry f)
{-# INLINE assocLMap #-}

assocLMapElt :: (v -> v') -> AssocL k v -> AssocL k v'
assocLMapElt f = assocLMap (\k v -> (k,f v))
{-# INLINE assocLMapElt #-}

assocLMapKey :: (k -> k') -> AssocL k v -> AssocL k' v
assocLMapKey f = assocLMap (\k v -> (f k,v))
{-# INLINE assocLMapKey #-}

assocLMapUnzip :: AssocL k (v1,v2) -> (AssocL k v1,AssocL k v2)
assocLMapUnzip l = unzip [ ((k,v1),(k,v2)) | (k,(v1,v2)) <- l ]

assocLKeys :: AssocL k v -> [k]
assocLKeys = map fst
{-# INLINE assocLKeys #-}

assocLElts :: AssocL k v -> [v]
assocLElts = map snd
{-# INLINE assocLElts #-}

assocLGroupSort :: Ord k => AssocL k v -> AssocL k [v]
assocLGroupSort = map (foldr (\(k,v) (_,vs) -> (k,v:vs)) (panic "UHC.Util.AssocL.assocLGroupSort" ,[])) . groupSortOn fst

-------------------------------------------------------------------------------------------
--- Utils: Combinations
-------------------------------------------------------------------------------------------

-- | Combine [[x1..xn],..,[y1..ym]] to [[x1..y1],[x2..y1],..,[xn..ym]].
--   Each element [xi..yi] is distinct based on the the key k in xi==(k,_)
combineToDistinguishedElts :: Eq k => [AssocL k v] -> [AssocL k v]
combineToDistinguishedElts []     = []
combineToDistinguishedElts [[]]   = []
combineToDistinguishedElts [x]    = map (:[]) x
combineToDistinguishedElts (l:ls)
  = combine l $ combineToDistinguishedElts ls
  where combine l ls
          = concatMap (\e@(k,_)
                         -> mapMaybe (\ll -> maybe (Just (e:ll)) (const Nothing) $ lookup k ll)
                                     ls
                      ) l

