{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

module UHC.Util.CHR.Key
  (
    TTKeyableOpts(..)
  , defaultTTKeyableOpts
  
  , TTKeyable(..)
  , toTTKey
  )
  where

import UHC.Util.TreeTrie

-------------------------------------------------------------------------------------------
--- TTKeyable
-------------------------------------------------------------------------------------------

data TTKeyableOpts
  = TTKeyableOpts
      { ttkoptsVarsAsWild       :: Bool             -- treat vars as wildcards
      }

defaultTTKeyableOpts = TTKeyableOpts True

-- | TreeTrie key construction
class TTKeyable x where -- key | x -> key where
  type TTKey x :: *
  toTTKey'                  :: TTKeyableOpts -> x ->  TreeTrieKey  (TTKey x)                          -- option parameterized constuction
  toTTKeyParentChildren'    :: TTKeyableOpts -> x -> (TreeTrie1Key (TTKey x), [TreeTrieMpKey  (TTKey x)])   -- building block: parent of children + children
  
  -- default impl
  toTTKey' o                    = uncurry ttkAdd' . toTTKeyParentChildren' o
  toTTKeyParentChildren' o      = ttkParentChildren . toTTKey' o

toTTKey :: TTKeyable x => x -> TreeTrieKey (TTKey x)
toTTKey = toTTKey' defaultTTKeyableOpts


