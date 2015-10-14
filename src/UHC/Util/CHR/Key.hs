{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FunctionalDependencies #-}

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
class TTKeyable x key | x -> key where
  -- type TTKey x :: *
  toTTKey'                  :: TTKeyableOpts -> x ->  TreeTrieKey  (key)                          -- option parameterized constuction
  toTTKeyParentChildren'    :: TTKeyableOpts -> x -> (TreeTrie1Key (key), [TreeTrieMpKey  (key)])   -- building block: parent of children + children
  
  -- default impl
  toTTKey' o                    = uncurry ttkAdd' . toTTKeyParentChildren' o
  toTTKeyParentChildren' o      = ttkParentChildren . toTTKey' o

toTTKey :: TTKeyable x key => x -> TreeTrieKey (key)
toTTKey = toTTKey' defaultTTKeyableOpts


