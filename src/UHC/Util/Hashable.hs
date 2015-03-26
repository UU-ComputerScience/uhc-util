{-| Re-export of hashable package,
    in addition providing some of the instances for datatypes defined in the remainder of the uhc-util package.
-}

module UHC.Util.Hashable
  ( module Data.Hashable
  )
  where

import Data.Hashable
import UHC.Util.FPath

-- Instances

instance Hashable FPath
