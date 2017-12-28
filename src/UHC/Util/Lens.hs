{-| Minimal redefine + re-export of a lens package, fclabels currently.
    in addition providing some of the instances for datatypes defined in the remainder of the uhc-util package.
-}

{-# LANGUAGE TypeOperators, NoMonomorphismRestriction #-}

module UHC.Util.Lens
  ( module CHR.Data.Lens

  )
  where

import CHR.Data.Lens

{-
-- * Wrappers

-- | Wrapper around a Maybe with a default in case of Nothing
isoMbWithDefault :: o -> (f :-> Maybe o) -> (f :-> o)
isoMbWithDefault dflt f = iso (Iso (maybe dflt id) (Just)) . f

-- | Wrapper around a Maybe with an embedded panic in case of Nothing, with a panic message
isoMb :: String -> (f :-> Maybe o) -> (f :-> o)
isoMb msg f = iso (Iso (panicJust msg) (Just)) . f
-}
