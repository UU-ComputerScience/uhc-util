-------------------------------------------------------------------------------------------
--- Freshness of something
-------------------------------------------------------------------------------------------

module UHC.Util.Fresh
  ( -- MonadFresh(..)
    Fresh(..)
  )
  where

{-
class Monad m => MonadFresh f m where
  -- | Fresh single 'f'
  fresh :: m f
  fresh = freshInf

  -- | Fresh infinite range of 'f'
  freshInf :: m f
  freshInf = fresh
-}

class Fresh fs f where
  -- | Fresh single 'f'
  fresh :: fs -> (f,fs)
  fresh = freshInf

  -- | Fresh infinite range of 'f'
  freshInf :: fs -> (f,fs)
  freshInf = fresh

instance Fresh Int Int where
  fresh i = (i, i+1)

instance Fresh Int String where
  fresh i = ("$" ++ show i, i+1)
