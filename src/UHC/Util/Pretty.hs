
-------------------------------------------------------------------------
-- Wrapper module around pretty printing
-------------------------------------------------------------------------

module UHC.Util.Pretty
  ( -- module UU.Pretty
    -- module UHC.Util.Chitil.Pretty
    module CHR.Pretty

  , putPPFPath
  )
  where

-- import UU.Pretty
-- import UHC.Util.Chitil.Pretty
import CHR.Pretty
import           UHC.Util.FPath
import           System.IO


-------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------


instance PP FPath where
  pp = pp . fpathToStr



-------------------------------------------------------------------------
-- PP printing to file
-------------------------------------------------------------------------



putPPFPath :: FPath -> PP_Doc -> Int -> IO ()
putPPFPath fp pp wid
  = do { fpathEnsureExists fp
       ; putPPFile (fpathToStr fp) pp wid
       }

