-------------------------------------------------------------------------------------------
--- Generic terms describing constraints, providing interpretation to AST of your choice
-------------------------------------------------------------------------------------------

module UHC.Util.CHR.GTerm.AST
  ( GTm(..)
  
  , GTermAs(..)
  
  , gtermasFail
  )
  where

import           Data.Char
import           Data.Typeable
import           GHC.Generics
import           Control.Monad.Except

import           UHC.Util.Pretty as PP

-------------------------------------------------------------------------------------------
--- Term language/AST
-------------------------------------------------------------------------------------------

-- | Terms
data GTm
  = GTm_Var     String                  -- ^ variable (to be substituted)
  | GTm_Int     Integer                 -- ^ int value (for arithmetic)
  | GTm_Str     String                  -- ^ string value
  | GTm_Con     String [GTm]            -- ^ general term structure
  deriving (Show, Eq, Ord, Typeable, Generic)

instance PP GTm where
  pp (GTm_Var v        ) = pp v -- "v" >|< v
  pp (GTm_Con c []     ) = pp c
  pp (GTm_Con c@(h:_) [a1,a2])
    | not (isAlpha h)    = ppParens $ a1 >#< c >#< a2
  pp (GTm_Con c as     ) = ppParens $ c >#< ppSpaces as
  pp (GTm_Int i        ) = pp i

-------------------------------------------------------------------------------------------
--- Term interpretation in context of CHR
-------------------------------------------------------------------------------------------

-- | Interpretation monad, which is partial
type GTermAsM = Either PP_Doc

-- | Term interpretation in context of CHR
class GTermAs cnstr guard bprio prio tm
  | cnstr -> guard bprio prio tm
  , guard -> cnstr bprio prio tm
  , bprio -> cnstr guard prio tm
  , prio -> cnstr guard bprio tm
  , tm -> cnstr guard bprio prio
  where
  --
  asTm :: GTm -> GTermAsM tm
  --
  asHeadConstraint :: GTm -> GTermAsM cnstr
  --
  asBodyConstraint :: GTm -> GTermAsM cnstr
  --
  asGuard :: GTm -> GTermAsM guard
  --
  asHeadBacktrackPrio :: GTm -> GTermAsM bprio
  --
  asAltBacktrackPrio :: GTm -> GTermAsM bprio
  --
  asRulePrio :: GTm -> GTermAsM prio

-- | Fail the interpretation
gtermasFail :: GTm -> String -> GTermAsM a
gtermasFail t m = throwError $ "GTerm interpretation failure" >-< indent 2 ("why :" >#< m >-< "term:" >#< t)
