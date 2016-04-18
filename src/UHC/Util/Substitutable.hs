{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances #-}

module UHC.Util.Substitutable
  (
    VarUpdatable(..)
  , VarExtractable(..)
  
{-
  , SubstMake(..)
  
  , SubstVarKey
  , SubstVarVal
-}
  , ExtrValVarKey
  
  , VarTerm(..)
  )
  where

import qualified Data.Set as Set
import           UHC.Util.VarMp

-------------------------------------------------------------------------------------------
--- Substitutable classes
-------------------------------------------------------------------------------------------

infixr 6 `varUpd`
infixr 6 `varUpdCyc`

type family ExtrValVarKey vv :: *

type instance ExtrValVarKey [vv] = ExtrValVarKey vv

class VarUpdatable vv subst where
  varUpd            ::  subst -> vv -> vv
  varUpdCyc         ::  subst -> vv -> (vv, VarMp' (VarLookupKey subst) (VarLookupVal subst))
  s `varUpdCyc` x = (s `varUpd` x, emptyVarMp)

class Ord (ExtrValVarKey vv) => VarExtractable vv where
  varFree           ::  vv -> [ExtrValVarKey vv]
  varFree           =   Set.toList . varFreeSet
  
  varFreeSet        ::  vv -> Set.Set (ExtrValVarKey vv)
  varFreeSet        =   Set.fromList . varFree
  
{-
  -- | Maybe is a key
  varextrMbKey :: vv -> Maybe (ExtrValVarKey vv)
  -- | Construct wrapper for key (i.e. lift, embed)
  varextrMkKey :: ExtrValVarKey vv -> vv
-}

instance {-# OVERLAPPABLE #-} (VarExtractable vv, Ord (ExtrValVarKey vv)) => VarExtractable [vv] where
  varFreeSet        =   Set.unions . map varFreeSet

-- | Term with a (substitutable, extractable, free, etc.) variable
class VarTerm vv where
  -- | Maybe is a key
  varTermMbKey :: vv -> Maybe (ExtrValVarKey vv)
  -- | Construct wrapper for key (i.e. lift, embed)
  varTermMkKey :: ExtrValVarKey vv -> vv
  


