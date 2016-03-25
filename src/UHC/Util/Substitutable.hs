{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

module UHC.Util.Substitutable
  (
    VarUpdatable(..)
  , VarExtractable(..)
  
  , SubstMake(..)
  
  , SubstVarKey
  , SubstVarVal
  , ExtrValVarKey
  )
  where

import qualified Data.Set as Set
import           UHC.Util.VarMp

-------------------------------------------------------------------------------------------
--- Substitutable classes
-------------------------------------------------------------------------------------------

infixr 6 `varUpd`
infixr 6 `varUpdCyc`

-- | Invariant: SubstVarKey subst = ExtrValVarKey (SubstVarVal subst)
type family SubstVarKey subst :: *
type family SubstVarVal subst :: *
type family ExtrValVarKey vv :: *

type instance ExtrValVarKey [vv] = ExtrValVarKey vv

class SubstMake subst where
  substSingleton :: SubstVarKey subst -> SubstVarVal subst -> subst
  substEmpty     :: subst

class VarUpdatable vv subst where -- skey sval | subst -> skey sval where
  varUpd            ::  subst -> vv -> vv
  varUpdCyc         ::  subst -> vv -> (vv, VarMp' (SubstVarKey subst) (SubstVarVal subst))
  s `varUpdCyc` x = (s `varUpd` x,emptyVarMp)

class Ord (ExtrValVarKey vv) => VarExtractable vv where -- k | vv -> k where
  varFree           ::  vv -> [ExtrValVarKey vv]
  varFreeSet        ::  vv -> Set.Set (ExtrValVarKey vv)
  
  -- default
  varFree           =   Set.toList . varFreeSet
  varFreeSet        =   Set.fromList . varFree

