{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances #-}

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

type instance SubstVarKey (StackedVarLookup subst) = SubstVarKey subst
type instance SubstVarVal (StackedVarLookup subst) = SubstVarVal subst

type instance ExtrValVarKey [vv] = ExtrValVarKey vv

class SubstMake subst where
  substSingleton :: SubstVarKey subst -> SubstVarVal subst -> subst
  substEmpty     :: subst

instance {-# OVERLAPPABLE #-}
         ( VarLookupBase subst k v
         , k ~ SubstVarKey subst
         , v ~ SubstVarVal subst
         )
    => SubstMake subst where
  substSingleton     = varlookupSingleton
  {-# INLINE substSingleton #-}
  substEmpty         = varlookupEmpty
  {-# INLINE substEmpty #-}

instance SubstMake subst => SubstMake (StackedVarLookup subst) where
  substSingleton k v = StackedVarLookup [substSingleton k v]
  {-# INLINE substSingleton #-}
  substEmpty         = StackedVarLookup [substEmpty]
  {-# INLINE substEmpty #-}

class VarUpdatable vv subst where
  varUpd            ::  subst -> vv -> vv
  varUpdCyc         ::  subst -> vv -> (vv, VarMp' (SubstVarKey subst) (SubstVarVal subst))
  s `varUpdCyc` x = (s `varUpd` x, emptyVarMp)

class Ord (ExtrValVarKey vv) => VarExtractable vv where -- k | vv -> k where
  varFree           ::  vv -> [ExtrValVarKey vv]
  varFreeSet        ::  vv -> Set.Set (ExtrValVarKey vv)
  
  -- default
  varFree           =   Set.toList . varFreeSet
  varFreeSet        =   Set.fromList . varFree

