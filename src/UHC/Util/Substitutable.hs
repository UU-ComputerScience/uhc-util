{-# LANGUAGE TypeFamilies, MultiParamTypeClasses, FlexibleContexts, FunctionalDependencies #-}

module UHC.Util.Substitutable
  (
    VarUpdatable(..)
  , VarExtractable(..)
  )
  where

import qualified Data.Set as Set
import           UHC.Util.VarMp

-------------------------------------------------------------------------------------------
--- Substitutable classes
-------------------------------------------------------------------------------------------

infixr 6 `varUpd`
infixr 6 `varUpdCyc`

class VarUpdatable vv subst skey sval | subst -> skey sval where
  -- type VarUpdKey subst :: *
  -- type VarUpdVal subst :: *
  varUpd            ::  subst -> vv -> vv
  varUpdCyc         ::  subst -> vv -> (vv, VarMp' skey sval)
  s `varUpdCyc` x = (s `varUpd` x,emptyVarMp)

class Ord k => VarExtractable vv k | vv -> k where
  varFree           ::  vv -> [k]
  varFreeSet        ::  vv -> Set.Set k
  
  -- default
  varFree           =   Set.toList . varFreeSet
  varFreeSet        =   Set.fromList . varFree

