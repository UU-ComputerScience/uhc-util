{-# LANGUAGE DeriveFunctor, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}

-------------------------------------------------------------------------------------------
-- | Lookups combined into stack of lookups, allowing combined lookup coupled with updates on top of stack only
-------------------------------------------------------------------------------------------

module UHC.Util.Lookup.Stacked
  ( Stacked(..)
  
  , Stacks(..)
  )
  where

-------------------------------------------------------------------------------------------
import           Control.Applicative
import           Control.Arrow
import           Control.Monad.State
import           UHC.Util.Lookup.Types
import           UHC.Util.Lens               as L
import           Prelude                     hiding (lookup, null)
import           Data.Maybe
import qualified Data.List                   as List
import qualified Data.Map                    as Map
import qualified Data.Set                    as Set
import qualified Data.Vector.Unboxed         as UV
import qualified Data.Vector.Unboxed.Mutable as MV
-------------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------------------

-- | Stacked Lookup derived from a base one, to allow a use of multiple lookups but update on top only
newtype Stacks l = Stacks {unStacks :: [l]}
  deriving (Functor, Applicative)

-------------------------------------------------------------------------------------------
-- Lenses
-------------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------------
-- Stacked API
-------------------------------------------------------------------------------------------

-- | Functionality on top of 'Lookup' for awareness of a scope.
-- Minimal definition 'lifts', 'top'/'topM', 'pop'/'popM', 'push'/'pushM'
class Stacked stk elt | stk -> elt where
  -- internal api
  lifts         :: elt -> stk
  
  -- basic api
  top           :: stk -> elt
  pop           :: stk -> (elt,stk)
  push          :: elt -> stk -> stk
  
  -- monadic api
  topM          :: (MonadState stk m) => m elt
  popM          :: (MonadState stk m) => m elt
  pushM         :: (MonadState stk m) => elt -> m ()
  
  -- lifted variations
  tops          :: stk -> stk
  pops          :: stk -> (stk,stk)
  pushs         :: stk -> stk -> stk        -- ^ push, but only top of first arg

  -- lifted monadic variations
  topsM         :: (MonadState stk m) => m stk
  popsM         :: (MonadState stk m) => m stk
  pushsM        :: (MonadState stk m) => stk -> m ()

  -- defaults one way
  tops      = lifts . top
  pops      = first lifts . pop
  pushs     = push . top
  topsM     = gets tops
  popsM     = state pops
  pushsM    = modify . pushs
  
  -- defaults both ways
  topM = gets top
  top  = evalState topM
  
  popM = state pop
  pop  = runState popM

  pushM = modify . push
  push  = execState . pushM

-------------------------------------------------------------------------------------------
-- Default impl
-------------------------------------------------------------------------------------------

instance Stacked (Stacks lkup) lkup where
  lifts e = Stacks [e]
  top = List.head . unStacks
  pop (Stacks (h:t)) = (h, Stacks t)
  push h (Stacks t) = Stacks (h:t)

instance (Lookup lkup k v) => Lookup (Stacks lkup) k v where
  lookup  k  = listToMaybe . catMaybes . map (lookup k) . unStacks
  alter f k  = Stacks . map (alter f k) . unStacks
  null       = all null . unStacks
  toList     = concatMap toList . unStacks
  fromList   = lifts . fromList

  -- for performance reasons
  keysSet = Set.unions . map keysSet . unStacks

-- modifications only for top level, otherwise use <$>
instance LookupApply l1 l2 => LookupApply l1 (Stacks l2) where
  l1 `apply` Stacks (h:t) = Stacks $ apply l1 h : t

