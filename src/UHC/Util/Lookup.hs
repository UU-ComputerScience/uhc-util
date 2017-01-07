-------------------------------------------------------------------------------------------
-- Abstraction of Map like datatypes providing lookup
-------------------------------------------------------------------------------------------

module UHC.Util.Lookup
  (
  -- * re-export of base
    module UHC.Util.Lookup.Types
  , module UHC.Util.Lookup.Instances
  , module UHC.Util.Lookup.Scoped
  , module UHC.Util.Lookup.Stacked
  
  , lookupResolveVar
  , lookupResolveVal
  , lookupResolveAndContinueM
  )
  where

-------------------------------------------------------------------------------------------
import           Prelude                        hiding (lookup)
import           Control.Applicative
import           UHC.Util.Lookup.Types
import           UHC.Util.Lookup.Instances
import           UHC.Util.Lookup.Scoped         (Scoped)
import           UHC.Util.Lookup.Stacked        (Stacked)
import           UHC.Util.VarLookup             (VarLookupKey, VarLookupVal)
-------------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------------
--- Lookup and resolution
-------------------------------------------------------------------------------------------

-- | Fully resolve lookup
lookupResolveVar :: Lookup m (VarLookupKey m) (VarLookupVal m) => (VarLookupVal m -> Maybe (VarLookupKey m)) -> VarLookupKey m -> m -> Maybe (VarLookupVal m)
lookupResolveVar isVar k m = lookup k m >>= \v -> lookupResolveVal isVar v m <|> return v

-- | Fully resolve lookup
lookupResolveVal :: Lookup m (VarLookupKey m) (VarLookupVal m) => (VarLookupVal m -> Maybe (VarLookupKey m)) -> VarLookupVal m -> m -> Maybe (VarLookupVal m)
lookupResolveVal isVar v m = isVar v >>= \k -> lookupResolveVar isVar k m <|> return v

-- | Monadically lookup a variable, resolve it, continue with either a fail or success monad continuation
lookupResolveAndContinueM :: (Monad m, Lookup s (VarLookupKey s) (VarLookupVal s)) => (VarLookupVal s -> Maybe (VarLookupKey s)) -> (m s) -> (m a) -> (VarLookupVal s -> m a) -> VarLookupKey s -> m a
lookupResolveAndContinueM tmIsVar gets failFind okFind k = gets >>= \s -> maybe failFind okFind $ lookupResolveVar tmIsVar k s

