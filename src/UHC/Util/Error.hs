{-# LANGUAGE CPP, NoMonomorphismRestriction #-}

-- | Wrapper module around Control.Monad.Error, in order to be backwards compatible as far as UHC is concerned.

module UHC.Util.Error
  (
# if __GLASGOW_HASKELL__ >= 710
    module Control.Monad.Except
  -- , module Control.Monad.Error.Class
  , Error(..)
  , ErrorT
  
  , runErrorT 
  , withErrorT
  , mapErrorT 

  , runError  
  , withError 
  , mapError  
# else
    module Control.Monad.Error
# endif
  )
  where

#if __GLASGOW_HASKELL__ >= 710
import Control.Monad.Except
-- import Control.Monad.Error.Class (Error(..))
#else
import Control.Monad.Error
#endif

#if __GLASGOW_HASKELL__ >= 710
type ErrorT = ExceptT

runErrorT  = runExceptT
withErrorT = withExceptT
mapErrorT  = mapExceptT

runError  = runExcept
withError = withExcept
mapError  = mapExcept

-- | Copied/old/deprecated functionality from Control.Monad.Error.Class
class Error a where
    -- | Creates an exception without a message.
    -- The default implementation is @'strMsg' \"\"@.
    noMsg  :: a
    -- | Creates an exception with a message.
    -- The default implementation of @'strMsg' s@ is 'noMsg'.
    strMsg :: String -> a

    noMsg    = strMsg ""
    strMsg _ = noMsg

#else
#endif
