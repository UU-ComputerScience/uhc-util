{-| Minimal redefine + re-export of a lens package, fclabels currently.
    in addition providing some of the instances for datatypes defined in the remainder of the uhc-util package.
-}

{-# LANGUAGE TypeOperators #-}

module UHC.Util.Lens
  ( 
    (^*)

  , (^.)
  , (^=)
  , (^$=)
  
  , (=.)
  , (=:)
  , (=$:)
  
  , focus
  
  , mkLabel
  )
  where

import           Prelude hiding ((.), id)
import qualified Control.Monad.State as MS
import           Control.Monad.Trans
import           Control.Category

import           Data.Label
import           Data.Label.Monadic((=:), (=.))
import qualified Data.Label.Monadic as M(modify)

-- * Operator interface for composition

infixl 9 ^*
-- | functional getter, which acts like a field accessor
(^*) :: (a :-> b) -> (b :-> c) -> (a :-> c)
f1 ^* f2 = f2 . f1
{-# INLINE (^*) #-}


-- * Operator interface for functional part (occasionally similar to Data.Lens)

infixl 8 ^.
-- | functional getter, which acts like a field accessor
(^.) :: a -> (a :-> b) -> b
a ^. f = get f a
{-# INLINE (^.) #-}

infixr 4 ^=
-- | functional setter, which acts like a field assigner
(^=) :: (a :-> b) -> b -> a -> a
(^=) = set
{-# INLINE (^=) #-}

infixr 4 ^$=
-- | functional modify
(^$=) :: (a :-> b) -> (b -> b) -> a -> a
(^$=) = modify
{-# INLINE (^$=) #-}

-- * Operator interface for monadic part (occasionally similar to Data.Lens)

infixr 4 =$:
-- | monadic modify & set
(=$:) :: MS.MonadState f m => (f :-> o) -> (o -> o) -> m ()
(=$:) = M.modify
{-# INLINE (=$:) #-}

focus :: (MS.MonadState a m, MS.MonadState b m) => (a :-> b) -> m c -> m c
focus f m = do
  a <- MS.get
  (b,c) <- do {MS.put (get f a) ; c <- m ; b <- MS.get ; return (b,c)}
  MS.put $ set f b a
  return c
  
{-
 (Lens f) (StateT g) = StateT $ \a -> case f a of
  StoreT (Identity h) b -> liftM (second h) (g b)
-}
