{-# LANGUAGE UndecidableInstances, FlexibleContexts, FlexibleInstances, TypeSynonymInstances, FunctionalDependencies, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables #-}

-------------------------------------------------------------------------
-- | Combinators for a compile run.
--   20150218: will replace CompileRun, or this one will overwrite CompileRun, in due time
-------------------------------------------------------------------------

module UHC.Util.CompileRun2
  ( CompileRunner

  , CompileRunState(..)
  , CompileRun(..)

  , CompilePhase
  , CompilePhaseT(runCompilePhaseT)
  
  , CompileUnit(..)
  , CompileUnitState(..)
  , CompileRunError(..)
  , CompileModName(..)
  , CompileRunStateInfo(..)

  , CompileParticipation(..)

  , FileLocatable(..)

  , mkEmptyCompileRun

  , crCU, crMbCU
  , ppCR

  , cpUpdStateInfo, cpUpdSI

  , cpUpdCU, cpUpdCUWithKey
  , cpSetFail, cpSetStop, cpSetStopSeq, cpSetStopAllSeq
  , cpSetOk, cpSetErrs, cpSetLimitErrs, cpSetLimitErrsWhen, cpSetInfos, cpSetCompileOrder

  , cpSeq, cpSeqWhen
  , cpEmpty

  , cpFindFileForNameOrFPath
  , cpFindFilesForFPathInLocations, cpFindFilesForFPath, cpFindFileForFPath
  , cpImportGather, cpImportGatherFromMods, cpImportGatherFromModsWithImp
  , cpPP, cpPPMsg

  , forgetM
  )
  where

import           Data.Maybe
import           System.Exit
import           Control.Monad
import           Control.Applicative(Applicative(..))
import           Control.Monad.Error as ME
import           Control.Monad.State
import qualified Control.Exception as CE
import           Control.Monad.Identity
import           System.IO
import qualified Data.Map as Map
import           UHC.Util.Pretty
import           UHC.Util.Utils
import           UHC.Util.FPath


-------------------------------------------------------------------------
-- Utility
-------------------------------------------------------------------------

-- forget result
forgetM :: Monad m => m a -> m ()
forgetM m
  = do { _ <- m
       ; return ()
       }

-------------------------------------------------------------------------
-- The way a CompileUnit can participate
-------------------------------------------------------------------------

data CompileParticipation
  = CompileParticipation_NoImport
  deriving (Eq, Ord)

-------------------------------------------------------------------------
-- Interfacing with actual state info
-------------------------------------------------------------------------

-- | Conversion from string to module name
class CompileModName n where
  mkCMNm      	:: String -> n

-- | State of a compile unit
class CompileUnitState s where
  cusDefault  		:: s
  cusUnk      		:: s
  cusIsUnk      	:: s -> Bool
  cusIsImpKnown		:: s -> Bool

-- | Per compile unit
class CompileUnit u n l s | u -> n l s where
  cuDefault 		:: u
  cuFPath   		:: u -> FPath
  cuUpdFPath    	:: FPath -> u -> u
  cuLocation		:: u -> l
  cuUpdLocation 	:: l -> u -> u
  cuKey     		:: u -> n
  cuUpdKey      	:: n -> u -> u
  cuState   		:: u -> s
  cuUpdState    	:: s -> u -> u
  cuImports     	:: u -> [n]
  cuParticipation 	:: u -> [CompileParticipation]

  -- defaults
  cuParticipation _	=  []

-- | Error reporting
class {- FPathError e => -} CompileRunError e p | e -> p where
  crePPErrL         :: [e] -> PP_Doc
  creMkNotFoundErrL :: p -> String -> [String] -> [FileSuffix] -> [e]
  creAreFatal       :: [e] -> Bool

  -- defaults
  crePPErrL         _       = empty
  creMkNotFoundErrL _ _ _ _ = []
  creAreFatal       _       = True

class CompileRunStateInfo i n p where
  crsiImportPosOfCUKey :: n -> i -> p

-------------------------------------------------------------------------
-- Class alias covering all requirements
-------------------------------------------------------------------------

-- | Class alias for compile functionality
class
  ( CompileModName nm
  , CompileUnitState state
  , CompileUnit unit nm loc state
  , CompileRunError err pos
  , CompileRunStateInfo info nm pos
  , MonadState (CompileRun nm unit info err) m
  -- , MonadError (CompileRunState err) m
  , MonadIO m
  , Monad m
  ) => CompileRunner state nm pos loc unit info err m
  where
    -- | Deal with error
    {-
    cpHandleErr' :: m a -> m a
    cpHandleErr' m = do
        x <- m
        cr <- get
        let modf f = do {modify f ; return x}
        case crState cr of
          CRSFailErrL about es mbLim
            -> do { let (showErrs,omitErrs) = maybe (es,[]) (flip splitAt es) mbLim
                  ; liftIO (unless (null about) (hPutPPLn stderr (pp about)))
                  ; liftIO $ unless (null showErrs) $ 
                           do { hPutPPLn stderr (crePPErrL showErrs)
                              ; unless (null omitErrs) $ hPutStrLn stderr "... and more errors"
                              ; hFlush stderr
                              }
                  ; if creAreFatal es then liftIO exitFailure else modf crSetOk
                  }
          CRSErrInfoL about doPrint is
            -> do { if null is
                    then return x
                    else liftIO (do { hFlush stdout
                                    ; hPutPPLn stderr (about >#< "found errors" >-< e)
                                    ; return x
                                    })
                  ; if not (null is) then liftIO exitFailure else return x
                  }
            where e = empty -- if doPrint then crePPErrL is else empty
          CRSFailMsg msg
            -> do { liftIO $ hPutStrLn stderr msg
                  ; liftIO exitFailure
                  }
          CRSFail
            -> do { liftIO exitFailure
                  }
          CRSStop
            -> do { liftIO $ exitWith ExitSuccess
                  }
          _ -> return x
    -}

-------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------

instance CompileRunError String ()

-------------------------------------------------------------------------
-- Locatable
-------------------------------------------------------------------------

class FileLocatable x loc | loc -> x where		-- funcdep has unlogical direction, but well...
  fileLocation   :: x -> loc
  noFileLocation :: loc

-------------------------------------------------------------------------
-- State
-------------------------------------------------------------------------

data CompileRunState err
  = CRSOk									-- continue
  | CRSFail									-- fail and stop
  | CRSFailMsg String						-- fail with a message and stop
  | CRSStopSeq								-- stop current cpSeq
  | CRSStopAllSeq							-- stop current cpSeq, but also the surrounding ones
  | CRSStop									-- stop completely
  | CRSFailErrL String [err] (Maybe Int)	-- fail with errors and stop
  | CRSErrInfoL String Bool [err]			-- just errors, continue

data CompileRun nm unit info err
  = CompileRun
      { crCUCache       :: Map.Map nm unit
      , crCompileOrder  :: [[nm]]
      , crTopModNm      :: nm
      , crState         :: CompileRunState err
      , crStateInfo     :: info
      }

instance Error (CompileRunState err) where
  noMsg = CRSOk
  strMsg = CRSFailMsg
  
-- instance Monad m => MonadError (CompileRunState err) m 
  
instance Show (CompileRunState err) where
  show CRSOk				= "CRSOk"
  show CRSFail				= "CRSFail"
  show (CRSFailMsg s)		= "CRSFail: " ++ s
  show CRSStopSeq			= "CRSStopSeq"
  show CRSStopAllSeq		= "CRSStopAllSeq"
  show CRSStop				= "CRSStop"
  show (CRSFailErrL _ _ _)	= "CRSFailErrL"
  show (CRSErrInfoL _ _ _)	= "CRSErrInfoL"

mkEmptyCompileRun :: n -> i -> CompileRun n u i e
mkEmptyCompileRun nm info
  = CompileRun
      { crCUCache		= Map.empty
      , crCompileOrder	= []
      , crTopModNm      = nm
      , crState			= CRSOk
      , crStateInfo		= info
      }

-------------------------------------------------------------------------
-- Monad impl (20140804 AD, not (yet?) put into action, too much code still breaks)
-------------------------------------------------------------------------

-- type CompilePhase n u i e a = CompilePhaseT n u i e (StateT (CompileRun n u i e) (ErrorT (CompileRunState e) IO)) a
-- type CompilePhase n u i e a = CompilePhase_S_E_IO n u i e a
-- type CompilePhase n u i e a = StateT (CompileRun n u i e) IO a

{-
type CompilePhase_S_E_T_State n u i e = CompileRun n u i e
type CompilePhase_S_E_T_Error n u i e = CompileRunState e

newtype CompilePhase_S_E_T n u i e m a
  = CompilePhase_S_E_T { runCompilePhase_S_E_T :: StateT (CompilePhase_S_E_T_State n u i e) (ErrorT (CompilePhase_S_E_T_Error n u i e) m) a }

type CompilePhase_S_E_IO n u i e a = CompilePhase_S_E_T n u i e IO a
  -- = CompilePhase_S_E_IO { runCompilePhase_S_E_IO :: StateT (CompilePhase_S_E_IO_State n u i e) (ErrorT (CompilePhase_S_E_IO_Error n u i e) IO) a }
-}

{-
instance CompileRunError e p => Monad (CompilePhase_S_E_T n u i e IO) where
  return x = CompilePhase_S_E_T $ return x -- \cr -> return (x, cr)
  cp >>= f = CompilePhase_S_E_T $ do -- \cr1 -> do
        x <- runCompilePhase_S_E_T cp -- (x,cr2) <- runCompilePhase_S_E_T cp cr1
        let modf f = do {modify f ; return x}
        cr <- get
        case crState cr of
          CRSFailErrL about es mbLim
            -> do { let (showErrs,omitErrs) = maybe (es,[]) (flip splitAt es) mbLim
                  ; liftIO (unless (null about) (hPutPPLn stderr (pp about)))
                  ; liftIO $ unless (null showErrs) $ 
                           do { hPutPPLn stderr (crePPErrL showErrs)
                              ; unless (null omitErrs) $ hPutStrLn stderr "... and more errors"
                              ; hFlush stderr
                              }
                  ; if creAreFatal es then liftIO exitFailure else modf crSetOk
                  }
          CRSErrInfoL about doPrint is
            -> do { if null is
                    then return x
                    else liftIO (do { hFlush stdout
                                    ; hPutPPLn stderr (about >#< "found errors" >-< e)
                                    ; return x
                                    })
                  ; if not (null is) then liftIO exitFailure else return x
                  }
            where e = empty -- if doPrint then crePPErrL is else empty
          CRSFailMsg msg
            -> do { liftIO $ hPutStrLn stderr msg
                  ; liftIO exitFailure
                  }
          CRSFail
            -> do { liftIO exitFailure
                  }
          CRSStop
            -> do { liftIO $ exitWith ExitSuccess
                  }
          _ -> return x
        cr <- get
        case crState cr of
          CRSOk         -> runCompilePhase_S_E_T (f x)
          CRSStopSeq    -> do { modf crSetOk ; ME.throwError CRSStopSeq }
          CRSStopAllSeq -> do { modf crSetStopAllSeq ; ME.throwError CRSStopAllSeq }
          crs           -> ME.throwError crs

instance CompileRunError e p => MonadIO (CompilePhase_S_E_T n u i e IO) where
  liftIO = CompilePhase_S_E_T . liftIO

instance MonadTrans (CompilePhase_S_E_T n u i e) where
  lift = CompilePhase_S_E_T . lift . lift

instance CompileRunError e p => MonadState (CompilePhase_S_E_T_State n u i e) (CompilePhase_S_E_T n u i e IO) where
  get = CompilePhase_S_E_T get
  put = CompilePhase_S_E_T . put

-}

-- | 'CompileRun' as state in specific StateT variant with non standard >>=
-- newtype CompilePhaseT n u i e m a = CompilePhaseT {runCompilePhaseT :: CompileRun n u i e -> m (a, CompileRun n u i e)}
newtype CompilePhaseT n u i e m a
  = CompilePhaseT {runCompilePhaseT :: m a}

type CompilePhase n u i e a = CompilePhaseT n u i e Identity a

instance CompileRunner state n pos loc u i e m => Functor (CompilePhaseT n u i e m) where
    fmap = liftM
 
instance CompileRunner state n pos loc u i e m => Applicative (CompilePhaseT n u i e m) where
    pure  = return
    (<*>) = ap

-- instance CompileRunner state n pos loc u i e m where

instance CompileRunner state n pos loc u i e m => Monad (CompilePhaseT n u i e m) where
  return x = CompilePhaseT $ return x -- \cr -> return (x, cr)
  cp >>= f = CompilePhaseT $ do -- \cr1 -> do
        x <- {- cpHandleErr' $ -} runCompilePhaseT cp -- (x,cr2) <- runCompilePhaseT cp cr1
        let modf f = do {modify f ; return x}
        cr <- get
        case crState cr of
          CRSFailErrL about es mbLim
            -> do { let (showErrs,omitErrs) = maybe (es,[]) (flip splitAt es) mbLim
                  ; liftIO (unless (null about) (hPutPPLn stderr (pp about)))
                  ; liftIO $ unless (null showErrs) $ 
                           do { hPutPPLn stderr (crePPErrL showErrs)
                              ; unless (null omitErrs) $ hPutStrLn stderr "... and more errors"
                              ; hFlush stderr
                              }
                  ; if creAreFatal es then liftIO exitFailure else modf crSetOk
                  }
          CRSErrInfoL about doPrint is
            -> do { if null is
                    then return x
                    else liftIO (do { hFlush stdout
                                    ; hPutPPLn stderr (about >#< "found errors" >-< e)
                                    ; return x
                                    })
                  ; if not (null is) then liftIO exitFailure else return x
                  }
            where e = empty -- if doPrint then crePPErrL is else empty
          CRSFailMsg msg
            -> do { liftIO $ hPutStrLn stderr msg
                  ; liftIO exitFailure
                  }
          CRSFail
            -> do { liftIO exitFailure
                  }
          CRSStop
            -> do { liftIO $ exitWith ExitSuccess
                  }
          _ -> return x
        cr <- get
        case crState cr of
          CRSOk         -> runCompilePhaseT (f x)
          CRSStopSeq    -> do { modf crSetOk ; return $ panic "Monad.CompilePhaseT.CRSStopSeq" }
          CRSStopAllSeq -> do { modf crSetStopAllSeq ; return $ panic "Monad.CompilePhaseT.CRSStopAllSeq" }
          crs           -> return $ panic "Monad.CompilePhaseT._"
{-        
        case crState cr of
          CRSOk         -> runCompilePhaseT (f x)
          CRSStopSeq    -> do { modf crSetOk ; ME.throwError CRSStopSeq }
          CRSStopAllSeq -> do { modf crSetStopAllSeq ; ME.throwError CRSStopAllSeq }
          crs           -> ME.throwError crs
-}

instance MonadTrans (CompilePhaseT n u i e) where
  lift = CompilePhaseT

instance (CompileRunner state n pos loc u i e m, MonadState s m) => MonadState s (CompilePhaseT n u i e m) where
  get = lift get
  put = lift . put

instance (CompileRunner state n pos loc u i e m, MonadIO m) => MonadIO (CompilePhaseT n u i e m) where
  liftIO = lift . liftIO

instance (CompileRunner state n pos loc u i e m, MonadError e' m) => MonadError e' (CompilePhaseT n u i e m) where
  throwError = lift . throwError
  catchError m hdl = lift $ catchError (runCompilePhaseT m) (runCompilePhaseT . hdl)

{-
instance (Show e, MonadIO m) => MonadError e m where
  throwError e = CE.throwIO $ CE.ErrorCall $ show e
  catchError m hdl = CE.catch m hdl
-}

{-
-}

{-
instance MonadError m => MonadError (CompilePhaseT n u i e m) where
  liftIO = CompilePhaseT . liftIO
-}

{-
instance (Monad m, MonadIO m, Monad (CompilePhaseT n u i e m)) => MonadIO (CompilePhaseT n u i e m) where
  liftIO = lift . liftIO
-}

-------------------------------------------------------------------------
-- Pretty printing
-------------------------------------------------------------------------

ppCR :: (PP n,PP u) => CompileRun n u i e -> PP_Doc
ppCR cr
  = "CR" >#< show (crState cr) >|< ":" >#<
      (   (ppBracketsCommasBlock $ map (\(n,u) -> pp n >#< "->" >#< pp u) $ Map.toList $ crCUCache $ cr)
      >-< ppBracketsCommas (map ppBracketsCommas $ crCompileOrder $ cr)
      )

crPP :: (PP n,PP u) => String -> CompileRun n u i e -> IO (CompileRun n u i e)
crPP m cr = do { hPutStrLn stderr (m ++ ":") ; hPutPPLn stderr (ppCR cr) ; hFlush stderr ; return cr }

crPPMsg :: (PP m) => m -> CompileRun n u i e -> IO (CompileRun n u i e)
crPPMsg m cr = do { hPutPPLn stdout (pp m) ; return cr }

cpPP :: (PP n, PP u, CompileRunner s n p l u i e m) => String -> CompilePhaseT n u i e m ()
cpPP m
 = do { liftIO (hPutStrLn stderr (m ++ ":"))
      ; cr <- get
      ; liftIO (hPutPPLn stderr (ppCR cr))
      ; liftIO (hFlush stderr)
      ; return ()
      }

cpPPMsg :: (PP msg, CompileRunner s n p l u i e m) => msg -> CompilePhaseT n u i e m ()
cpPPMsg m
 = do { liftIO (hPutPPLn stdout (pp m))
      ; return ()
      }



-------------------------------------------------------------------------
-- State manipulation, sequencing: compile unit
-------------------------------------------------------------------------

crMbCU :: Ord n => n -> CompileRun n u i e -> Maybe u
crMbCU modNm cr = Map.lookup modNm (crCUCache cr)

crCU :: (Show n,Ord n) => n -> CompileRun n u i e -> u
crCU modNm = panicJust ("crCU: " ++ show modNm) . crMbCU modNm

-------------------------------------------------------------------------
-- State manipulation, sequencing: non monadic
-------------------------------------------------------------------------

crSetOk :: CompileRun n u i e -> CompileRun n u i e
crSetOk cr = cr {crState = CRSOk}

crSetFail :: CompileRun n u i e -> CompileRun n u i e
crSetFail cr = cr {crState = CRSFail}

crSetStop :: CompileRun n u i e -> CompileRun n u i e
crSetStop cr = cr {crState = CRSStop}

crSetStopSeq :: CompileRun n u i e -> CompileRun n u i e
crSetStopSeq cr = cr {crState = CRSStopSeq}

crSetStopAllSeq :: CompileRun n u i e -> CompileRun n u i e
crSetStopAllSeq cr = cr {crState = CRSStopAllSeq}

crSetErrs' :: Maybe Int -> String -> [e] -> CompileRun n u i e -> CompileRun n u i e
crSetErrs' limit about es cr
  = case es of
      [] -> cr
      _  -> cr {crState = CRSFailErrL about es limit}

crSetInfos' :: String -> Bool -> [e] -> CompileRun n u i e -> CompileRun n u i e
crSetInfos' msg dp is cr
  = case is of
      [] -> cr
      _  -> cr {crState = CRSErrInfoL msg dp is}

-------------------------------------------------------------------------
-- Compile unit observations
-------------------------------------------------------------------------

crCUState :: (Ord n,CompileUnit u n l s,CompileUnitState s) => n -> CompileRun n u i e -> s
crCUState modNm cr = maybe cusUnk cuState (crMbCU modNm cr)

crCUFPath :: (Ord n,CompileUnit u n l s) => n -> CompileRun n u i e -> FPath
crCUFPath modNm cr = maybe emptyFPath cuFPath (crMbCU modNm cr)

crCULocation :: (Ord n,FileLocatable u loc) => n -> CompileRun n u i e -> loc
crCULocation modNm cr = maybe noFileLocation fileLocation (crMbCU modNm cr)

-------------------------------------------------------------------------
-- Find file for FPath
-------------------------------------------------------------------------

cpFindFileForNameOrFPath :: (FPATH n) => String -> n -> FPath -> [(String,FPath)]
cpFindFileForNameOrFPath loc _ fp = searchFPathFromLoc loc fp

cpFindFilesForFPathInLocations
  :: ( Ord n
     , FPATH n, FileLocatable u loc, Show loc
     , CompileRunner s n p loc u i e m
     ) => (loc -> n -> FPath -> [(loc,FPath,[e])]) -> ((FPath,loc,[e]) -> res)
          -> Bool -> [(FileSuffix,s)] -> [loc] -> Maybe n -> Maybe FPath -> CompilePhaseT n u i e m [res]
cpFindFilesForFPathInLocations getfp putres stopAtFirst suffs locs mbModNm mbFp
  = do { cr <- get
       ; let cus = maybe cusUnk (flip crCUState cr) mbModNm
       ; if cusIsUnk cus
          then do { let fp = maybe (mkFPath $ panicJust ("cpFindFileForFPath") $ mbModNm) id mbFp
                        modNm = maybe (mkCMNm $ fpathBase $ fp) id mbModNm
                        suffs' = map fst suffs
                  ; fpsFound <- liftIO (searchLocationsForReadableFiles (\l f -> getfp l modNm f)
                                                                        stopAtFirst locs suffs' fp
                                       )
                  ; case fpsFound of
                      []
                        -> do { cpSetErrs (creMkNotFoundErrL (crsiImportPosOfCUKey modNm (crStateInfo cr)) (fpathToStr fp) (map show locs) suffs')
                              ; return []
                              }
                      ((_,_,e@(_:_)):_)
                        -> do { cpSetErrs e
                              ; return []
                              }
                      ffs@((ff,loc,_):_)
                        -> do { cpUpdCU modNm (cuUpdLocation loc . cuUpdFPath ff . cuUpdState cus . cuUpdKey modNm)
                              ; return (map putres ffs)
                              }
                        where cus = case lookup (Just $ fpathSuff ff) suffs of
                                      Just c  -> c
                                      Nothing -> case lookup (Just "*") suffs of
                                                   Just c  -> c
                                                   Nothing -> cusUnk
                  }
          else return (maybe [] (\nm -> [putres (crCUFPath nm cr,crCULocation nm cr,[])]) mbModNm)
       }

cpFindFilesForFPath
  :: forall e n u p i s m .
     ( Ord n
     , FPATH n, FileLocatable u String
     , CompileRunner s n p String u i e m
     ) => Bool -> [(FileSuffix,s)] -> [String] -> Maybe n -> Maybe FPath -> CompilePhaseT n u i e m [FPath]
cpFindFilesForFPath
  = cpFindFilesForFPathInLocations (\l n f -> map (tup12to123 ([]::[e])) $ cpFindFileForNameOrFPath l n f) tup123to1

cpFindFileForFPath
  :: ( Ord n
     , FPATH n, FileLocatable u String
     , CompileRunner s n p String u i e m
     ) => [(FileSuffix,s)] -> [String] -> Maybe n -> Maybe FPath -> CompilePhaseT n u i e m (Maybe FPath)
cpFindFileForFPath suffs sp mbModNm mbFp
  = do { fps <- cpFindFilesForFPath True suffs sp mbModNm mbFp
       ; return (listToMaybe fps)
       }

-------------------------------------------------------------------------
-- Gather all imports
-------------------------------------------------------------------------

-- | recursively extract imported modules, providing a way to import + do the import
cpImportGatherFromModsWithImp
  :: (Show n, Ord n, CompileRunner s n p l u i e m)
     => (u -> [n])														-- get imports
     -> (Maybe prev -> n -> CompilePhaseT n u i e m (x,Maybe prev))		-- extract imports from 1 module
     -> [n]																-- to be imported modules
     -> CompilePhaseT n u i e m ()
cpImportGatherFromModsWithImp getImports imp1Mod modNmL
  = do { cr <- get
       ; cpSeq (   [ one Nothing modNm | modNm <- modNmL ]
                ++ [ cpImportScc ]
               )
       }
  where one prev modNm
          = do { (_,new) <- {- cpHandleErr' $ -} imp1Mod prev modNm
               -- ; cpHandleErr
               ; cr <- get
               ; if CompileParticipation_NoImport `elem` cuParticipation (crCU modNm cr)
                 then cpDelCU modNm
                 else imps new modNm
               }
        imps prev m
          = do { cr <- get
               ; let impL m = [ i | i <- getImports (crCU m cr), not (cusIsImpKnown (crCUState i cr)) ]
               ; cpSeq (map (\n -> one prev n) (impL m))
               }

-- | recursively extract imported modules
cpImportGatherFromMods
  :: (Show n, Ord n, CompileRunner s n p l u i e m)
     => (Maybe prev -> n -> CompilePhaseT n u i e m (x,Maybe prev))		-- extract imports from 1 module
     -> [n]																-- to be imported modules
     -> CompilePhaseT n u i e m ()
cpImportGatherFromMods = cpImportGatherFromModsWithImp cuImports

-- | Abbreviation for cpImportGatherFromMods for 1 module
cpImportGather
  :: (Show n,Ord n,CompileRunner s n p l u i e m)
       => (n -> CompilePhaseT n u i e m ()) -> n -> CompilePhaseT n u i e m ()
cpImportGather imp1Mod modNm
  = cpImportGatherFromMods
      (\_ n -> do { r <- imp1Mod n
                  ; return (r,Nothing)
                  }
      )
      [modNm]

crImportDepL :: (CompileUnit u n l s) => CompileRun n u i e -> [(n,[n])]
crImportDepL = map (\cu -> (cuKey cu,cuImports cu)) . Map.elems . crCUCache

cpImportScc :: (Ord n, CompileRunner s n p l u i e m) => CompilePhaseT n u i e m ()
cpImportScc = modify (\cr -> (cr {crCompileOrder = scc (crImportDepL cr)}))


-------------------------------------------------------------------------
-- State manipulation, state update (Monadic)
-------------------------------------------------------------------------

cpUpdStateInfo, cpUpdSI :: CompileRunner s n p l u i e m => (i -> i) -> CompilePhaseT n u i e m ()
cpUpdStateInfo upd
  = do { cr <- get
       ; put (cr {crStateInfo = upd (crStateInfo cr)})
       }

cpUpdSI = cpUpdStateInfo

-------------------------------------------------------------------------
-- State manipulation, compile unit update (Monadic)
-------------------------------------------------------------------------

cpUpdCUM :: (Ord n, CompileRunner s n p l u i e m) => n -> (u -> IO u) -> CompilePhaseT n u i e m ()
cpUpdCUM modNm upd
  = do { cr <- get
       ; cu <- liftIO (maybe (upd cuDefault) upd (crMbCU modNm cr))
       ; put (cr {crCUCache = Map.insert modNm cu (crCUCache cr)})
       }


cpUpdCUWithKey :: (Ord n, CompileRunner s n p l u i e m) => n -> (n -> u -> (n,u)) -> CompilePhaseT n u i e m n
cpUpdCUWithKey modNm upd
  = do { cr <- get
       ; let (modNm',cu) = (maybe (upd modNm cuDefault) (upd modNm) (crMbCU modNm cr))
       ; put (cr {crCUCache = Map.insert modNm' cu $ Map.delete modNm $ crCUCache cr})
       ; return modNm'
       }

cpUpdCU :: (Ord n, CompileRunner s n p l u i e m) => n -> (u -> u) -> CompilePhaseT n u i e m ()
cpUpdCU modNm upd
  = do { cpUpdCUWithKey modNm (\k u -> (k, upd u))
       ; return ()
       }

-- | delete unit
cpDelCU :: (Ord n,CompileRunner s n p l u i e m) => n -> CompilePhaseT n u i e m ()
cpDelCU modNm
  = do { modify (\cr -> cr {crCUCache = Map.delete modNm $ crCUCache cr})
       }
{-
  = do { cr <- get
       ; let cu = (maybe (upd cuDefault) upd (crMbCU modNm cr))
       ; put (cr {crCUCache = Map.insert modNm cu (crCUCache cr)})
       }
-}
{-
cpUpdCU modNm upd
 = cpUpdCUM modNm (return . upd)
-}

-------------------------------------------------------------------------
-- State manipulation, sequencing (Monadic)
-------------------------------------------------------------------------

cpSetErrs :: CompileRunner s n p l u i e m => [e] -> CompilePhaseT n u i e m ()
cpSetErrs es
 = modify (crSetErrs' Nothing "" es)

cpSetInfos :: CompileRunner s n p l u i e m => String -> Bool -> [e] -> CompilePhaseT n u i e m ()
cpSetInfos msg dp is
 = modify (crSetInfos' msg dp is)

cpSetFail :: CompileRunner s n p l u i e m => CompilePhaseT n u i e m ()
cpSetFail
 = modify crSetFail

cpSetStop :: CompileRunner s n p l u i e m => CompilePhaseT n u i e m ()
cpSetStop
 = modify crSetStop

cpSetStopSeq :: CompileRunner s n p l u i e m => CompilePhaseT n u i e m ()
cpSetStopSeq
 = modify crSetStopSeq

cpSetStopAllSeq :: CompileRunner s n p l u i e m => CompilePhaseT n u i e m ()
cpSetStopAllSeq
 = modify crSetStopAllSeq

cpSetOk :: CompileRunner s n p l u i e m => CompilePhaseT n u i e m ()
cpSetOk
 = modify (\cr -> (cr {crState = CRSOk}))

cpSetCompileOrder :: CompileRunner s n p l u i e m => [[n]] -> CompilePhaseT n u i e m ()
cpSetCompileOrder nameLL
 = modify (\cr -> (cr {crCompileOrder = nameLL}))

cpSetLimitErrs, cpSetLimitErrsWhen :: CompileRunner s n p l u i e m => Int -> String -> [e] -> CompilePhaseT n u i e m ()
cpSetLimitErrs l a e
 = modify (crSetErrs' (Just l) a e)

cpSetLimitErrsWhen l a e
 = do { when (not (null e))
             (cpSetLimitErrs l a e)
      }

cpEmpty :: CompileRunner s n p l u i e m => CompilePhaseT n u i e m ()
cpEmpty = return ()

-- sequence of phases, each may stop the whole sequencing
cpSeq :: CompileRunner s n p l u i e m => [CompilePhaseT n u i e m ()] -> CompilePhaseT n u i e m ()
cpSeq = sequence_
{-
-}
{-
cpSeq []     = return ()
cpSeq (a:as) = do { a
                  ; cpHandleErr
                  ; cr <- get
                  ; case crState cr of
                      CRSOk         -> cpSeq as
                      CRSStopSeq    -> cpSetOk
                      CRSStopAllSeq -> cpSetStopAllSeq
                      _             -> return ()
                  }
-}

-- conditional sequence
cpSeqWhen :: CompileRunner s n p l u i e m => Bool -> [CompilePhaseT n u i e m ()] -> CompilePhaseT n u i e m ()
cpSeqWhen True as = cpSeq as
cpSeqWhen _    _  = return ()

-- handle possible error in sequence
{-
cpHandleErr :: CompileRunError e p => CompilePhase n u i e ()
cpHandleErr
  = do { cr <- get
       ; case crState cr of
           CRSFailErrL about es (Just lim)
             -> do { let (showErrs,omitErrs) = splitAt lim es
                   ; liftIO (unless (null about) (hPutPPLn stderr (pp about)))
                   ; liftIO (putErr' (if null omitErrs then return () else hPutStrLn stderr "... and more errors") showErrs)
                   ; failOrNot es
                   }
           CRSFailErrL about es Nothing
             -> do { liftIO (unless (null about) (hPutPPLn stderr (pp about)))
                   ; liftIO (putErr' (return ()) es)
                   ; failOrNot es
                   }
           CRSErrInfoL about doPrint is
             -> do { if null is
                     then return ()
                     else liftIO (do { hFlush stdout
                                     ; hPutPPLn stderr (about >#< "found errors" >-< e)
                                     })
                   ; if not (null is) then liftIO exitFailure else return ()
                   }
             where e = empty -- if doPrint then crePPErrL is else empty
           CRSFail
             -> do { liftIO exitFailure
                   }
           CRSStop
             -> do { liftIO $ exitWith ExitSuccess
                   }
           _ -> return ()
       }
  where putErr' m e   = if null e
                        then return ()
                        else do { hPutPPLn stderr (crePPErrL e)
                                ; m
                                ; hFlush stderr
                                }
        failOrNot es = if creAreFatal es then liftIO exitFailure else cpSetOk
-}

