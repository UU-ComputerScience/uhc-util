{-# LANGUAGE RankNTypes #-}

-------------------------------------------------------------------------
-- Wrapper module around pretty printing
-------------------------------------------------------------------------

module UHC.Util.Pretty
  ( -- module UU.Pretty
    -- module UHC.Util.Chitil.Pretty
    module UHC.Util.PrettySimple

  , PP_DocL

  -- * Choice combinators
  , (>-|-<)
  , (>-#-<)
  
  -- * General PP for list
  , ppListSep, ppListSepV, ppListSepVV
  
  -- * Pack PP around
  , ppCurlys
  , ppPacked
  , ppPackedWithStrings
  , ppParens
  , ppCurly
  , ppBrackets
  , ppVBar
  
  -- * Block, horizontal/vertical as required
  , ppBlock, ppBlock'
  , ppBlockWithStrings, ppBlockWithStrings'
  , ppParensCommasBlock
  , ppCurlysBlock
  , ppCurlysSemisBlock
  , ppCurlysCommasBlock
  , ppParensSemisBlock
  , ppBracketsCommasBlock
  , ppBracketsCommasV
  
  -- * Vertical PP of list only
  , ppVertically
  
  -- * Horizontal PP of list only
  , ppCommas, ppCommas'
  , ppSemis, ppSemis'
  , ppSpaces
  , ppCurlysCommas, ppCurlysCommas', ppCurlysCommasWith
  , ppCurlysSemis, ppCurlysSemis'
  , ppParensCommas, ppParensCommas'
  , ppBracketsCommas
  , ppBracketsCommas'
  , ppHorizontally
  , ppListSepFill

  -- * Misc
  , ppDots, ppMb, ppUnless, ppWhen

  -- * IO
  , hPutWidthPPLn, putWidthPPLn
  , hPutPPLn, putPPLn
  , hPutPPFile, putPPFile
  , putPPFPath
  )
  where

-- import UU.Pretty
-- import UHC.Util.Chitil.Pretty
import UHC.Util.PrettySimple
import UHC.Util.FPath
import System.IO
import Data.List

-------------------------------------------------------------------------
-- PP utils for lists
-------------------------------------------------------------------------

type PP_DocL = [PP_Doc]

-- | PP list with open, separator, and close
ppListSep :: (PP s, PP c, PP o, PP a) => o -> c -> s -> [a] -> PP_Doc
ppListSep = ppListSepWith pp -- o >|< hlist (intersperse (pp s) (map pp pps)) >|< c
{-
ppListSep o c s pps
  = o >|< l pps >|< c
  where l []      = empty
        l [p]     = pp p
        l (p:ps)  = pp p >|< map (s >|<) ps
-}

-- | PP list with open, separator, and close, and explicit PP function
ppListSepWith :: (PP s, PP c, PP o) => (a->PP_Doc) -> o -> c -> s -> [a] -> PP_Doc
ppListSepWith ppa o c s pps = o >|< hlist (intersperse (pp s) (map ppa pps)) >|< c

{-# DEPRECATED ppListSepFill "Use ppListSep" #-}
ppListSepFill :: (PP s, PP c, PP o, PP a) => o -> c -> s -> [a] -> PP_Doc
ppListSepFill o c s pps
  = l pps
  where l []      = o >|< c
        l [p]     = o >|< pp p >|< c
        l (p:ps)  = hlist ((o >|< pp p) : map (s >|<) ps) >|< c

ppBlock' :: (PP ocs, PP a) => ocs -> ocs -> ocs -> ocs -> [a] -> [PP_Doc]
ppBlock' osngl _ c _ []                   = [osngl >|< c]
ppBlock' osngl o c _ [a] | isSingleLine x = [osngl >|< x >|< c]
                         | otherwise      = [o >|< x] ++ [pp c]
                         where x = pp a
ppBlock' _     o c s (a:as)               = [o >|< a] ++ map (s >|<) as ++ [pp c]

-- | PP list with open, separator, and close in a possibly multiline block structure
ppBlock :: (PP ocs, PP a) => ocs -> ocs -> ocs -> [a] -> PP_Doc
ppBlock o c s = vlist . ppBlock' o o c s

-- | See 'ppBlock', but with string delimiters aligned properly, yielding a list of elements
ppBlockWithStrings' :: (PP a) => String -> String -> String -> [a] -> [PP_Doc]
ppBlockWithStrings' o c s = ppBlock' o (pad o) c (pad s)
  where l = maximum $ map length [o,s]
        pad s = s ++ replicate (l - length s) ' '

-- | See 'ppBlock', but with string delimiters aligned properly
ppBlockWithStrings :: (PP a) => String -> String -> String -> [a] -> PP_Doc
ppBlockWithStrings o c s = vlist . ppBlockWithStrings' o c s

-- | PP horizontally: list separated by comma
ppCommas :: PP a => [a] -> PP_Doc
ppCommas = ppListSep "" "" ","

-- | PP horizontally: list separated by comma + single blank
ppCommas' :: PP a => [a] -> PP_Doc
ppCommas' = ppListSep "" "" ", "

-- | PP horizontally: list separated by semicolon
ppSemis :: PP a => [a] -> PP_Doc
ppSemis = ppListSep "" "" ";"

-- | PP horizontally: list separated by semicolon + single blank
ppSemis' :: PP a => [a] -> PP_Doc
ppSemis' = ppListSep "" "" "; "

-- | PP horizontally: list separated by single blank
ppSpaces :: PP a => [a] -> PP_Doc
ppSpaces = ppListSep "" "" " "

-- | PP horizontally or vertically with "{", " ", and "}" in a possibly multiline block structure
ppCurlysBlock :: PP a => [a] -> PP_Doc
ppCurlysBlock = ppBlockWithStrings "{" "}" "  "

-- | PP horizontally or vertically with "{", ";", and "}" in a possibly multiline block structure
ppCurlysSemisBlock :: PP a => [a] -> PP_Doc
ppCurlysSemisBlock = ppBlockWithStrings "{" "}" "; "

-- | PP horizontally or vertically with "{", ",", and "}" in a possibly multiline block structure
ppCurlysCommasBlock :: PP a => [a] -> PP_Doc
ppCurlysCommasBlock = ppBlockWithStrings "{" "}" ", "

-- | PP horizontally or vertically with "(", ";", and ")" in a possibly multiline block structure
ppParensSemisBlock :: PP a => [a] -> PP_Doc
ppParensSemisBlock = ppBlockWithStrings "(" ")" "; "

-- | PP horizontally or vertically with "(", ",", and ")" in a possibly multiline block structure
ppParensCommasBlock :: PP a => [a] -> PP_Doc
ppParensCommasBlock = ppBlockWithStrings "(" ")" ", "

-- | PP horizontally or vertically with "[", ",", and "]" in a possibly multiline block structure
ppBracketsCommasV, ppBracketsCommasBlock :: PP a => [a] -> PP_Doc
ppBracketsCommasBlock = ppBlockWithStrings "[" "]" ", "
{-# DEPRECATED ppBracketsCommasV "Use ppBracketsCommasBlock" #-}
ppBracketsCommasV = ppBracketsCommasBlock

-- | PP horizontally with "[", ",", and "]"
ppBracketsCommas :: PP a => [a] -> PP_Doc
ppBracketsCommas = ppListSep "[" "]" ","

-- | PP horizontally with "[", ", ", and "]"
ppBracketsCommas' :: PP a => [a] -> PP_Doc
ppBracketsCommas' = ppListSep "[" "]" ", "

-- | PP horizontally with "(", ",", and ")"
ppParensCommas :: PP a => [a] -> PP_Doc
ppParensCommas = ppListSep "(" ")" ","

-- | PP horizontally with "(", ", ", and ")"
ppParensCommas' :: PP a => [a] -> PP_Doc
ppParensCommas' = ppListSep "(" ")" ", "

-- | PP horizontally with "{", ",", and "}"
ppCurlysCommas :: PP a => [a] -> PP_Doc
ppCurlysCommas = ppListSep "{" "}" ","

ppCurlysCommasWith :: PP a => (a->PP_Doc) -> [a] -> PP_Doc
ppCurlysCommasWith ppa = ppListSepWith ppa "{" "}" ","

-- | PP horizontally with "{", ", ", and "}"
ppCurlysCommas' :: PP a => [a] -> PP_Doc
ppCurlysCommas' = ppListSep "{" "}" ", "

-- | PP horizontally with "{", ";", and "}"
ppCurlysSemis :: PP a => [a] -> PP_Doc
ppCurlysSemis = ppListSep "{" "}" ";"

-- | PP horizontally with "{", "; ", and "}"
ppCurlysSemis' :: PP a => [a] -> PP_Doc
ppCurlysSemis' = ppListSep "{" "}" "; "

{-
ppCommaListV :: PP a => [a] -> PP_Doc
ppCommaListV = ppListSepVV "[" "]" "; "
-}

{-# DEPRECATED ppListSepV', ppListSepV, ppListSepVV "Use pp...Block variants" #-}
ppListSepV' :: (PP s, PP c, PP o, PP a) => (forall x y . (PP x, PP y) => x -> y -> PP_Doc) -> o -> c -> s -> [a] -> PP_Doc
ppListSepV' aside o c s pps
  = l pps
  where l []      = o `aside` c
        l [p]     = o `aside` p `aside` c
        l (p:ps)  = vlist ([o `aside` p] ++ map (s `aside`) (init ps) ++ [s `aside` last ps `aside` c])

-- compact vertical list
{-
ppListSepV3 :: (PP s, PP c, PP o, PP a) => o -> c -> s -> [a] -> PP_Doc
ppListSepV3 o c s pps
  = l pps
  where l []      = o >|< c
        l [p]     = o >|< p >|< c
        l (p:ps)  = vlist ([o >|< p] ++ map (s >|<) (init ps) ++ [s >|< last ps >|< c])
-}

ppListSepV :: (PP s, PP c, PP o, PP a) => o -> c -> s -> [a] -> PP_Doc
ppListSepV = ppListSepV' (>|<)

ppListSepVV :: (PP s, PP c, PP o, PP a) => o -> c -> s -> [a] -> PP_Doc
ppListSepVV = ppListSepV' (>-<)

-- | Alias for 'vlist'
ppVertically :: [PP_Doc] -> PP_Doc
ppVertically = vlist

-- | Alias for 'hlist'
ppHorizontally :: [PP_Doc] -> PP_Doc
ppHorizontally = hlist

-------------------------------------------------------------------------
-- Printing open/close pairs
-------------------------------------------------------------------------

ppPacked :: (PP o, PP c, PP p) => o -> c -> p -> PP_Doc
ppPacked o c pp
  = o >|< pp >|< c

ppPackedWithStrings :: (PP p) => String -> String -> p -> PP_Doc
ppPackedWithStrings o c x = ppBlockWithStrings o c "" [x]

ppParens, ppBrackets, ppCurly, ppCurlys, ppVBar :: PP p => p -> PP_Doc
ppParens   = ppPackedWithStrings "(" ")"
ppBrackets = ppPackedWithStrings "[" "]"
ppCurly    = ppPackedWithStrings "{" "}"
ppCurlys   = ppCurly
ppVBar     = ppPackedWithStrings "|" "|"

-------------------------------------------------------------------------
-- Additional choice combinators, use with care...
-------------------------------------------------------------------------

infixr 2 >-|-<, >-#-<

aside :: (PP a, PP b) => String -> a -> b -> PP_Doc
aside sep l r | isSingleLine l' && isSingleLine r' = l' >|< sep >|< r'
              | otherwise                          = l' >-< r'
  where l' = pp l
        r' = pp r

-- | As (>|<), but doing (>-<) when does not fit on single line
(>-|-<) :: (PP a, PP b) => a -> b -> PP_Doc
(>-|-<) = aside ""

-- | As (>#<), but doing (>-<) when does not fit on single line
(>-#-<) :: (PP a, PP b) => a -> b -> PP_Doc
(>-#-<) = aside " "

-------------------------------------------------------------------------
-- Misc
-------------------------------------------------------------------------

ppDots :: PP a => [a] -> PP_Doc
ppDots = ppListSep "" "" "."

ppMb :: PP a => Maybe a -> PP_Doc
ppMb = maybe empty pp

ppUnless :: Bool -> PP_Doc -> PP_Doc
ppUnless b p = if b then empty else p

ppWhen :: Bool -> PP_Doc -> PP_Doc
ppWhen b p = if b then p else empty

instance PP a => PP (Maybe a) where
  pp = maybe (pp "?") pp

instance PP Bool where
  pp = pp . show

-------------------------------------------------------------------------
-- PP printing to file
-------------------------------------------------------------------------

hPutLn :: Handle -> Int -> PP_Doc -> IO ()
{-
hPutLn h w pp
  = do hPut h pp w
       hPutStrLn h ""
-}
hPutLn h w pp
  = hPutStrLn h (disp pp w "")

hPutWidthPPLn :: Handle -> Int -> PP_Doc -> IO ()
hPutWidthPPLn h w pp = hPutLn h w pp

putWidthPPLn :: Int -> PP_Doc -> IO ()
putWidthPPLn = hPutWidthPPLn stdout

hPutPPLn :: Handle -> PP_Doc -> IO ()
hPutPPLn h = hPutWidthPPLn h 4000

putPPLn :: PP_Doc -> IO ()
putPPLn = hPutPPLn stdout

hPutPPFile :: Handle -> PP_Doc -> Int -> IO ()
hPutPPFile h pp wid
  = hPutLn h wid pp


putPPFPath :: FPath -> PP_Doc -> Int -> IO ()
putPPFPath fp pp wid
  = do { fpathEnsureExists fp
       ; putPPFile (fpathToStr fp) pp wid
       }

putPPFile :: String -> PP_Doc -> Int -> IO ()
putPPFile fn pp wid
  =  do  {  h <- openFile fn WriteMode
         ;  hPutPPFile h pp wid
         ;  hClose h
         }
