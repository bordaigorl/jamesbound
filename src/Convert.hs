-- | Convert mode
module Convert(convert, runConvert) where

import Frontend hiding (getWriter)
import System.IO
import Language.PiCalc
import Language.PiCalc.Dot

import Data.List
import Data.Set(Set)
import qualified Data.Set as Set

import Control.Monad

runConvert = runJB convert ()

convert :: JB () ()
convert = do
    progs <- readInputProgs
    input  <- getOutputFiles progs
    forM_ input $ \((source, prog, _), writer) ->
        convert1 source prog writer

convert1 :: FilePath -> PiProg -> ((Handle -> IO ()) -> IO ()) -> JB () ()
convert1 source prog writeOut = do
    target  <- getOpt outType
    dostats <- getOpt withStats
    stats'  <- getTermStats $ start prog
    let stats | dostats = ("Source: " ++ source) : stats'
              | otherwise = []
    liftIO $ writeOut $ \h -> do
        hPutStr h $ comment $ stats
        case target of
            Normalised -> hPutStrLn h $ show $ pretty prog
            NormalForm -> hPutStrLn h $ show $ pretty $ nfProg prog -- todo
            Standard   -> hPutStrLn h $ show $ pretty $ stdProg prog
            Restricted -> hPutStrLn h $ show $ pretty $ prog{start=restrNF $ stdNF $ start prog}
            StdPict    -> hPutDot h $ termToDot $ start prog
            JavaScript -> hPutStrLn h $ js prog
            NoOutput   -> return ()


getOutputFiles inputFiles = do
    ext <- getOpt extension
    out <- getOpt outputFile
    case ext of
        Nothing -> do
            writer <- getWriterOrOut' AppendMode out
            return $ zip inputFiles $ repeat $ writer
        Just  e -> do
            when (out /= Nothing) $
                warnLn "Output using extension option, --output option ignored."
            return [(p, withFile (inp ++ "." ++ e) WriteMode) | p@(inp,_,_) <- inputFiles]

-- comment [] = ""
comment xs = unlines $ map ("// "++) $ xs

stdProg prog = progMap (stdToTerm.stdNF) prog
nfProg prog = progMap nf prog

js (PiProg i d) = "(function() {\n" ++ jsnames ++ "\n  return {\n    defs: {\n      " ++ jsdefs ++ "\n    },\n    init: {\n" ++ jsinit ++ "\n    }\n  }\n}());"
  where s = stdToTerm $ stdNF i
        jsnames = unlines $ map (\x-> "  var ch_"++(show $ pretty x)++" = new Channel(\""++(show $ pretty x)++"\");") names
        names = case s of
            (New ns p) -> Set.toList ns
            (Parall p) -> []
        jsdefs = ""
        jsinit = ""
