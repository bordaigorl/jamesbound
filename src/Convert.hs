-- | Convert mode
module Convert(convert, runConvert) where

import Frontend hiding (getWriter)
import System.IO
import Language.PiCalc
import Language.PiCalc.Dot

import Data.Set(Set)
import qualified Data.Set as Set

runConvert = runJB convert ()

convert:: JB () ()
convert = do
    (prog, _) <- readInputProg
    writeOut  <- getOpt outputFile >>= getWriterOrOut
    target    <- getOpt outType
    stats     <- getTermStats $ start prog
    liftIO $ writeOut $ \h -> do
        hPutStr h $ comment stats
        case target of
            Normalised -> hPutStrLn h $ show $ pretty prog
            Standard   -> hPutStrLn h $ show $ pretty $ stdProg prog
            Restricted -> hPutStrLn h $ show $ pretty $ prog{start=restrNF $ stdNF $ start prog}
            StdPict    -> hPutDot h $ termToDot $ start prog
            JavaScript -> hPutStrLn h $ js prog
            NoOutput   -> return ()


-- comment [] = ""
comment xs = unlines $ map ("// "++) $ xs

stdProg prog = progMap (stdToTerm.stdNF) prog

js (PiProg i d) = "(function() {\n" ++ jsnames ++ "\n  return {\n    defs: {\n      " ++ jsdefs ++ "\n    },\n    init: {\n" ++ jsinit ++ "\n    }\n  }\n}());"
  where s = stdToTerm $ stdNF i
        jsnames = unlines $ map (\x-> "  var ch_"++(show $ pretty x)++" = new Channel(\""++(show $ pretty x)++"\");") names
        names = case s of
            (New ns p) -> Set.toList ns
            (Parall p) -> []
        jsdefs = ""
        jsinit = ""
