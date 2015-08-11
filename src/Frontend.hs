{-# LANGUAGE RecordWildCards #-}
-- | Options for the command-line tool
module Frontend(
      module Options
    , JB
    , liftIO
    , liftHL
    , stdin, stdout, stderr
    , parseOptions
    , runJB
    , readInputProg
    , readInputProgs
    , getWriter
    , getWriterOrOut
    , getWriterOrOut'
    , userInput
    , userInputWith
    , output
    , outputLn
    , colorWrap
    , header
    , promptUser
    , promptUserLn
    , info
    , infoLn
    , warn
    , warnLn
    , shout
    , shoutLn
    , debugMsg
    , debugMsgs
    , sepLine
    , fatal
    , getOpts
    , getOpt
    , setOpt
    , when
    , whenOpt
    , unless
    , unlessOpt
    , exitError
    , exitOk
    , getTermStats
    , getStdStats
) where


import qualified System.Console.Haskeline as HL
import System.Console.Haskeline.Completion
import System.Console.Haskeline.MonadException

import Control.Monad (when)
import Control.Monad.State

-- System
import System.IO
import System.Exit
import System.Directory -- (createDirectoryIfMissing, getTemporaryDirectory, doesFileExist, removeFile)
import System.FilePath.Posix ((</>),takeDirectory,takeBaseName,replaceExtension,takeFileName)

import System.Environment (getArgs, withArgs)

-- Utils:
import Version
import Options

import Language.PiCalc

type JB state = StateT state (StateT JBOpt (HL.InputT IO))
-- The main reason why we parametrise on `state` instead of wrapping JB in a
-- state monad only when needed is that we want to hide the lifts needed for the
-- various layers in a convenient API that can be used directly without lifting.
-- Yet we allow each mode to have its dedicated portion of state (accessible
-- through put and get directly).

parseOptions = do
    args <- getArgs
    (if null args then withArgs ["--help"] else id) parseOptions'

parseOptions' = getPun >>= jbModes >>= validateOpt

validateOpt x = return x

liftHL m = lift $ lift $ m -- (just in case we add layers on top)

userInput :: String -> JB st (Maybe String)
userInput prompt = do
    loud <- liftIO $ isLoud
    liftHL $ HL.getInputLine (if loud then prompt else "")

userInputWith :: String -> (String, String) -> JB st (Maybe String)
userInputWith prompt rl = do
    loud <- liftIO $ isLoud
    liftHL $ HL.getInputLineWithInitial (if loud then prompt else "") rl

output :: MonadIO m => String -> m ()
output s   = liftIO $ putStr s
outputLn :: MonadIO m => String -> m ()
outputLn s = liftIO $ putStrLn s

colorWrap c action = do
    whenOpt colored $ output $ "\x1b["++c++"m"
    x <- action
    whenOpt colored $ output "\x1b[0m"
    return x

colorWrapStr c s = do
    color <- getOpt colored
    if color then return ("\x1b["++c++"m" ++ s ++ "\x1b[0m")
             else return s

header = colorWrap "40;1;37"

promptUser :: MonadIO m => String -> m ()
promptUser   = liftIO . putStr
promptUserLn :: MonadIO m => String -> m ()
promptUserLn = liftIO . putStrLn

info s   = liftIO $ whenNormal $ putStr s
infoLn s = liftIO $ whenNormal $ putStrLn s

shout s   = liftIO $ whenLoud $ putStr s
shoutLn s = liftIO $ whenLoud $ putStrLn s

warn s   = do
    s' <- colorWrapStr "33" $ "Warning:\n" ++ unlines (map (" >  "++) s)
    liftIO $ whenLoud $ hPutStr stderr s'
warnLn s = do
    s' <- colorWrapStr "33" s
    liftIO $ whenLoud $ hPutStrLn stderr s'

debugMsg "" = debugMsgs "" []
debugMsg s = debugMsgs s []

debugMsgs s  ss = colorWrap "31" $ liftIO $ do
    putStrLn $ "\n<<<<<<<<<<<   DEBUG "++s++"  >>>>>>>>>>>"
    putStrLn $ unlines $ map ("  "++) $ concatMap lines ss
    putStrLn $ "<<<<<<<<<<<    END "++s++"   >>>>>>>>>>>\n"

fatal msg = colorWrap "41" $ liftIO $ do
    hPutStr stderr "Fatal Error: "
    hPutStrLn stderr msg
    exitError

runJB :: JB state r -> state -> JBOpt -> IO r
runJB action state opt = do
    appDir <- getAppUserDataDirectory programName
    createDirectoryIfMissing False appDir
    let hfile = appDir </> "history"
    let sett = HL.setComplete noCompletion
            HL.defaultSettings{HL.historyFile = Just hfile}
    HL.runInputT sett $ evalStateT (evalStateT action state) opt

getOpts :: JB st JBOpt
getOpts = lift get
getOpt :: (JBOpt -> r) -> JB st r
getOpt f = lift (gets f)
setOpt :: (JBOpt -> JBOpt) -> JB st ()
setOpt f = lift (modify f)

whenOpt :: (JBOpt -> Bool) -> JB st () ->  JB st ()
whenOpt optSel action = do
    b <- getOpt optSel
    when b action

unlessOpt :: (JBOpt -> Bool) -> JB st () ->  JB st ()
unlessOpt optSel action = do
    b <- getOpt optSel
    unless b action


readInputProgs = getOpt inputFiles >>= defToStdin >>= mapM readProgFromFile' >>= alsoFromTerm
defToStdin [] = do
    term <- getOpt inputTerm
    if term == Nothing
        then return ["-"]
        else return []
defToStdin fs = return fs
alsoFromTerm ps = do
    term <- getOpt inputTerm
    case term of
        Nothing -> return ps
        Just str -> do
            prog <- readProgFromString "[option]" str
            return (prog:ps)

readInputProg :: JB state (PiProg, NameId)
readInputProg = getOpt inputFile >>= readProgFromFile

readProgFromFile :: FilePath -> JB state (PiProg, NameId)
readProgFromFile f = do
    (_, prog, n) <- readProgFromFile' f
    return (prog, n)

readProgFromFile' :: FilePath -> JB state (String, PiProg, NameId)
readProgFromFile' "-" = do
    istr <- userInput "Input Term: "
    case istr of
        Just str -> readProgFromString "[stdin]" str
        Nothing -> (warnLn "Warning: no input, exiting.") >> exitOk
readProgFromFile' filename = do
    ok <- liftIO $ doesFileExist filename
    if ok then do
        str <- liftIO $ readFile filename
        readProgFromString filename str
      else fatal $ "File " ++ filename ++ " not found!"

readProgFromString source str =
    case readPiProg source str of
        Right (prog, fstFree, w) -> do
            when (not $ null w) $ warn w
            return (source, prog, fstFree)
        Left e -> fatal $ "Parsing Error in " ++ source ++ " " ++ e

-- | takes an optional filename and returns a function that given a
-- function @f::Handle -> IO r@ will apply it to the handle corresponding to the
-- given file (or stdout)
getWriter :: Maybe String -> JB state ((Handle -> IO ()) -> IO ())
getWriter Nothing = return (\_ -> return ())
getWriter (Just "-") = return ($ stdout)
getWriter (Just out) = return $ withFile out WriteMode

getWriterOrOut :: Maybe String -> JB state ((Handle -> IO r) -> IO r)
getWriterOrOut = getWriterOrOut' WriteMode

getWriterOrOut' :: IOMode -> Maybe String -> JB state ((Handle -> IO r) -> IO r)
getWriterOrOut' _    Nothing    = return ($ stdout)
getWriterOrOut' _    (Just "-") = return ($ stdout)
getWriterOrOut' mode (Just out) = return $ withFile out mode

-- exitCfaTimeout = hPutStrLn stderr "The Analysis timed out!" >> exitWith (ExitFailure 12)
-- exitBfcTimeout = hPutStrLn stderr "Verification timed out!" >> exitWith (ExitFailure 13)
exitError = liftIO $ exitWith $ ExitFailure 1
exitOk:: JB state r
exitOk = liftIO $ exitWith ExitSuccess
-- exitUnsafe = exitWith $ ExitFailure 10

getTermStats t = do
    withStats <- getOpt withStats
    if withStats
        then return [
              " Depth: " ++ (show $ depth $ stdNF t)
            , "Nest-ν: " ++ (show $ nestRestr t)
            , "Nest-|: " ++ (show $ nestPrl t)
            , " Num-|: " ++ (show $ numSeq t)
            ]
        else return []

getStdStats t = do
    withStats <- getOpt withStats
    if withStats
        then return [
              " Depth: " ++ (show $ depth t)
            -- , "Nest-ν: " ++ (show $ nestRestr t)
            -- , "Nest-|: " ++ (show $ nestPrl t)
            -- , " Num-|: " ++ (show $ numSeq t)
            ]
        else return []

sepLine :: JB state ()
sepLine = infoLn "------------------------------"

-- showParseErr :: ParseError -> String -> String
-- showParseErr e s =
--     sherr ++ "\n\t" ++ ln ++ "\n\t" ++ indic
--   where
--     pos = errorPos e
--     ln = (lines s)!!(sourceLine pos - 1)
--     pad = replicate (sourceColumn pos - 1) ' '
--     indic = pad ++ "^"
--     shpos =sourceName pos ++ ":" ++ (show $ sourceLine pos) ++ ":" ++ (show $ sourceColumn pos)
--     sherr = shpos ++ ":" ++ (dropWhile (=='\n') $
--               showErrorMessages "or" "unknown parse error"
--                                 "expecting" "unexpected" "end of input"
--                                (errorMessages e))
