-- | The explore mode of jb.
--   It executes the operational semantics of a term, step by step
--   using one of the four strategies: ask the user, leftmost redex, random.
module Explore(explore, runExplore) where

import Frontend
import Language.PiCalc
import Language.PiCalc.Dot

import System.Random(randomRIO)

-- import System.Console.CmdArgs.Default
-- instance Default ExplState where
--     def = ES ()

data ExplState = ES ()

-- TODO: rewrite this using ExplState to store past and current (using a ReachTree?)
initState = ES ()

runExplore = runJB explore initState
help = "HELP:\n\t0   - stop\n\tn>0 - select successor\n\tn<0 - go back n steps\n"

explore:: JB ExplState ()
explore = do
    (prog, nf) <- readInputProg
    strat <- getOpt strategy
    select <- case strat of
        Ask      -> infoLn help >> return askUser
        LeftMost -> return leftmost
        Random   -> return random
    outputDot  <- getOpt strDotFile >>= getWriter
    optUnf <- getOpt optUnfolding
    let getSucc = if optUnf then optSuccessors else successors
    loop outputDot select getSucc (defs prog) [fromProg prog]
    return ()

loop _ _ _ _ [] = return ()
loop outputDot select getSucc pdefs ts@(t:past) = do
    infoLn $ show $ pretty $ term t
    stats <- getStdStats $ term t
    output $ unlines stats
    checkCovering t past
    sepLine
    liftIO $ outputDot $ \h -> hPutDot h $ stdToDot $ term t
    sequence_ [printOpt i x | (x, i) <- zip succProc [1,2..]]
    future <- select ts succProc
    case future of
        Nothing  -> return ()
        Just ts' -> loop outputDot select getSucc pdefs ts'
  where
    succProc = getSucc pdefs t

printOpt i x = do
    promptUser $ " '-"++show i++"--> "
    promptUser $ show $ pretty $ origin x
    info " =>\n\t"
    infoLn $ concise $ stdToTerm $ term x

concise x = renderStyle style{mode=OneLineMode} $ prettyShort 5 x

askUser :: [PiProcess] -> [PiProcess] -> JB ExplState (Maybe [PiProcess])
askUser ts xs = do
    c <- userInput "Choice> "
    case c of
        Nothing -> return Nothing
        Just "d" -> debugMsgs "Dump" [show $ head ts] >> return (Just ts)
        Just n  ->
            case reads n of
                [] -> return Nothing
                (i,_):_ ->
                    case i of
                        0         -> return Nothing
                        i | i > length xs -> return Nothing
                        _ | i > 0 -> return $ Just $ (xs !! (i-1)):ts
                        i | i < -(length ts) -> return Nothing
                        _ | i < 0 -> (infoLn "BACK!")>>(return $ Just $ drop (-i) ts)

leftmost :: [PiProcess] -> [PiProcess] -> JB ExplState (Maybe [PiProcess])
leftmost _  []    = return Nothing
leftmost ts (x:_) = withPause $ return $ Just $ x:ts

random :: [PiProcess] -> [PiProcess] -> JB ExplState (Maybe [PiProcess])
random _  [] = return Nothing
random ts xs = withPause $ do
    i <- liftIO $ randomRIO (0, length xs - 1)
    return $ Just $ (xs !! i):ts

withPause action = do
    nostop <- getOpt nonStop
    if nostop
        then action
        else do
            u <- userInput "Continue?> "
            case u of
                Just s | s `elem` ["","y","Y","yes"] -> action
                _ -> return Nothing
                -- Nothing -> return Nothing


checkCovering t ts = do
    -- withStats <- liftIO $ isNormal
    withStats <- getOpt withStats
    when withStats $ case break (`coveredBy` term t) $ map term ts of
        (_,[])   -> infoLn "## Not covering"
        (_,t':_) -> info "## Covering: " >> (infoLn $ renderStyle style{mode=OneLineMode} $ pretty t')

