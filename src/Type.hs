{-# LANGUAGE RecordWildCards #-}
-- | Type checking mode of jb.
--   It runs type inference to decide if a term is typably hierarchical.
module Type(typeInference, runTypeInference) where

import Frontend
import Language.PiCalc
import Language.PiCalc.Analysis.Hierarchical

import Control.Monad

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.MultiSet as MSet
import Data.List(sort, intercalate, intersperse)

import Language.PiCalc.Pretty(nest)
-- import Text.PrettyPrint(nest, braces, sep, punctuate, comma)

runTypeInference = runJB typeInference ()

typeInference:: JB () ()
typeInference = do
    progs <- readInputProgs
    when (length progs > 1) $ setOpt shouldShowFn
    skipu <- getOpt skipUnsupported
    infer <- selectAlgorithm
    sequence_ $
        intersperse sepLines $
            [apply infer source prog | (source, prog, _) <- progs, (not skipu) || isSupported prog  ]
    disclaimer

disclaimer = do
    shoutLn " .-----------------  << Warning >>  -------------------."
    shoutLn " | The current version of the type system is a variant |"
    shoutLn " | of the one presented in the paper.                  |"
    shoutLn " | It does not fully support global free names and is  |"
    shoutLn " | restricted in the kind of types it can infer for    |"
    shoutLn " | better performance.                                 |"
    shoutLn " '-----------------------------------------------------'\n"

sepLines = info "\n" >> sepLine >> info "\n"

shouldShowFn o@TypeInf{showFileNames = Nothing} = o{showFileNames = Just True}
shouldShowFn o@TypeInf{showFileNames = _} = o

showTVar (NameType n)  = show $ pretty n
showTVar (ArgType n i) = (show $ pretty n) ++ "[" ++ show i ++ "]"
-- namelst p = map pretty $ Set.toList $ allNames p

showArity Nothing = "Any"
showArity (Just i) = show i ++ "-ary"

declareUnsupported = colorWrap "33" $ outputLn "UNSUPPORTED"
declareSimplyTyped True = positiveLn "SIMPLY TYPED"
declareSimplyTyped False = negativeLn "NOT SIMPLY TYPED"
declareTypablyHierarchical True = positiveLn "TYPABLY HIERARCHICAL"
declareTypablyHierarchical False = negativeLn "NOT TYPABLY HIERARCHICAL"

positiveLn x = colorWrap "32" $ outputLn x
negativeLn x = colorWrap "31" $ outputLn x

apply infer source prog = do
    let p = start prog
    printFn source
    if isSupported prog then
        infer p
     else do
        declareUnsupported
        declareInput p
        shoutLn "   Currently definitions and process calls are not supported."
        shoutLn "   Please reformulate the term using replication: *(term)."

declareInput term = do
    useColor <- getOpt colored
    let prettyPrint | useColor  = prettyTerm (colorHoareStyle defTermOpts)
                    | otherwise = pretty
    info "\n"
    infoLn $ show $ nest 4 $ prettyPrint term
    unlessAlgSimple $ do
        shoutLn "\nConstraints:\n"
        shoutBaseConstr term
    info "\n"

selectAlgorithm = do
    alg <- getOpt algorithm
    unless (alg == AlgComplete) $ warnLn $ "Warning: Applying " ++ show alg ++ " algorithm"
    case alg of
        AlgComplete   -> return (hierarchical inferTypes)
        AlgAltCompl   -> return (hierarchical inferTypesSlow)
        AlgIncomplete -> warnIncomplete >> return (hierarchical inferTypesIncomplete)
        AlgSimple     -> return simpletype
  where warnIncomplete = warnLn "Warning: The incomplete type system may reject terms which can be proved hierarchical with the complete algorithm (but has better performance).\n"

unlessAlgSimple m = do
    alg <- getOpt algorithm
    unless (alg == AlgSimple) m

printFn fn = do
    flag <- getOpt showFileNames
    case flag of
        Just True -> header (output $ "\n# " ++ fn) >> output "\n" >> info "\n"
        _         -> return ()

simpletype p =
    case unifyTypes p of
        Left err -> do
            declareSimplyTyped False
            declareInput p
            reportArityMismatch err
        Right eq -> do
            declareSimplyTyped True
            declareInput p
            let (typing, types) = buildTypingEnv eq
            printTypingEnv (allRestr p) typing types



hierarchical infer p = do
    case infer p of
        ArityMismatch mismatch -> do
            declareSimplyTyped False
            declareInput p
            reportArityMismatch mismatch
        Inconsistent {..} -> do
            declareTypablyHierarchical False
            declareInput p
            printTypingEnv (allRestr p) typing types
            forM_ cycles $ \ys -> do
                info "    Cycle: "
                forM_ ys $ \y ->
                    info $ (show $ pretty y) ++ " "
                infoLn ""
        NotTShaped {..} -> do
            declareTypablyHierarchical False
            declareInput p
            printTypingEnv (allRestr p) typing types
            info "    These names have the same type but are always tied to each other: "
            forM_ conflicts $ \y ->
                info $ (show $ pretty y) ++ " "
            infoLn ""
        Inferred {..} -> do
            declareTypablyHierarchical True
            declareInput p
            when (not $ null $ baseTypes) $ do
                infoLn "Typable with base types"
                info "   "
                infoLn $ intercalate " ⤙ " $ map (("t"++).show) baseTypes
                -- infoLn "and types"
                printTypingEnv (allRestr p) typing types
            infoLn $ "Bound on depth: " ++ (show $ length baseTypes)


reportArityMismatch (n1, n2, xs) = do
    info $ "   Wrong arity for names "
    forM_ xs $ \x ->
        info $ (show $ pretty x) ++ " "
    infoLn $ "\n   Expected arity: " ++ show n1
    infoLn $   "     Actual arity: " ++ show n2

printTypingEnv names typing types = do
    infoLn "with types"
    forM_ (Map.toList $ typing) $ \(x, b) ->
        when (isGlobal x || x `Set.member` names) $ do
            info "   "
            info $ show $ pretty x
            info ":τ"
            info $ show b
    infoLn "\nwhere"
    forM_ (Map.toList $ types) $ \(b, args) -> do
        info "   τ"
        info $ show b
        info " = t"
        info $ show b
        infoLn $ showTypeArg args
    infoLn ""

showTypeArg (Just xs) = "[" ++ intercalate ", " (map (\x-> "τ"++show x) xs) ++ "]"
showTypeArg Nothing = ""

shoutBaseConstr p = shout $ unlines $ map prcs $ constrBaseTypes p
  where
    prcs (BLt a b) = "    " ++ pp a  ++ " < " ++ pp b
    prcs (BLtOr as bs c) =   "    OR ⎡ " ++ pps as  ++ " < " ++ pp c ++
                           "\n       ⎣ " ++ pps bs  ++ " < " ++ pp c

    pp = show . pretty
    pps xs = show $ map pretty xs

isSupported :: PiProg -> Bool
isSupported prog = (null $ defsList $ defs prog) && (not $ hasPCall $ start prog)
  where
    hasPCall (Parall  ps) = any hasPCall $ MSet.distinctElems ps
    hasPCall (Alt     as) = any (hasPCall.snd) $ MSet.distinctElems as
    hasPCall (New  _   p) = hasPCall p
    hasPCall (Bang p@(Alt _)) = hasPCall p
    hasPCall (Bang     p) = True
    hasPCall (PiCall _ _) = True
    -- hasPCall _ = False