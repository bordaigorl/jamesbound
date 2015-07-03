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

runTypeInference = runJB typeInference ()

typeInference:: JB () ()
typeInference = do
    progs <- readInputProgs
    when (length progs > 1) $ setOpt shouldShowFn
    skipu <- getOpt skipUnsupported
    sequence_ $
        intersperse sepLines $
            [infer source prog | (source, prog, _) <- progs, (not skipu) || isSupported prog  ]

sepLines = info "\n" >> sepLine >> info "\n"

shouldShowFn o@TypeInf{showFileNames = Nothing} = o{showFileNames = Just True}
shouldShowFn o@TypeInf{showFileNames = _} = o

showTVar (NameType n)  = show $ pretty n
showTVar (ArgType n i) = (show $ pretty n) ++ "[" ++ show i ++ "]"
-- namelst p = map pretty $ Set.toList $ allNames p

showArity Nothing = "Any"
showArity (Just i) = show i ++ "-ary"

declareUnsupported = outputLn "UNSUPPORTED"
declareSimplyTyped True = outputLn "SIMPLY TYPED"
declareSimplyTyped False = outputLn "NOT SIMPLY TYPED"
declareTypablyHierarchical True = outputLn "TYPABLY HIERARCHICAL"
declareTypablyHierarchical False = outputLn "NOT TYPABLY HIERARCHICAL"

infer source prog = do
    let p = start prog
    printFn source
    if isSupported prog then do
        onlysimple <- getOpt simple
        if onlysimple
            then simpletype p
            else hierarchical p
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
    infoLn $ show $ prettyPrint term
    info "\n"

printFn fn = do
    flag <- getOpt showFileNames
    case flag of
        Just True -> (outputLn $ "# " ++ fn) >> info "\n"
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



hierarchical p = do
    case inferTypes p of
        ArityMismatch mismatch -> do
            declareSimplyTyped False
            declareInput p
            reportArityMismatch mismatch
        Inconsistent conflicts -> do
            declareTypablyHierarchical False
            declareInput p
            forM_ conflicts $ \ys -> do
                info "    Cycle: "
                forM_ ys $ \y ->
                    info $ (show $ pretty y) ++ " "
                infoLn ""
        result -> do
            declareTypablyHierarchical True
            declareInput p
            infoLn "Typable with base types"
            info "   "
            infoLn $ intercalate " ⤙ " $ map (("t"++).show) $ baseTypes result
            infoLn "and types"
            printTypingEnv (allRestr p) (typing result) (types result)


reportArityMismatch (n1, n2, xs) = do
    info $ "   Wrong arity for names "
    forM_ xs $ \x ->
        info $ (show $ pretty x) ++ " "
    infoLn $ "\n   Expected arity: " ++ show n1
    infoLn $   "     Actual arity: " ++ show n2

printTypingEnv names typing types = do
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

showTypeArg (Just xs) = "[" ++ intercalate ", " (map (\x-> "τ"++show x) xs) ++ "]"
showTypeArg Nothing = ""

printBaseConstr cs = shout $ unlines $ map prcs cs
  where
    prcs (BLt a b) = pp a  ++ " < " ++ pp b
    prcs (BLtOr as bs c) =   "OR ⎡ " ++ pps as  ++ " < " ++ pp c ++
                           "\n   ⎣ " ++ pps bs  ++ " < " ++ pp c

    pp = show . pretty
    pps = show . (map pretty)

isSupported :: PiProg -> Bool
isSupported prog = (null $ defsList $ defs prog) && (not $ hasPCall $ start prog)
  where
    hasPCall (Parall ps) = any hasPCall $ MSet.distinctElems ps
    hasPCall (Alt    as) = any (hasPCall.snd) $ MSet.distinctElems as
    hasPCall (New  _  p) = hasPCall p
    hasPCall (Bang    p) = hasPCall p
    hasPCall (PiCall _ _) = True
    -- hasPCall _ = False