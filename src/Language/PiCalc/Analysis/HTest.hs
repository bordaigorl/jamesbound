module Language.PiCalc.Analysis.HTest where

import Language.PiCalc.Analysis.Hierarchical

import Language.PiCalc

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.List(sort, intercalate)


-- import Language.PiCalc.Pretty

-- import Text.Parsec
-- import Text.Parsec.Char
-- import Text.Parsec.Combinator
-- import Text.Parsec.String

import GHC.Exts( IsString(..) )

import Control.Monad

import Data.Graph

instance Show v => Show (SCC v) where
    show (AcyclicSCC x) = show x
    show (CyclicSCC xs) = "{" ++ intercalate ", " (map show xs) ++ "}"

showTVar (NameType n)  = show $ pretty n
showTVar (ArgType n i) = (show $ pretty n) ++ "[" ++ show i ++ "]"
-- namelst p = map pretty $ Set.toList $ allNames p

showArity Nothing = "Any"
showArity (Just i) = show i ++ "-ary"

prlkg p = map (\(k,l)->(pretty k, pretty l)) $ Map.toList $ linkedToGraph p

testC p =
    case unifyTypes p of
        Left err -> putStrLn $ "Not typable: " ++ show err
        Right c  -> do
            putStrLn "Typable:"
            forM_ c $ \(a, xs) -> do
                putStrLn $ showArity a
                forM_  (Set.toList xs) $ \x -> do
                    putStr "  "
                    putStrLn $ showTVar x


infer p = do
    putStrLn $ show $ pretty p
    case inferTypes p of
        ArityMismatch (n1, n2, xs) -> do
            putStrLn "Untypable:"
            putStr $ "   Wrong arity for names "
            forM_ xs $ \x ->
                putStr $ (show $ pretty x) ++ " "
            putStrLn $ "\n   Expected arity: " ++ show n1
            putStrLn $   "     Actual arity: " ++ show n2
        Inconsistent conflicts -> do
            putStrLn "Untypable:"
            forM_ conflicts $ \ys -> do
                putStr "    Cycle: "
                forM_ ys $ \y ->
                    putStr $ (show $ pretty y) ++ " "
                putStrLn ""
        result -> do
            putStrLn "Typable with base types"
            putStr "   "
            putStrLn $ intercalate " ⤙ " $ map (("t"++).show) $ baseTypes result
            putStrLn "and types"
            let restr = allRestr p
            forM_ (Map.toList $ typing result) $ \(x, b) ->
                when (isGlobal x || x `Set.member` restr) $ do
                    putStr "   "
                    putStr $ show $ pretty x
                    putStr ":τ"
                    putStr $ show b
            putStrLn "\nwhere"
            forM_ (Map.toList $ types result) $ \(b, args) -> do
                putStr "   τ"
                putStr $ show b
                putStr " = t"
                putStr $ show b
                putStrLn $ showTypeArg args


showTypeArg (Just xs) = "[" ++ intercalate ", " (map (\x-> "τ"++show x) xs) ++ "]"
showTypeArg Nothing = ""

term1 :: PiTerm
term1 = fromString "ν(s,c).(*(s(x).(νd.x<d>)) | *(c(m).(s<m> | m(y).c<m>)) | *(τ.(νm.c<m>)))"

term2 :: PiTerm
term2 = fromString "ν(s,n,v,a).(s<a> | *(s(x).(νb.(v<b>.n<x> | s<b>))))"

term3 :: PiTerm
term3 = fromString "*(p(x).(ν(y,z).(x<z> | y<z> | p<y>))) | (νa.p<a>)"


printBaseConstr cs = putStr $ unlines $ map prcs cs
  where
    prcs (BLt a b) = pp a  ++ " < " ++ pp b
    prcs (BLtOr as bs c) =   "OR ⎡ " ++ pps as  ++ " < " ++ pp c ++
                           "\n   ⎣ " ++ pps bs  ++ " < " ++ pp c

    pp = show . pretty
    pps = show . (map pretty)
--     prcs (HLeq k1 k2)     = ppv k1 ++ " ≤ " ++ ppv k2
--     prcs (HGeqMax k1 ks)  = ppv k1 ++ " ≥ " ++ ppvmax ks
--     prcs (HGeqOr a b1 b2) = "OR ⎡ "
--                                 ++ ppv a ++ " ≥ " ++ ppvmax b1 ++ "\n   ⎣ "
--                                 ++ ppv a ++ " ≥ " ++ ppvmax b2
--     prcs (HGt  k1 k2)     = ppv k1 ++ " > " ++ ppv k2
--     prcs (HAllDiff ks)    = "all≠" ++ ppvall ks
--     prcs (HSubType k1 k2) = "τ" ++ ppv k1 ++ " = τ" ++ ppv k2
--     prcs (HTCompat t1 ts) = ppv t1 ++ " compat" ++ ppvall ts

--     ppv (NameType n) = show $ pretty n
--     ppv (ArgType n i) = (show $ pretty n) ++ ":" ++ show i
--     ppvall = concatMap ((' ':).ppv)
--     ppvmax [x] = ppv x
--     ppvmax xs  = "max" ++ ppvall xs

-- debugConstr :: String -> PiTerm -> IO ()
-- debugConstr types p = prntCnstr $ zipWith eval csv csi
--   where
--     csv = constrainTypes p
--     sub = parsetyped p types
--     csi = substConstr sub csv

--     eval cv ci = (cv, checkConstr ci)

--     prntCnstr cs = (putStr $ unlines $ map prcs cs) >> putStr "\x1b[0m"
--       where
--         prcs (HLeq k1 k2, t)     = trp t ++ ppv k1 ++ " ≤ " ++ ppv k2
--         prcs (HGeqMax k1 ks, t)  = trp t ++ ppv k1 ++ " ≥ " ++ ppvmax ks
--         prcs (HGeqOr a b1 b2, t) = trp t ++ "OR  ⎡ "
--                                     ++ ppv a ++ " ≥ " ++ ppvmax b1 ++ "\n         ⎣ "
--                                     ++ ppv a ++ " ≥ " ++ ppvmax b2
--         prcs (HGt  k1 k2, t)     = trp t ++ ppv k1 ++ " > " ++ ppv k2
--         prcs (HAllDiff ks, t)    = trp t ++ "all≠" ++ ppvall ks
--         prcs (HSubType k1 k2, t) = trp t ++ "τ" ++ ppv k1 ++ " = τ" ++ ppv k2
--         prcs (HTCompat t1 ts, t) = trp t ++ ppv t1 ++ " compat" ++ ppvall ts

--         ppv (NameType n) = show $ pretty n
--         ppv (ArgType n i) = (show $ pretty n) ++ ":" ++ (show i)
--         ppvmax [x] = ppv x
--         ppvmax xs  = "max" ++ ppvall xs
--         ppvall = concatMap ((' ':).ppv)

--         trp True  = "  \x1b[92m✔\x1b[0m  "
--         trp False = "  \x1b[91m✘\x1b[0m  "


-- ---- 8< ------------------------------------------------

-- -- parsing of types

-- parseTypes = parse ptypes

-- ptypes = do
--     skipspaces
--     sepEndBy typebind (symbol ";")
--   where
--     typebind = do
--         n <- name <?> "name"
--         symbol ":"
--         t <- typeexp
--         return (n, t)
--     typeexp = do
--         k <- level <?> "level (integer)"
--         ks <- option [] typelist
--         return $ HType k ks
--     typelist = between (symbol "[") (symbol "]") $ do
--         sepBy typeexp (symbol ",")

--     name = do  -- partial reconstruction of real ids
--         h <- many1 lower
--         t <- many (alphaNum <|> char '_')
--         skipspaces
--         return $ h ++ t

--     level :: Parser Level
--     level = do
--         n <- many1 digit
--         return $ read n

--     symbol s = do
--         r <- string s
--         skipspaces
--         return r

--     skipspaces = skipMany space


-- parsetyped p stypes =
--     case parseTypes "<implicit>" stypes of
--         Left e  -> error $ "*** Parsing Error:\n" ++ show e
--         Right tmap ->
--             let nmap = Map.fromList $ [ (name, piname) | name <- map fst tmap, let (piname:_) = Set.toList $ Set.filter (\x-> (show $ pretty x)==name) (allNames p) ]
--             in Map.fromList $ map (\(x,y)->(nmap Map.! x,y)) tmap


-- -----------------------------------------------------------
-- -- * Examples
-- -----------------------------------------------------------

-- -- ν(a0, l1).(*l1?x2.(νy3.(a0!(x2, y3) ‖ l1!y3)))
-- -- Names: [a0,l1,x2,y3]
-- -- Expected: fail
-- exList = "ν(l, a).(*l(x).(νy.(a<x,y> | l<y>)))" :: PiTerm
-- exListTypes = "a0:2[1,0]; l1:3[1]; x2:1; y3:0;"


-- -- ν(c0, s1).((*c0?r2.(νa3.r2!a3.a3?y4.c0!r2))
-- --           ‖ (*s1?r5.(r5?x6.(νok7.x6!ok7) ‖ s1!r5))
-- --           ‖ (*τ.(νr8.(c0!r8 ‖ s1!r8))))
-- -- Names: [c0,s1,r2,a3,y4,r5,x6,ok7,r8]
-- -- Expected: pass
-- exServer = "ν(s,c).((*s(r).(r?x.(νok.x!ok) | s<r>)) | (*c(r).(νa.r!a.a?y.c<r>)) | *(τ.(νr.(c<r> | s<r>))))" :: PiTerm
-- exServerTypes = "c0:0[2[3[4]]]; s1:1[2[3[4]]]; r2:2[3[4]]; r5:2[3[4]]; r8:2[3[4]]; a3:3[4]; x6:3[4]; ok7:4; y4:4;"

-- -- ν(a0, l1, p2).(*l1?x3.p2?y4.(a0!(x3, y4) ‖ l1!y4))
-- -- Names: [a0,l1,p2,x3,y4]
-- -- Expected: pass
-- exL = "ν(l, a, p).(*l(x).(p(y).(a<x,y> | l<y>)))" :: PiTerm
-- exLTypes = "a0:3[1,0]; l1:4[1]; p2:2[0]; x3:1; y4:0;"

-- -- ν(a0, l1, p2).((*l1?x3.p2?y4.(a0!(x3, y4) ‖ l1!y4))
-- --               ‖ (*τ.(νw5.p2!w5)))
-- -- Names: [a0,l1,p2,x3,y4,w5]
-- -- Expected: fail
-- exUp = "ν(l, a, p).(*l(x).(p(y).(a<x,y> | l<y>)) | *(τ.(νw.p<w>)))" :: PiTerm
-- exUpTypes = "a0:5[4,0]; l1:6[4]; p2:1[0]; x3:4; y4:0; w5:0"

-- -- ν(a0, l1, p2, w3).((*l1?x4.p2?y5.(a0!(x4, y5) ‖ l1!y5)) ‖ (*p2!w3))
-- -- Names: [a0,l1,p2,w3,x4,y5]
-- -- Expected: pass
-- exLB = "ν(l, a, p, w).(*l(x).(p(y).(a<x,y> | l<y>)) | *(p<w>))" :: PiTerm
-- exLBTypes = "a0:3[1,0]; l1:4[1]; p2:2[0]; x4:1; y5:0; w3:0"

-- -- Names: [fwd,grow,a0,x3,y4,m5,x6,y7,r8]
-- --exLadder = "νa.(*(νr.a<r>) | grow<a> | *(grow(x).a(y).(fwd<x,y> | grow<y>)) | *(fwd(x,y).x(m).(y<m> | fwd<x,y>)) )" :: PiTerm
-- --exLadderTypes = "fwd:0[3,3]; grow:1; a0:2; x3:3; y4:3; m5:4; x6:3; y7:3; r8:3"