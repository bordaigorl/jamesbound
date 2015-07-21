-- | The "analyse" mode of jb.
--   Currently it generates the reachability tree.

module Analyse(analyse, runAnalyse) where

import Frontend
import Control.Monad.State

import Language.PiCalc hiding (style)
import Language.PiCalc.Semantics
import Language.PiCalc.Dot

import Data.Map (Map)
import qualified Data.Map as Map

import qualified Language.PiCalc.Pretty as P

import Data.Text.Lazy (pack)

import Data.GraphViz as Dot
import Data.GraphViz.Commands.IO
import Data.GraphViz.Attributes.Complete


{- For reference:
Analyse { inputFile    :: FilePath
        , maxPathLen   :: Maybe Integer
        , maxDepth     :: Maybe Integer
        , reachDotFile :: Maybe FilePath }
-}


data AnalysisState = AS{
      rTree :: ReachTree
    , seenStates :: SeenMap
    } deriving (Show)

--               Term        Repres    Other pred with action
type SeenMap = [(StdNFTerm, Vertex, [(Vertex, PiAction)])]

initState =  AS emptyRTree []

putTree t = modify $ \as -> as{rTree=t}
putSeen s = modify $ \as -> as{seenStates=s}
getTree = gets rTree
getVertState v = gets $ vertState v . rTree
getSeen = gets seenStates


runAnalyse :: JBOpt -> IO ()
runAnalyse = runJB analyse initState

analyse :: JB AnalysisState ()
analyse = do
    (prog, nf) <- readInputProg
    let std = stdNF $ start prog
    putTree $ rTreeFromStd std nf
    red  <- getOpt reduction
    let succs | red >= GroupUnf = optSuccessors
              | otherwise       = successors
    quo  <- getOpt quotienting
    let quotient | quo >= GlobalQuot   = quotSeen
                 | quo >= SiblingsQuot = quotList
                 | otherwise           = const return
    expand (defs prog) succs quotient
    outputDot  <- getOpt reachDotFile >>= getWriterOrOut
    tree <- getTree
    seen <- getSeen
    det  <- getOpt rtDetails
    liftIO $ outputDot $ \h -> hPutDot h $ rTreeToDot (fmtSt det) $ rTreeToGraphElems det tree seen
    -- outputLn $ show t
    return ()

notSeen :: Vertex -> (Vertex, PiState) -> JB AnalysisState Bool
notSeen v (v', p) = do
    seen <- getSeen
    case break cong seen of
        (r1,(s', w, ws):r2) -> do
            putSeen $ (s', w, (v, a):ws):(r1++r2)
            return False
        (_, []) -> do
            putSeen $ (s, v',[]):seen
            return True
  where
    a = origin $ stateProc p
    s = term   $ stateProc p
    cong (t,_,_) = congruentStd s t

quotSeen v = filterM (notSeen v)


-- | explore the reachable terms breadth first.
--   Return whether the search stopped because it explored every state (True)
--   or because it exceeded the bounds on path (False).
expand pdefs succs quotient = bfs [(0,1)]
  where

    bfs [] = return True
    bfs (v:vs) = do
        ws <- getSucc v
        bfs (vs ++ ws)

    getSucc (v, pl) = do
        s <- getVertState v
        exc <- orM (exceeds (stateDepth s) =<< getOpt maxDepth)
                   (exceeds pl =<< getOpt maxPathLen)
        case stateSucc s of
            _ | exc -> return []
            Nothing -> do
                t <- getTree
                succS <- quotient v $ mkChildren t v $ succs pdefs $ stateProc s
                let succV = map fst succS
                let t' = insertChildren t v succS
                putTree t'
                return $ map (\x -> (x, pl+1)) succV
            Just succS -> return $ map (\x -> (x, pl+1)) succS

quotList _ states = return $ quotient [] states
  where
    quotient acc [] = reverse acc
    quotient acc ((v,x):xs)
        | any (congruentStd $ term $ stateProc x) (map (term.stateProc.snd) acc) = quotient acc xs
        | otherwise = quotient ((v, x):acc) xs


orM :: JB s Bool -> JB s Bool -> JB s Bool
orM = liftM2 (||)

exceeds n Nothing  = return False
exceeds n (Just m) = return $ m < n


rTreeToGraphElems det t@(RT m) seen = (nodes, edges)
  where
    nodes = Map.assocs m
    edges = succEdges ++ covEdges ++ congEdges ++ backEdges
    succEdges = [ (v, w, SuccEdge $ action act) |
                    (v, PiState{stateSucc=Just vs}) <- nodes,
                    w <- vs,
                    let act = origin $ stateProc (m Map.! w)
                ]
    covEdges
        | wantCovering =
            [ (v, w, e) | (v, PiState{stateParent=p}) <- nodes
                        , (w,e) <- coveredAncestor (term $ vertProc t v) p ]
        | otherwise = []
    coveredAncestor z Nothing = []
    coveredAncestor z (Just v)
        | (term $ vertProc t v) `coveredBy` z =
            (v,CovEdge):if allCovering then coveredAncestor z $ vertParent t v else []
        --  | otherwise = (v, CongEdge):(coveredAncestor z $ vertParent t v)
        | otherwise = coveredAncestor z $ vertParent t v
    congEdges
        | ShowCongr `elem` det =
            [ (v, w, CongRel) |
                (v, PiState{stateProc=vP}) <- nodes,
                (w, PiState{stateProc=wP}) <- nodes,
                v < w,
                term wP `congruentStd` term vP
            ]
        | otherwise = []
    wantCovering = AllCovering `elem` det || FstCovering `elem` det
    allCovering  = AllCovering `elem` det

    backEdges
        | HideQuot `elem` det = []
        | otherwise = [ (v, w, CongSucc $ action a) | (_, w, vs) <- seen, (v,a) <- vs]
    action | HideUnfLbl `elem` det = \a ->
            case a of
                Unfolding _ -> InitState
                otherwise -> a
           | otherwise = id

fmtSt det v st
    | TermSnippet `elem` det =
        "{" ++ (show $ stateDepth st) ++ "|" ++ lblTerm' 2 st ++ "}"
    | otherwise = show $ stateDepth st
  where
    lblTerm' n st = algn $ case stdToTerm $ term $ stateProc st of
        New _ t -> "ν…" ++ (renderStyle P.style{lineLength=10,ribbonsPerLine=1} $ prettyShort n t)
        t -> renderStyle P.style{lineLength=10,ribbonsPerLine=1} $ prettyShort n t
    algn s = concatMap (++"\\l") $ cutAt 6 $ lines s
    cutAt n s
        | l < n = s
        | otherwise = take n' s ++ "...":drop (l-n') s
        where
            n' = max 1 $ n `div` 2 - 1
            l  = length s
