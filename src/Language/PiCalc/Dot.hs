{-# LANGUAGE OverloadedStrings #-}
module Language.PiCalc.Dot(
      stdToDot
    , stdToDot'
    , stdToDotWith
    , stdToDotWith'
    , termToDot
    , stdDotParam
    , RTEdges(..)
    , rTreeToDot
    , module Data.GraphViz.Commands.IO
) where

import Language.PiCalc.Syntax
import Language.PiCalc.Semantics
import Language.PiCalc.Pretty hiding (style)
import qualified Language.PiCalc.Pretty as P

import Data.Set(Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.MultiSet(MultiSet)
import qualified Data.MultiSet as MSet

-- import Data.Text.Lazy (pack)
import Data.String

import Data.GraphViz as Dot
import Data.GraphViz.Commands.IO
import Data.GraphViz.Attributes.Complete
import Data.GraphViz.Attributes.Colors.X11

termToDot p = stdToDot (stdNF p)

stdToDot = stdToDotWith stdDotParam

stdToDotWith param p@(StdNF stdp) = stdToDotWith' param fstFree p
  where fstFree = 1 + (maximum $ 0:[ setMax ns | (StdFactor _ ns) <- MSet.distinctElems stdp ])

setMax s | Set.null s = 0
         | otherwise  = unique $ Set.findMax s

stdToDot' = stdToDotWith' stdDotParam

stdToDotWith' par i (StdNF stdp) = graphElemsToDot par nodes edges
  where
    nodes = [ (unique n, Left $ show $ pretty n) | (StdFactor _ ns) <- MSet.distinctElems stdp, n <- Set.elems ns ]
        ++ map (\(a,(b,_))->(a,b)) procNodes
    procNodes = zipWith (\a b->(b, a))
            [ (Right $ show $ prettyShort 1 p, Set.elems ns) | (StdFactor p ns) <- MSet.elems stdp ]
            [i, i+1..]
    edges = [(unique n,a,()) | (a, (_, ns)) <- procNodes, n <- ns]
    -- BEWARE: undirected graphs only accept INCREASING edges i.e. (a,b,_) where a <= b
    --         here we are ok because id for seq proc get calculated from first free.

stdDotParam = nonClusteredParams {
        -- globalAttributes = ga,
        isDirected=False,
        fmtNode = fn
    }
    where
        -- ga = [GraphAttrs [RankDir FromLeft ] ]
        fn (n,Left l) = [toLabel l, style filled, shape Ellipse]
        fn (n,Right l) = [toLabel l, style rounded, shape BoxShape]


data RTEdges = SuccEdge PiAction | CovEdge | CongSucc PiAction | CongRel

rTreeToDot fmt (nodes, edg) = graphElemsToDot par nodes edg
  where
    par = nonClusteredParams {isDirected=True, fmtNode = nodeFormat, fmtEdge = edgeFormat }
    nodeFormat (v, st) = [ toLabel $ fmt v st
                           -- toLabel $ show $ stateDepth st
                         , customAttribute ( "contents") $ lblTerm st
                         , customAttribute ( "tooltip") $ fromString $ show v
                         , shape Record
                         -- , shape BoxShape
                         , color $ case stateSucc st of Nothing -> Gray; _ -> Black
                         , style rounded]
    lblTerm st = fromString $ (renderStyle P.style{lineLength=50, mode=OneLineMode} $ pretty $ term $ stateProc st)
                     -- ++ '\n':(show $ term $ stateProc st)
    -- lblTerm st = pack $ show $ term $ stateProc st
    -- lblTerm st = pack $ renderStyle P.style{lineLength=50, mode=OneLineMode} $ pretty $ term $ stateProc st
    -- lblTerm st = pack $ renderStyle P.style{lineLength=50} $ pretty $ term $ stateProc st

    -- nodeFormat (_, st) = [toLabel $ (show $ stateDepth st) ++ "|" ++ (show $ pretty $ term $ stateProc st), Shape MRecord ]
    edgeFormat (_, _, SuccEdge a) = (FontSize 10):(color Black):actionFmt a
    edgeFormat (_, _, CongSucc a) = (FontSize 10):(color Darkkhaki):actionFmt a
    edgeFormat (_, _, CovEdge ) = [style dotted, color DodgerBlue]
    -- edgeFormat (_, _, CongEdge) = [color Crimson]
    edgeFormat (_, _, CongRel) = [color Gray, edgeEnds NoDir]

    actionFmt InitState     = []
    actionFmt (SyncOn x)    = [toLabel $ show $ pretty x, fontColor DarkGreen]
    actionFmt TauAction     = [toLabel tauStr, fontColor Gray30]
    actionFmt (Unfolding p) = [toLabel $ show $ pretty p, fontColor Black]
    tauStr :: String
    tauStr = "τ"
