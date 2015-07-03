{- |
Module      :  Cover
Description :  Cover relation between processes
Maintainer  :  emanuele.dosualdo@cs.ox.ac.uk

This module defines a function @isCovered@ checking if a process is covered by
another.

The implementation consists of an improved version of Ullmann's sub-graph
isomorphism algorithm.

-}
module Language.PiCalc.Semantics.Cover(
    module Language.PiCalc.Semantics.Cover
) where

import Language.PiCalc.Syntax

import Data.Array(bounds)
-- import Data.List (partition, minimumBy)
import Data.Map(Map,(!))
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set
import Data.MultiSet(MultiSet)
import qualified Data.MultiSet as MSet

-- TESTING -----------------------------------
-- import Text.PrettyPrint
import Language.PiCalc.Pretty
import Debug.Trace
----------------------------------------------

import Data.Graph
-- import Data.Array
import Data.Graph.Ullmann
import Language.PiCalc.Semantics.Substitutions
import Language.PiCalc.Syntax.Congruence


coveredBy :: StdNFTerm -> StdNFTerm -> Bool
coveredBy small big = not $ failedMatch $ coverMatches small big

coverMatches:: StdNFTerm -> StdNFTerm -> [Match]
coverMatches small big'
    | isStdZero small = [emptyMatch]
    | isStdZero big'  = noMatch
    | otherwise = subGraphIso semant candidates graphS graphB
  where
    big = renameStd trasl big'
    (graphS, fstSeqS, vert2nodeS, name2vertS) = stdGraph small
    (graphB, fstSeqB, vert2nodeB, name2vertB) = stdGraph big
    lstSeqS = snd $ bounds graphS
    lstSeqB = snd $ bounds graphB

    semant = checkMatch vert2nodeB name2vertB vert2nodeS name2vertS

    candidates = [ candidate i js | i <- Map.elems name2vertS, let js = Map.elems name2vertB]
              ++ [ candidate i js  | i <- [fstSeqS..lstSeqS]
                 , let (Right fS) = vert2nodeS ! i
                 , let js = [ j | j <- [fstSeqB..lstSeqB]
                            , let (Right fB) = vert2nodeB ! j
                            , Set.size (restrNames fS) == Set.size (restrNames fB)
                            ]
                 ]

    trasl x = x{unique=maxNameS + (unique x)}
    maxNameS
        | Map.null name2vertS = 0
        | otherwise = 1 + (unique $ fst $ Map.findMax name2vertS)


stdGraph :: StdNFTerm -> (Graph, Vertex,  Map Vertex (Either PiName StdFactor), Map PiName Vertex)
stdGraph (StdNF s)
    | MSet.null s = (buildG (0,0) [], 0, Map.empty, Map.empty)
    | otherwise   = (buildG (fstIx, lastIx) edgeList, fstSeq, vert2node, name2vert)
  where
    nameNodes = zip [fstIx.. ] [Left  n | n <- Set.toAscList names]
    seqNodes  = zip [fstSeq..] [Right f | f <- seqs]
    name2vert = Map.fromDistinctAscList $ zip (Set.toAscList names) [fstIx..]
    fstSeq = Set.size names
    fstIx = 0
    lastIx = fstSeq + (MSet.size s) -1
    nodes = nameNodes ++ seqNodes

    vert2node = Map.fromDistinctAscList $ nodes

    edgeList = [ (name2vert ! x, j) |
                    (j,Right f) <- seqNodes,
                    x <- Set.elems $ restrNames f ]

    names = Set.unions [restrNames f | f <- MSet.distinctElems s]
    seqs = MSet.elems s


-- Precondition: all names have been matched when trying to match a seq term
checkMatch :: Map Vertex (Either PiName StdFactor)
           -> Map PiName Vertex
           -> Map Vertex (Either PiName StdFactor)
           -> Map PiName Vertex
           -> NodeSemantics
checkMatch v2nodeG name2vG v2nodeP name2vP match w v =
    case (v2nodeP ! w, v2nodeG ! v) of
        (Left   _, Left   _) -> True
        (Right tP, Right tG) -> 
            -- let a = (rename globalise $ seqTerm tG)
            --     b = (rename match2sub $ seqTerm tP)
            --     c = congruent a b
            -- in if c then traceShow a $ traceShow b $ c else c
            congruent (rename globalise $ seqTerm tG) (rename match2sub $ seqTerm tP)
        _ -> error "Name matched with seq!"
  where
    -- globalisation of names is necessary because when comparing seqterms after
    -- applying subs names should be the same name (same unique).
    -- So to make congruence require identification of those names we put the unique in the
    -- static and make the name global.
    -- TODO: find a better way to deal with this.
    globalise x
        | Map.member x name2vG = x{static = show $ unique x, isGlobal=True}
        | otherwise = x
    match2sub x =
        case Map.lookup x name2vP of
            Nothing -> x
            Just  j ->
                case Map.lookup j match of
                    Just  i ->
                        case Map.lookup i v2nodeG of
                            Just (Left  y) -> y{static = show $ unique y, isGlobal=True}
                            Just (Right _) -> error "Name matched with sequential term!"
                            Nothing -> error "Node not in graph!"
                    Nothing -> error "Name not mapped!"


---------------------------------------------------------
-- TESTING
---------------------------------------------------------
-- coverMatches' small big'
--     | isStdZero small = [[]]
--     | isStdZero big'  = []
--     | otherwise = map ((map resolveNodes) . Map.toList) $ subGraphIso semant candidates graphS graphB
--   where
--     big = renameStd trasl big'
--     (graphS, fstSeqS, vert2nodeS, name2vertS) = stdGraph small
--     (graphB, fstSeqB, vert2nodeB, name2vertB) = stdGraph big
--     lstSeqS = snd $ bounds graphS
--     lstSeqB = snd $ bounds graphB

--     semant = checkMatch vert2nodeB name2vertB vert2nodeS name2vertS

--     candidates = [ candidate i js | i <- Map.elems name2vertS, let js = Map.elems name2vertB]
--               ++ [ candidate i js  | i <- [fstSeqS..lstSeqS]
--                  , let (Right fS) = vert2nodeS ! i
--                  , let js = [ j | j <- [fstSeqB..lstSeqB]
--                             , let (Right fB) = vert2nodeB ! j
--                             , Set.size (restrNames fS) == Set.size (restrNames fB)
--                             ]
--                  ]

--     trasl x = x{unique=maxNameS + (unique x)}
--     untrasl (Left x) = Left x{unique=unique x - maxNameS}
--     untrasl x = x

--     maxNameS
--         | Map.null name2vertS = 0
--         | otherwise = 1 + (unique $ fst $ Map.findMax name2vertS)

--     resolveNodes (v, w) = (vert2nodeS Map.! v, untrasl $ vert2nodeB Map.! w)

-- shMatches ms = unlines $ map (unlines.(map shM)) ms
--   where
--     shM (Left x, Left y) = (show x) ++ " --> " ++ (show y)
--     shM (Right x, Right y) = (show $ pretty $ seqTerm x) ++ " --> " ++ (show $ pretty $ seqTerm y)