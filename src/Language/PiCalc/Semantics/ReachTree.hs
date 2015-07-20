{-# LANGUAGE RecordWildCards #-}
{- |
    Module      :  ReachTree
    Description :  Reachability Tree of a PiCalc term
    Copyright   :  Copyright (C) 2013 Emanuele D'Osualdo
    License     :  GPLv2
    Maintainer  :  emanuele.dosualdo@cs.ox.ac.uk

Reachability Tree of a PiCalc term
-}
module Language.PiCalc.Semantics.ReachTree(
      PiState(..)
    , ReachTree(..)
    , Vertex, Graph
    , emptyRTree
    , nextVertex
    , vertState
    , vertProc
    , vertSucc
    , vertParent
    -- , saveSucc
    , mkChildren
    , insertChildren
    , rTreeToGraph
    , rTreeFromStd
    , module Language.PiCalc.Semantics.Process
) where

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Graph

import Language.PiCalc.Syntax.Term
import Language.PiCalc.Syntax.StdNF
import Language.PiCalc.Semantics.Process

data PiState = PiState{
      stateProc  :: PiProcess
    , stateDepth :: Integer
    , stateSucc  :: Maybe [Vertex]
    , stateParent :: Maybe Vertex
    } deriving (Show, Eq)

newtype ReachTree = RT (Map Vertex PiState)
    deriving (Show, Eq)

emptyRTree = RT Map.empty

vertState v (RT m) = m Map.! v

saveSucc :: Vertex -> [Vertex] -> ReachTree -> ReachTree
saveSucc v s (RT m) = RT $
    Map.adjust (\p -> p{stateSucc=Just s}) v m

-- insertChildren v procs t@(RT m) = (vs, RT m')
--   where
--     vs = map fst nodes
--     states = map (mkRTChild v) procs
--     nodes = zip [nextVertex t..] states
--     m' = Map.union
--             (Map.fromDistinctAscList nodes)
--             (Map.adjust (\p -> p{stateSucc=Just vs}) v m)

mkChildren :: ReachTree -> Vertex -> [PiProcess] -> [(Vertex, PiState)]
mkChildren t v procs = nodes
  where
    states = map (mkRTChild v) procs
    nodes = zip [nextVertex t..] states

-- Assumes vertex of children are distinct and sorted in ascending order
insertChildren :: ReachTree -> Vertex -> [(Vertex, PiState)] -> ReachTree
insertChildren t@(RT m) v nodes = RT m'
  where
    vs = map fst nodes
    m' = Map.union
            (Map.fromDistinctAscList nodes)
            (Map.adjust (\p -> p{stateSucc=Just vs}) v m)

mkRTState p =
    PiState { stateProc = p
            , stateDepth = depth $ term p
            , stateSucc = Nothing
            , stateParent = Nothing }

mkRTChild v p = (mkRTState p){stateParent = Just v}

rTreeFromStd :: StdNFTerm -> NameId -> ReachTree
rTreeFromStd t n = RT $ Map.singleton 0 $ mkRTState $ mkProcess t n

nextVertex (RT m)
    | Map.null m = 0
    | otherwise  = 1 + (fst $ Map.findMax m)

rTreeToGraph (RT m) = buildG bnd ed
  where
    bnd | Map.null m = (0,0)
        | otherwise  = (fst $ Map.findMin m, fst $ Map.findMax m)
    ed = [ (v, w) | (v, PiState{stateSucc=Just vs}) <- Map.toList m, w <- vs ]


vertProc :: ReachTree -> Vertex -> PiProcess
vertProc (RT m) v = stateProc $ m Map.! v
vertSucc :: ReachTree -> Vertex -> Maybe [Vertex]
vertSucc (RT m) v = Map.lookup v m >>= stateSucc
vertParent :: ReachTree -> Vertex -> Maybe Vertex
vertParent (RT m) v = Map.lookup v m >>= stateParent
