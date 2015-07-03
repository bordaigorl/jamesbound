{- |
    Module      :  Ullmann
    Description :  Matching of graphs using Ullmann's algorithm
    Copyright   :  Copyright (C) 2013 Emanuele D'Osualdo
    License     :  CRAPL

    Maintainer  :  emanuele.dosualdo@cs.ox.ac.uk

This module implements graph matching algorithms for /undirected/ graphs.
It is based on the algorithm documented in

* Ullmann, J.R. 1976. /An algorithm for subgraph isomorphism./ Journal of the ACM (JACM). 23, 1 (1976), 31--42.

More sophisticated data structures could be used to keep the state (i.e. using the ST monad)
but we choose a simpler approach.

The core functions can be combined to compute:

 1. sub-graph isomorphism

 2. graph isomorphism

Semantic information can be taken in account by providing functions that
determine whether two nodes are an admissible match.
-}
{-# LANGUAGE RecordWildCards #-}
module Data.Graph.Ullmann(
    -- * Types
      Vertices
    , Match
    , PartialMatch
    , Candidates
    , NodeSemantics
    -- * Matching functions
    , graphMatch
    , graphIso
    , subGraphIso
    , isomorphicTo
    , embeddableIn
    -- * Predefined parameters
    , candidate
    , candidateAny
    , optCandAny
    , noSemantics
    , emptyMatch
    , noMatch
    , failedMatch
    , matchToList
    -- , lookupMatch
) where

import Data.Graph
import Data.Array ((!), bounds)
import Data.List (sortBy)
-- import qualified Data.IntMap as M -- for matches
import qualified Data.Map as M -- for matches
import qualified Data.IntSet as V -- for vertices

-- | A set of vertices
type Vertices = V.IntSet

-- | A map from vertices of the pattern to vertices of the target graph
type Match = M.Map Vertex Vertex
-- type Match = M.IntMap Vertex

-- | A partial match is a match where not every vertex of the pattern has been
-- mapped to a vertex of the graph
type PartialMatch = Match

-- | Candidate matches: @(w, set)@ means that any acceptable match must map @w@ to a vertex in @set@
-- Please note: the list should define a map, so no @w@ should be repeated and
-- all the vertexes of the pattern should be in the list.
type Candidates = [(Vertex, Vertices)]

-- | A function taking a partial match @m@, two vertices @w@ and @v@ to be matched,
-- and returns whether @m ∪ (w,v)@ is an acceptable partial match
type NodeSemantics = PartialMatch -> Vertex -> Vertex -> Bool

{- |
    The main matching function.
    Some notes about its parameters:

    * @(<#)@ is not necessarily asymmetric:
        if set to @(<=)@ the function implements sub-graph isomorphism,
        if set to @(==)@ it computes graph isomorphism;

    * @sem@ checks if mapping a vertex @w@ to @v@ is acceptable wrt the current
        partial match being a user provided function, it can be used to test for
        semantic compatibility of data associated with the vertices;

    * a couple @(w,{v1,...,vn})@ in @cand@ means that @w@ can be
        tentatively matched with any of the @vi@ but no other vertex;
        /please note:/ every vertex @w@ should appear only once in the list.

    * the role of the two graphs @pat@ and @graph@ heavily depends on the choice of @(<#)@.

    A nice feature of the algorithm is that it respects the order of the user
    provided candidates so that if some orders are heuristically more efficient
    the user can impose them. This can be important when the order of the choice
    for matchings matters in the specific application, eg. because the semantic
    compatibility function depends on it.
-}
graphMatch
    :: (Int -> Int -> Bool) -- ^ @(<#)@ a relation between cardinalities
    -> NodeSemantics        -- ^ @sem@ a function checking if mapping a vertex @w@ to @v@ is acceptable
    -> Candidates           -- ^ @cand@ a list representing the possible matches to be considered
    -> Graph                -- ^ @pat@ the graph used as a pattern
    -> Graph                -- ^ @graph@ the graph where a match with @pat@ is searched
    -> [Match]              -- ^ A list of mappings between vertices of @pat@ and @graph@ representing all possible matches.
graphMatch (<#) sem cand' pat' graph'
    | not $ numVert pat' <# numVert graph' = []
    | numVert pat' /= length cand' = []
    | any nonMatchable candidates = []
    | otherwise = match emptyMatch candidates
  where
    compatible = map remUncompat
    remUncompat (w, vs) = (w, V.filter (\v->(degP ! w) <# (degG ! v)) vs)
    candidates = compatible cand'
    nonMatchable (_,vs) = V.null vs

    degG = outdegree graph'
    degP = outdegree pat'

    numVert g = 1 + abs (uncurry (-) $ bounds g)

    pat = fmap V.fromList pat'
    graph = fmap V.fromList graph'

    match m [] = [m]
    match m ((w,vs):cs) =
        concat [match m' cs' |
            v <- V.elems vs,
            sem m w v,
            let cs' = remove v cs,
            let m' = M.insert w v m,
            checkMatch w v m',
            consistent w v cs'
        ]

    remove v = map (\(w, vs)->(w, V.delete v vs))

    checkMatch w v m = all check (M.assocs m)
      where
        check (w', v') =
            V.member w' (pat ! w) `implies` V.member v' (graph ! v)

    consistent w v = all check
      where
        check (w', vs') = (not $ V.null vs')
            && (V.member w' (pat ! w) `implies` (not $ V.null $ V.intersection vs' (graph ! v)))

a `implies` b = (not a) || b


candidateAny :: Graph -> Graph -> Candidates
candidateAny p g = [ (w, V.fromList $ vertices g) | w <- vertices p]

candidate :: Vertex -> [Vertex] -> (Vertex, Vertices)
candidate v vs = (v, V.fromList vs)


-- | the empty node semantics: accepts any matching
noSemantics :: NodeSemantics
noSemantics _ _ _ = True

-- | equivalent to 'graphMatch'  @(==)@
graphIso :: NodeSemantics -> Candidates -> Graph -> Graph -> [Match]
graphIso = graphMatch  (==)

-- | equivalent to @'graphMatch'  (<=)@
subGraphIso :: NodeSemantics -> Candidates -> Graph -> Graph -> [Match]
subGraphIso = graphMatch  (<=)

-- | determines if the two graphs are isomorphic
isomorphicTo :: Graph -> Graph -> Bool
p `isomorphicTo` g = not $ null $ graphIso noSemantics (optCandAny p g) p g

-- | @p \`embeddableIn\` g@ determines if @p@ can be embedded in @g@,
-- i.e. if there is a sub-graph of @g@ isomorphic to @p@
embeddableIn :: Graph -> Graph -> Bool
p `embeddableIn` g = not $ null $ subGraphIso noSemantics (optCandAny p g) p g

-- | Optimised candidates by putting higher-degree nodes in front
optCandAny :: Graph -> Graph -> Candidates
optCandAny p g = sortBy deg (candidateAny p g)
  where
    degP = outdegree p
    deg (a, _) (b, _) = compare (degP ! b) (degP ! a)


emptyMatch :: Match 
emptyMatch = M.empty

noMatch :: [Match]
noMatch = []

failedMatch :: [Match] -> Bool
failedMatch = null

matchToList :: Match -> [(Vertex, Vertex)]
matchToList = M.assocs

-- lookupMatch :: Vertex -> Match -> Vertex
-- lookupMatch w m =
    -- case M.lookup w m of
    --   Nothing -> error ("Match.lookupMatch: vertex " ++ show w ++ " is not an element of the map")
    --   Just x  -> x



-- Testing
eg = buildG (0,2) [(0,1), (0,2), (2,1)]
ep = buildG (0,2) [(0,1), (2,0)]

testsub p g = graphMatch  (<=) (\_ _ _-> True) (candidateAny p g) p g
testiso p g = graphMatch  (==) (\_ _ _-> True) (candidateAny p g) p g

