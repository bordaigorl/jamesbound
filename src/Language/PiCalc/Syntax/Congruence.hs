{- |
    Module      :  Congruence
    Description :  Structural congruence for pi-calculus terms
    Copyright   :  Copyright (C) 2013 Emanuele D'Osualdo
    License     :  CRAPL
    Maintainer  :  emanuele.dosualdo@cs.ox.ac.uk
    Stability   :  experimental

This module implements a procedure for establishing if two terms are
structurally congruent using graph isomorphism between standard normal forms.
-}
{-# LANGUAGE RecordWildCards #-}
module Language.PiCalc.Syntax.Congruence(
    module Language.PiCalc.Syntax.Congruence
    --   congruent
    -- , congruentStd
) where

import Language.PiCalc.Syntax.Term
import Language.PiCalc.Syntax.StdNF

import Data.List (partition)
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set
import Data.MultiSet(MultiSet)
import qualified Data.MultiSet as MSet
import qualified Data.IntSet as V
import qualified Data.IntMap as IM
-- import qualified Data.Map as IM

import Data.Graph
import Data.Array ((!))

import Data.Graph.Ullmann

import Control.Monad.State

-- TESTING ------------------------------------------------------------------
import Text.PrettyPrint hiding (style)
import Language.PiCalc.Pretty hiding (style)
import Data.GraphViz
import Data.GraphViz.Attributes.Complete
import Data.GraphVizEither
import Data.GraphViz.Commands.IO


strToDot a@(_,ng) = graphElemsToDot par n e
  where
    par = nonClusteredParams {isDirected=True, fmtNode = fn }
    fn (n, Right l)
        | isGlobal l = [toLabel $ static l, Shape DoubleCircle]
        | otherwise = [toLabel $ static l, Shape Circle]
    fn (n, Left  l) = [toLabel l, Shape BoxShape]
    (n, e) = getGraphElems id a

getGraphElems f a@(st, NamesGr{..}) = (n, e)
  where
    nameNodes = map (\(x,v)->(f v,Right $ x)) $ Map.assocs nameMap
    lblN (Snd vs) = map (\v-> (f v, Left $ show v)) vs
    lblN (Rcv vs) = map (\v-> (f v, Left $ show v)) vs
    lblN (Call _ vs) = map (\v-> (f v, Left $ show v)) vs
    lblN _ = []
    extrNode (StrNode{..}) = (f vert, Left $ show lbl):(concat $ lblN lbl:map extrNode children)
    extrNode (Zero) = []
    n = (f zeroV, Left "Zero"):nameNodes ++ extrNode st
    e = map (\(a,b)->(f a,f b,())) $ strEdges a ++ edgesToNames

dotCand nmed g1@(_,ng1) g2@(_,ng2) = graphElemsToDot par n e
  where
    (n1,e1) = getGraphElems Left g1
    (n2,e2) = getGraphElems Right g2
    c = strCandidates g1 g2
    n = n1++n2

    namesV1 = Set.fromList $ Map.elems $ nameMap ng1
    namesV2 = Set.fromList $ Map.elems $ nameMap ng2

    e | nmed      = e1++e2++[ (Left v, Right v',()) | (v,vset) <- c, v' <- V.elems vset ] -- shows edges between names
      | otherwise = e1++e2++[ (Left v, Right v',()) | (v,vset) <- c, v' <- V.elems vset, Set.notMember v namesV1, Set.notMember v' namesV2 ]
    -- par = nonClusteredParams {isDirected=True, fmtNode = fn, fmtEdge = fe }
    par = defaultParams {isDirected=True, fmtNode = fn, fmtEdge = fe , clusterBy = cby, clusterID = (Num . Int)  }

    cby x@(Right _,_) = C 1 $ N x
    cby x@(Left _,_)  = C 2 $ N x

    fe (Right _, Right _, ()) = [color Red]
    fe (Left _, Left _, ())   = [color Blue]
    fe (_, _, ())             = [style dotted, edgeEnds NoDir]

    fn :: (Either Vertex Vertex, Either String PiName) -> [Attribute]
    fn (Right _, Right l)
        | isGlobal l      = [toLabel $ static l, color Red, Shape DoubleCircle]
        | otherwise       = [toLabel $ static l, color Red, Shape Circle]
    fn (Right n, Left  l) = [if (l==show n) then toLabel l else toLabel (show n ++ ':':l), color Red, Shape BoxShape]
    fn (Left  _, Right l)
        | isGlobal l      = [toLabel $ static l, color Blue, Shape DoubleCircle]
        | otherwise       = [toLabel $ static l, color Blue, Shape Circle]
    fn (Left  n, Left  l) = [if (l==show n) then toLabel l else toLabel (show n ++ ':':l), color Blue, Shape BoxShape]

test t a b = writeDotFile "jude2.dot" $ dotCand t (structure a) (structure b)

prettyCand c = vcat [int a <> colon <+> sep (punctuate comma $ map int $ V.toList b) | (a,b) <- c]

testProc :: NameId -> PiTerm
testProc 0 = zero
testProc n = alt [ (In  noName{static="x"++show n,unique=2*n  } [], testProc (n-1))
                 , (Out noName{static="y"++show n,unique=1+2*n} [], testProc (n-1)) ]
testProc' :: NameId -> PiTerm
testProc' 0 = zero
testProc' n = alt [ (In  noName{static="x"++show n,unique=1+2*n } [], testProc' (n-1))
                  , (Out noName{static="y"++show n,unique=2*n   } [], testProc' (n-1)) ]
stressNest n = congruent (testProc n) (testProc' n)
stressPrl n = congruent (prl $ replicate n $ testProc 3) (prl $ replicate n $ testProc' 3)
frc n = n `seq` return ()
-----------------------------------------------------------------------------

data StrTree = Zero
             | StrNode {lbl :: StrLabel, vert :: Vertex, children :: [StrTree]}
             deriving (Show)

data StrLabel = Prl | Sum | Snd [Vertex] | Rcv [Vertex] | T | Bng | Call String [Vertex]
    deriving (Show, Eq)

data NamesGr = NamesGr{
      globalNames  :: Set PiName
    , nameMap      :: Map PiName Vertex
    , edgesToNames :: [Edge]
    , maxVertex    :: Vertex
    } deriving (Show)

zeroV :: Vertex
zeroV = 0

strToGraph :: (StrTree, NamesGr) -> Graph
strToGraph a@(st, NamesGr{..}) = buildG (zeroV, maxVertex) $ edgesToNames ++ strEdges a

strEdges (st, NamesGr{..}) = snd $ strBones st
  where
    strBones Zero = (zeroV, [])
    strBones StrNode{..} =(vert, [ (vert,child) | child <- childvs ] ++ lblEdges lbl ++ concat subedges)
      where
        (childvs, subedges)  = unzip $ map strBones children
        lblEdges (Snd vs)    = zip (vert:vs) vs
        lblEdges (Rcv vs)    = zip (vert:vs) vs
        lblEdges (Call _ vs) = zip (vert:vs) vs
        lblEdges _           = []

strCandidates (Zero, _) (Zero, _) = [candidate zeroV [zeroV]]
strCandidates (Zero, _)  _        = []
strCandidates  _        (Zero, _) = []
strCandidates (st1, ng1) (st2, ng2) = (candidate zeroV [zeroV]):(candidate (vert st1) [vert st2]):strCand' st1 st2 ++ nameCand
  where
    nameCand =  globCand ++ locCand
    (gNames1, lNames1) = partition (isGlobal.fst) $ Map.assocs $ nameMap ng1
    (gNames2, lNames2) = partition (isGlobal.fst) $ Map.assocs $ nameMap ng2
    -- Below we rely on the fact that global names have static name unique wrt other global names
    globCand = [ candidate v [w] | (n,v) <- gNames1, (n',w) <- gNames2, static n == static n' ]
    locCand  = map (\(n,v) -> candidate v (map snd lNames2)) lNames1

    -- strCand' st1 st2 = IM.toList $ IM.fromListWith (V.union) $ strCand st1 st2
    strCand' st1 st2 = IM.toList $ strCand  st1 st2

    strCand (StrNode lbl1 vert1 childr1) (StrNode lbl2 vert2 childr2)
        | compat =
                IM.unions
                [ IM.fromList $
                       cand prlV1 prlV2
                    ++ cand sumV1 sumV2
                    ++ cand tV1   tV2
                    ++ cand bngV1 bngV2
                , candPref [(vert a:vs, vert b:vs') | (a,vs) <- sndV1, (b,vs') <- sndV2, length vs == length vs' ]
                , candPref [(vert a:vs, vert b:vs') | (a,vs) <- rcvV1, (b,vs') <- rcvV2, length vs == length vs' ]
                , candPref [(vert a:vs, vert b:vs') | (a,p,vs) <- callV1, (b,p',vs') <- callV2, p==p', length vs == length vs' ]
                , any2map prlV1 prlV2
                , any2map sumV1 sumV2
                , any2map (map fst sndV1) (map fst sndV2)
                , any2map (map fst rcvV1) (map fst rcvV2)
                , any2map tV1 tV2
                , any2map bngV1 bngV2
                , any2map (map fst3 callV1) (map fst3 callV2)
                ]
      where
        any2map xs ys = IM.unionsWith (V.union) [strCand x y | x <- xs, y <- ys]

        cand vs1 vs2 = [candidate (vert v) (map vert vs2) | not (null vs2), v <- vs1]

        candPref = candP IM.empty
        candP m [] = m
        candP m (((vs, vs')):xs) = candP (foldr merge m $ zip vs vs') xs
            where merge (a, b) m' = IM.insertWith (V.union) a (V.singleton b) m'

        c1@(prlV1, sumV1, sndV1, rcvV1, tV1, bngV1, callV1) = classify childr1 empty7
        c2@(prlV2, sumV2, sndV2, rcvV2, tV2, bngV2, callV2) = classify childr2 empty7
        compat = (lengths7 c1) == (lengths7 c1)

        lengths7 (a, b, c, d, e, f, g) = (length a, length b, length c, length d, length e, length f, length g)
        empty7 = ([],[],[],[],[],[],[])
        fst3 (a,_,_) = a

    strCand _ _ = IM.empty -- []

    classify [] acc = acc
    classify (Zero:ns) acc = classify ns acc
    classify (n:ns) (prlV, sumV, sndV, rcvV, tV, bngV, callV) =
        classify ns $ case lbl n of
            Prl -> (n:prlV, sumV, sndV, rcvV, tV, bngV, callV)
            Sum -> (prlV, n:sumV, sndV, rcvV, tV, bngV, callV)
            (Snd vs)     -> (prlV, sumV, (n, vs):sndV, rcvV, tV, bngV, callV)
            (Rcv vs)     -> (prlV, sumV, sndV, (n, vs):rcvV, tV, bngV, callV)
            T   -> (prlV, sumV, sndV, rcvV, n:tV, bngV, callV)
            Bng -> (prlV, sumV, sndV, rcvV, tV, n:bngV, callV)
            (Call pv vs) -> (prlV, sumV, sndV, rcvV, tV, bngV, (n, pv, vs):callV)


structure t = structureStd $ stdNF t
structureStd :: StdNFTerm -> (StrTree, NamesGr)
structureStd (StdNF x) | MSet.null x = (Zero,NamesGr{edgesToNames = [] , globalNames = Set.empty, nameMap = Map.empty , maxVertex = zeroV})
structureStd t' = runState (toTree t) strGr0
  where
    t = stdToTerm $ t'
    -- restrNames = Set.difference (allNames t) (freeNames t)
    nameAssoc = zip (Set.toAscList $ allNames t) [zeroV+1..]
    -- nameAssoc = zip (Set.toAscList restrNames) [zeroV+1..]
    strGr0 = NamesGr{
        edgesToNames = []
      , globalNames = freeNames t
      , nameMap = Map.fromAscList nameAssoc
      , maxVertex = if null nameAssoc then zeroV else snd $ last nameAssoc
      }

-- | Translation of a term to a tree plus name edges.
-- Please Note: the input process is assumed to be normalised.
toTree :: PiTerm -> State NamesGr StrTree
toTree p | isZero p =  return Zero
toTree (Parall ps) = forM (MSet.elems ps) toTree >>= mkNode Prl
toTree (Alt  alts) = forM (MSet.elems alts) preToTree >>= mkNode Sum
toTree (New _   p) = toTree p
toTree (PiCall pvar args) = namesToV args >>= \vs -> mkNode (Call pvar vs) []
toTree (Bang p) = toTree p >>= \c -> mkNode Bng [c]

mkNode lbl children = do
    v <- newVertex
    return $ StrNode lbl v children

preToTree (pre, cont) = do
    child <- toTree cont
    prefToNode pre child

prefToNode Tau child = mkNode T [child]
prefToNode (In  x xs) child = do
    (v:vs) <- namesToV (x:xs)
    return $ StrNode (Snd vs) v [child]
prefToNode (Out x xs) child = do
    (v:vs) <- namesToV (x:xs)
    return $ StrNode (Rcv vs) v [child]

namesToV xs = do
    vs <- mapM (const newVertex) xs
    nm <- gets nameMap
    addEdges $ nameEdges nm vs xs
    return vs

nameEdges _ [] _ = []
nameEdges _ _ [] = []
nameEdges nm (v:vs) (x:xs) =
    case Map.lookup x nm of
        -- Nothing -> nameEdges nm vs xs
        Nothing -> error "non-existing name referenced in term structure"
        Just vx -> (v,vx):nameEdges nm vs xs

newVertex = do
    g <- get
    let newV = maxVertex g + 1
    put g{maxVertex = newV}
    return newV

addEdges e = modify $ \g -> g{edgesToNames = e ++ edgesToNames g}

congruent p1 p2 = congruentStd (stdNF p1) (stdNF p2)

congruentStd p1 p2
    | p1==p2    = True
    | otherwise = not $ null $ graphIso noSemantics cand (strToGraph str1) (strToGraph str2)
  where
    str1 = structureStd p1
    str2 = structureStd p2
    cand = strCandidates str1 str2
