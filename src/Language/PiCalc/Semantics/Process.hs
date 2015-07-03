{-# LANGUAGE TypeSynonymInstances #-}
module Language.PiCalc.Semantics.Process (
      PiProcess
    , PiAction(..)
    , nextFree
    , term
    , origin
    -- , pdefs
    -- * Conversion
    , mkProcess
    , fromProg
    , fromProgWith
    -- , toProg
    , toTerm
    , toStdNF
    , successors
    , optSuccessors
    , successors'
) where

import Language.PiCalc.Syntax.Term
import Language.PiCalc.Syntax.StdNF

import Language.PiCalc.Semantics.Substitutions

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.MultiSet(MultiSet, distinctElems)
import qualified Data.MultiSet as MSet

-- TODO: Represent Redexes with a dedicated data structure

{- |
    Representation of the states of the execution of a pi-term.
    For better performance it is not just a PiTerm, but a structure
    which gives easier access to the redexes and better support for
    rewriting.
    More efficient structures could be used but our focus is on simplicity.
    This structure's main purpose is hiding details at the moment but could be expanded in the future.
-}
data PiProcess = PiProc{
      nextFree :: NameId
    , term     :: StdNFTerm
    , origin   :: PiAction
    } deriving (Show, Eq)

data PiAction = InitState | SyncOn PiName | TauAction | Unfolding PiTerm
    deriving (Show, Eq, Ord)

mkProcess :: StdNFTerm -> NameId -> PiProcess
mkProcess t free =
    PiProc{ nextFree = free
          , term = t
          , origin = InitState }

fromProg  :: PiProg -> PiProcess
fromProg prog = fromProgWith prog (1 + maxName)
  where
    maxName = maximum $
        (maxNameId $ start prog):
        [ max (maxArg a) (maxNameId p) | (a,p) <- Map.elems (defs prog) ]
    maxArg [] = 0
    maxArg xs = unique $ maximum xs

fromProgWith  :: PiProg -> NameId -> PiProcess
fromProgWith prog freeName =
    PiProc{ nextFree = freeName
          , term = stdNF $ start prog
          , origin = InitState }

-- toProg    :: PiProcess -> PiProg
-- toProg (PiProc{pdefs=d, term=t}) = PiProg{start=stdToTerm t, defs=d}

toTerm    :: PiProcess -> PiTerm
toTerm (PiProc{term=t}) = stdToTerm t

toStdNF   :: PiProcess -> StdNFTerm
toStdNF = term

successors :: PiDefs -> PiProcess -> [PiProcess]
successors pdefs proc@PiProc{term=t, nextFree=next} =
    synchSucc ++ tauSucc ++ unfSucc
  where
    synchSucc = [ proc{term=resTerm, origin=SyncOn x} |
        (x, inR, outR, a@(_,inCont), b@(_,outCont), σ, c) <- matchInRedexes $ pickInputs t,
        let reactum = stdNF $
                New (Set.union (restrNames inR) (restrNames outR))
                $ prl [ applySub σ inCont, outCont ],
        let resTerm = mergeStd c reactum ]
    tauSucc = [ proc{term=resTerm, origin=TauAction} |
        (redex, cont, c) <- pickTauRedex t,
        let resTerm = mergeStd c (stdNF $ New (restrNames redex) cont) ]
    unfSucc = [ proc{term=resTerm, nextFree=free, origin=Unfolding $ seqTerm redex} |
        (redex, cont, free, c) <- pickUnfoldRedex pdefs next t,
        let resTerm = mergeStd c (stdNF $ New (restrNames redex) cont) ]

optSuccessors :: PiDefs -> PiProcess -> [PiProcess]
optSuccessors pdefs proc@PiProc{term=t, nextFree=next} =
    (synchSucc ++ tauSucc) ++ unfSucc
  where
    synchSucc = [ proc{term=resTerm, origin=SyncOn x} |
        (x, inR, outR, a@(_,inCont), b@(_,outCont), σ, c) <- matchInRedexes $ pickInputs t,
        let reactum = stdNF $
                New (Set.union (restrNames inR) (restrNames outR))
                $ prl [ applySub σ inCont, outCont ],
        let resTerm = mergeStd c reactum ]
    tauSucc = [ proc{term=resTerm, origin=TauAction} |
        (redex, cont, c) <- pickTauRedex t,
        let resTerm = mergeStd c (stdNF $ New (restrNames redex) cont) ]
    unfSucc = [ proc{term=resTerm, nextFree=free, origin=Unfolding $ seqTerm redex} |
        (redex, reacta, free, c) <- allUnfoldRedex pdefs next t,
        let resTerm = mergeStd c (stdNF $ New (restrNames redex) $ paralls reacta) ]

successors' :: PiDefs -> PiProcess -> [(PiTerm, PiProcess)]
successors' pdefs proc@PiProc{term=t, nextFree=next} =
    synchSucc ++ tauSucc ++ unfSucc
  where
    synchSucc = [ (prl [alt [a], alt [b]], proc{term=resTerm, origin=SyncOn x}) |
        (x, inR, outR, a@(_,inCont), b@(_,outCont), σ, c) <- matchInRedexes $ pickInputs t,
        let reactum = stdNF $
                New (Set.union (restrNames inR) (restrNames outR))
                $ prl [ applySub σ inCont, outCont ],
        let resTerm = mergeStd c reactum ]
    tauSucc = [ (alt $ [(Tau, cont)], proc{term=resTerm, origin=TauAction}) |
        (redex, cont, c) <- pickTauRedex t,
        let resTerm = mergeStd c (stdNF $ New (restrNames redex) cont) ]
    unfSucc = [ (seqTerm redex, proc{term=resTerm, nextFree=free, origin=Unfolding $ seqTerm redex}) |
        (redex, cont, free, c) <- pickUnfoldRedex pdefs next t,
        let resTerm = mergeStd c (stdNF $ New (restrNames redex) cont) ]

matchInRedexes
    :: [(PiName, StdFactor, PiPrefTerm, StdNFTerm)]
    -> [(PiName, StdFactor, StdFactor, PiPrefTerm, PiPrefTerm, NameSubst, StdNFTerm)]
matchInRedexes potential =
    [ (x, inR, outR, inPick, outPick, σ, StdNF context) |
        (x, inR, inPick, StdNF rest) <- potential,
        outR@(StdFactor
            {seqTerm=Alt alts}) <- distinctElems rest,
        outPick@(Out _ _, _) <- distinctElems alts,
        σ <- match inPick outPick,
        let context = MSet.delete outR rest
    ]

pickInputs :: StdNFTerm -> [(PiName, StdFactor, PiPrefTerm, StdNFTerm)]
pickInputs (StdNF ps) =
    [ (x, inRedex, pick, StdNF context) |
        inRedex@(StdFactor
            {seqTerm=Alt alts}) <- distinctElems ps,
        pick@(In x _, _)   <- distinctElems alts,
        let context = MSet.delete inRedex ps
    ]


pickTauRedex :: StdNFTerm -> [(StdFactor, PiTerm, StdNFTerm)]
pickTauRedex (StdNF ps) =
    [ (redex, cont, StdNF context) |
        redex@(StdFactor
            {seqTerm=Alt alts}) <- distinctElems ps,
        (Tau, cont)  <- distinctElems alts,
        let context = MSet.delete redex ps
    ]

-- maybe keep subst separate as in InOutRed? Whould help when thinking in terms of derivatives
pickUnfoldRedex :: PiDefs -> NameId -> StdNFTerm -> [(StdFactor, PiTerm, NameId, StdNFTerm)]
pickUnfoldRedex pdefs nextFree (StdNF ps) =
    [ (redex, reactum, max free nextFree, StdNF context) |
        redex <- distinctElems ps,
        (reactum, free) <- getUnfolded pdefs nextFree $ seqTerm redex,
        let context = MSet.delete redex ps
    ]

allUnfoldRedex :: Monad m => PiDefs -> NameId -> StdNFTerm -> m (StdFactor, [PiTerm], NameId, StdNFTerm)
allUnfoldRedex pdefs nextFree (StdNF ps) = optUnf ([], Set.empty, [], nextFree, ps) $ MSet.distinctElems ps -- altern: elems => eager
  where
    optUnf ([], _, _, _, _) [] = fail "No unfoldable redex"
    optUnf (redexes, fnames, reacta, nextfr, context) [] = return (StdFactor {seqTerm=paralls redexes, restrNames=fnames}, reacta, nextfr, StdNF context)
    optUnf acc@(redexes, fnames, reacta, nextfr, context) (f:seqs) =
        let redex = seqTerm f in
        case getUnfolded pdefs nextfr redex of
            Nothing -> optUnf acc seqs
            Just (reactum, free) ->
                optUnf (redex:redexes, Set.union fnames (restrNames f), reactum:reacta, max free nextfr, MSet.delete f context) seqs

getUnfolded :: Monad m => PiDefs -> NameId -> PiTerm -> m (PiTerm, NameId)
getUnfolded pdefs nextFree (PiCall pvar args) = -- no need to check arity here: they have been checked by the name resolver
  case getDef pdefs pvar of
    Just (formArgs, proc) ->
        let (proc', free) = refreshWith nextFree (Set.fromList formArgs) proc
        in return (applySub (mkSubst $ zip formArgs args) $ proc', free)
    Nothing -> fail $ "No definition found for " ++ show pvar -- questionable: here we choose to make undefined calls just deadlock
        -- error $ "No definition found for " ++ show pvar
getUnfolded pdefs nextFree (Bang p) = let (p', f) = refresh nextFree p in return (parall p' (Bang p), f)
getUnfolded _ _ _                   = fail "Not unfoldable redex"

match (In x xs, _) (Out y ys, _)
    | x == y && length xs == length ys =
        [mkSubst $ zip xs ys]
match a@(Out _ _, _) b@(In _ _, _) = match b a -- just to avoid code duplication
match        _             _       = []

