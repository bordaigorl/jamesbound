{- |
    Module      :  Hierarchical
    Description :  Type system for Hierarchical Systems
    Copyright   :  (c) 2014 Oxford University
    License     :  CRAPL

    Maintainer  :  emanuele.dosualdo@cs.ox.ac.uk
    Stability   :  experimental

Type system for Hierarchical Systems.

Assumptions for the prototype:

 * base types form a total order
 * no definitions, no calls to process ids

-}
module Language.PiCalc.Analysis.Hierarchical(
      AdjMap
    -- * Simple types inference
    , module Language.PiCalc.Analysis.SimpleTyping
    -- * Tied to/Migratable relation
    , isLinkedTo
    , linkedTo
    , linkedToGraph
    , tiedTo
    , tiedToClasses
    , relTied
    -- * Derive constrains on base types
    , BConstr(..)
    , constrBaseTypes
    , baseTypesGraph
    , allBaseTypesGraphs
    , quotientBConstr
    -- * Solve base types constraints
    , SolverError(..)
    , solveBTConstr
    , solveBTConstrIncomplete
    , solveBTConstrSlow
    -- * Inference algorithm
    , InferredTypes(..)
    , inferTypes
    , inferTypesIncomplete
    , inferTypesSlow
    , inferenceSucceeded
    , isTypablyHierarchical
    , reach, reachability
) where

import Language.PiCalc.Syntax
import Language.PiCalc.Analysis.SimpleTyping

import Data.List(partition)

import Data.Set(Set)
import qualified Data.Set as Set
import Data.Set.Infix
import Data.Map(Map)
import qualified Data.Map as Map
import qualified Data.MultiSet as MSet

import Control.Monad (foldM)

{--
TODO:
  * Global types: when quotienting constr check if BVar is only assoc with global names → exclude from constraints
--}

type AdjMap node = Map node (Set node)
-- ^ this is the representation of a graph in this module

adjacent :: Ord n => n -> AdjMap n -> Set n
adjacent = Map.findWithDefault (∅)

-----------------------------------------------------------
-- * Tied to/Migratable relation
-----------------------------------------------------------

-- note: ns are the free names of the factor which are restricted in the normal form to which it belongs.
--       It is therefore unnecessary to intersect it with X (from νX.Π Pi)
isLinkedTo xs (StdFactor _ ns) = xs `intersects` ns

linkedTo xs s = filter (isLinkedTo xs) $ distFactors s

linkedToGraph :: PiTerm -> AdjMap PiName
linkedToGraph p = foldr adjmap Map.empty $ onlyRestr $ linkedRestr p
  where
    adjmap xs m = Set.foldr (adj xs) m xs
    adj xs x = Map.insertWith Set.union x xs
    restr = allRestr p
    onlyRestr = map (∩ restr)

linkedRestr :: PiTerm -> [Set PiName]
linkedRestr p = snd $ fnofseq (∅) p
  where
    fnofseq rs (Parall ps) = (Set.unions $ map fst fnseqs, concatMap snd fnseqs)
      where fnseqs = map (fnofseq rs) $ MSet.distinctElems ps
    fnofseq rs (Alt alts) = (fn, (fn ∩ rs):seqs)
      where
        fnseqs = map freePreNames $ MSet.distinctElems alts
        fn = Set.unions $ map fst fnseqs
        seqs = concatMap snd fnseqs
        freePreNames (In x xs, cont) = (Set.insert x $ Set.difference fn' (Set.fromList xs), seqs')
          where (fn', seqs') = fnofseq (∅) cont
        freePreNames (Out x xs, cont) = (Set.union fn' (Set.fromList $ x:xs), seqs')
          where (fn', seqs') = fnofseq (∅) cont
        freePreNames (Tau, cont) = fnofseq (∅) cont
    fnofseq rs (New ns proc) = (Set.difference fn ns, seqs)
      where (fn, seqs) = fnofseq (rs ∪ ns) proc
    fnofseq rs (Bang proc) = fnofseq rs proc
    fnofseq rs (PiCall pv xs) = (Set.fromList xs, []) -- not supported!

tiedTo xs s = tiedTo' False xs [] $ distFactors s
  where
    tiedTo' True  _  _    [] = []
    tiedTo' False xs rest [] = tiedTo' False xs [] rest
    tiedTo' done  xs rest (f@(StdFactor t ns):fs)
        | xs `intersects` ns = f : tiedTo' True (xs ∪ ns) rest fs
        | otherwise          = tiedTo' done xs (f:rest) fs

tiedToClasses :: StdNFTerm -> [(Set PiName, Set PiName, [StdFactor])]
tiedToClasses s = map extractFree $ stdNFcc s
  where
    extractFree (ns, mf) = (ns, freenames \\ ns, fcts)
      where
        fcts = MSet.distinctElems mf
        freenames = Set.unions [freeNames $ seqTerm f | f <- fcts]


-- | Relativised tied-to relation:
--    is any of the @ys@ reachable from @y@ in @g@ never going through nodes in @xs@?
relTied :: AdjMap PiName -> Set PiName -> (PiName, Set PiName) -> Bool
relTied g xs (y, ys)
  | Set.null ys = False -- optimisation
  | otherwise = reach (Set.singleton y) (linked y)
  where
    reach curr front
        | curr `intersects` ys = True
        | size >= size'        = False
        | otherwise            = reach curr' front'
      where
        curr' = curr ∪ front
        front'= Set.foldr (\x s -> (linked x) ∪ s) (∅) front
        size  = Set.size curr
        size' = Set.size curr'

    linked x = (adjacent x g) \\ xs

-----------------------------------------------------------
-- * Constrain base types
-----------------------------------------------------------

data BConstr k = BLt k k
               | BLtOr [k] [k] k
           -- ^  BLtOr xs  ys  a  ≡  txs < ta ∨ tys < ta
    deriving (Eq, Show, Ord)
-- ^ Base type constraints.
--   @BConstr BVar@ will be used for inference
--   @BConstr BType@ for checking

-- instance Functor BConstr where
--     fmap f (BLt k1 k2)       = BLt (f k1) (f k2)
--     fmap f (BLtOr ks1 ks2 k) = BLtOr (map f ks1) (map f ks2) (f k)

(<?) = BLt

constrBaseTypes :: PiTerm -> [BConstr PiName]
constrBaseTypes p = proveProc $ stdNF p
  where

    proveProc s = proveProc' s $ tiedToClasses s
    proveProc' s classes =
        [ y <? x | (rn, fn, _) <- classes, y <- lst fn, x <- lst rn ] ++
        concatMap (proveSeq.seqTerm) (distFactors s)

    proveSeq (Alt alts)      =
        concatMap (proveAlt.stdAlt) (MSet.distinctElems alts)
    proveSeq (Bang proc)     = proveProc (stdNF proc)
    proveSeq (PiCall p args) = error "Process calls not supported yet"

    proveAlt (In a args, s) =
        [BLtOr xs' ys' a | not $ null xs', not $ null ys'] ++ proveProc' s classes
      where
        xs = Set.fromList args
        xs' = lst xs
        classes = tiedToClasses s
        ys = Set.unions [fn | (_, fn, _) <- classes, fn `intersects` xs]
        ys' = lst $ Set.delete a $ ys \\ xs

    proveAlt (_, p) = proveProc p

    lst s = filter (not.isGlobal) $ Set.elems s
    stdAlt (p,c) = (p, stdNF c)


-- | A directed edge x → y in the graph represents x > y.
--   Nodes represent base type classes.
baseTypesGraph :: BTypeClasses -> [BConstr PiName] -> AdjMap BVar
baseTypesGraph btcl bcnstr = toAdj $ map quotient bcnstr
  where
    quotient (BLt x y) = (repr y, Set.singleton $ repr x)
    quotient (BLtOr _ ys z) =  (repr z, Set.fromList $ map repr ys)
    -- *IMPORTANT*: BLtOr is simplified by ignoring the first disjunct:
    --              you can always circumvent it by not sending known things
    toAdj = Map.fromListWith Set.union
    -- insAll m = foldr defaultEmpty m $ allBVars btcl
    defaultEmpty k = Map.insertWith (\_ x -> x) k (∅)
    repr = getRepr btcl

-- | Lazily create a list of all instances arising from different choices of disjunctions.
--   Gives priority to second disjuncts.
--   A directed edge x → y in the graph represents x > y.
--   Nodes represent base type classes.
allBaseTypesGraphs :: BTypeClasses -> [BConstr PiName] -> [AdjMap BVar]
allBaseTypesGraphs btcl bcnstr =
    [ mergeAdj fixed (toAdj choice) | choice <- allChoices bltors]
  where
    (blts, bltors) = partition isBLt $ concatMap quotient bcnstr
    fixed = toAdj $ map untag blts
    allChoices [] = [[]]
    allChoices (BLtOr xs ys z : cs) =
        [(z, Set.fromList ys):rest | rest <- others] ++
        [(z, Set.fromList xs):rest | rest <- others]
      where others = allChoices cs

    quotient (BLt x y) = [BLt (repr x) (repr y)]
    quotient (BLtOr [] ys z) = [BLt (repr y) (repr z) | y <- ys]
    quotient (BLtOr xs [] z) = [BLt (repr x) (repr z) | x <- xs]
    quotient (BLtOr xs ys z) = [BLtOr (map repr xs) (map repr ys) (repr z)]

    toAdj = Map.fromListWith Set.union
    -- insAll m = foldr defaultEmpty m $ allBVars btcl -- not necessary: just use findWithDefault (∅)
    defaultEmpty k = Map.insertWith (\_ x -> x) k (∅)
    repr = getRepr btcl

    mergeAdj = Map.unionWith Set.union

    isBLt (BLt _ _) = True
    isBLt _ = False

    untag (BLt x y) = (y, Set.singleton x)


-- | Lazily create a list of all /acyclic/ instances arising from different choices of disjunctions.
--   equivalent to @(filter acyclic) . allBaseTypesGraphs@
acyclicBaseTypesGraphs :: BTypeClasses -> [BConstr PiName] -> Either [[BVar]] [AdjMap BVar]
acyclicBaseTypesGraphs btcl bcnstr =
    case reachability blts of
        Left  c       -> Left $ [cycles c]
        Right transcl ->
            case allChoices [] [] transcl disj [] of
                (failed, []) -> Left failed
                (_, success) -> Right success
  where
    (blts, bltors) = quotientBConstr btcl bcnstr
    disj = concatMap (\(z, ds) -> [(z, xs, ys) | (xs, ys) <- ds]) $ Map.toList bltors

    -- allChoices :: [[BVar]] -> [AdjMap BVar] -> AdjMap BVar -> [(BVar, Set BVar, Set BVar)] -> [(AdjMap BVar, [(BVar, Set BVar, Set BVar)])] -> ([[BVar]], [AdjMap BVar])
    allChoices failed success curr [] rest = backtrack failed (curr:success) rest
    allChoices failed success curr ((z,xs,ys):ds) rest =
        case (reach curr (z, xs), reach curr (z, ys)) of
            (Left cycle1, Left cycle2) ->
                backtrack (cycles cycle1:cycles cycle2:failed) success rest
            (Right choice1, Right choice2) ->
                allChoices failed success choice2 ds ((choice1,ds):rest)
            (Right choice1, Left cycle2) ->
                allChoices (cycles cycle2:failed) success choice1 ds rest
            (Left cycle1, Right choice2) ->
                allChoices (cycles cycle1:failed) success choice2 ds rest

    backtrack failed success [] = (failed, success)
    backtrack failed success ((other,cont):rest) =
        allChoices failed success other cont rest

    cycles = Set.elems


quotientBConstr :: BTypeClasses -> [BConstr PiName] -> (AdjMap BVar, Map BVar [(Set BVar, Set BVar)])
quotientBConstr btcl bcnstr = foldr quotient (Map.empty, Map.empty) bcnstr
  where
    -- quotient :: BConstr PiName -> (Map BVar (Set BVar), Map BVar [(Set BVar, Set BVar)]) -> (Map BVar (Set BVar), Map BVar [(Set BVar, Set BVar)])
    quotient (BLt x y) (mlt, mor) = (add x y mlt, mor)
    quotient (BLtOr [] ys z) (mlt, mor) = (addAll ys z mlt, mor)
    quotient (BLtOr xs [] z) (mlt, mor) = (addAll xs z mlt, mor)
    quotient (BLtOr xs ys z) (mlt, mor) = (mlt, addOr xs ys z mor)

    add x y = Map.insertWith Set.union (repr y)  (Set.singleton $ repr x)
    addAll xs z = Map.insertWith Set.union (repr z) (reprset xs)
    addOr xs ys z m = mergeOr (repr z) (reprset xs, reprset ys) m
    -- the quick'n'easy option but it may introduce more choices than needed:
    -- mergeOr k v m = Map.insertWith (++) k [v] m
    mergeOr k (a,b) m = Map.insert k (merge [] ors) m
      where
        ors = Map.findWithDefault [] k m
        merge done [] = (a,b):done
        merge done ((a', b') : rest)
          | a  ⊆ a' && b  ⊆ b' = ors
          | a' ⊆ a  && b' ⊆ b  = (a, b):rest ++ done
          | otherwise          = merge ((a',b'):done) rest

    repr = getRepr btcl
    reprset = Set.fromList . (map repr)


-- | Takes a transitively closed DAG @g@, a node @n@ and a set of nodes @{n1, ..., nk}@.
--   It returns @Right g'@ where @g'@ is the transitive closure of @g ∪ {(n, n1), ..., (n, nk)}@.
--   It returns @Left xs@ if the added edges create a cycle with nodes @xs@.
reach :: Ord n => AdjMap n -> (n, Set n) -> Either (Set n) (AdjMap n)
reach graph (n, adj)
    | n ∊ new   = Left $ Set.filter connected new
    | otherwise = Right $ Map.mapWithKey insNew graph'
  where
    new = adj ∪ Set.unions [ adjacent x graph | x <- Set.elems adj ]
    graph' = Map.insertWith (∪) n new graph
    insNew x rs
        | n ∊ rs    = Set.union rs new
        | otherwise = rs
    connected x = adjacent x graph `intersects` new

reachability :: Ord n => AdjMap n -> Either (Set n) (AdjMap n)
reachability graph = foldM reach graph $ Map.toList graph
-- starting from graph instead of Map.empty saves a few cycles


data SolverError = Cycles [[BVar]] | TIncompat [BVar]
    deriving Show

-- TODO: the solveBT* functions could be consolidated into a single solver parametric in the function generating the alternative or-free graphs

solveBTConstr :: PiTerm -> BTypeClasses -> Either SolverError [BVar]
solveBTConstr p btcl =
    case acyclicBaseTypesGraphs btcl constr of
        (Left cs) -> Left $ Cycles cs
        (Right choices) -> solveTcompat p btcl choices
  where
    constr = constrBaseTypes p

solveBTConstrSlow :: PiTerm -> BTypeClasses -> Either SolverError [BVar]
solveBTConstrSlow p btcl = solveTcompat p btcl $ allBaseTypesGraphs btcl constr
  where
    constr = constrBaseTypes p

solveTcompat :: PiTerm -> BTypeClasses -> [AdjMap BVar] -> Either SolverError [BVar]
solveTcompat p btcl choices =
    case break isRight $ map (solveBTConstr' linkGr btcl) choices of
        (e:_,  [] ) -> e
        ( _ , s:_ ) -> s
  where
    linkGr = linkedToGraph p

    isRight (Right _) = True
    isRight (Left  _) = False


solveBTConstrIncomplete :: PiTerm -> BTypeClasses -> Either SolverError [BVar]
solveBTConstrIncomplete p btcl = solveBTConstr' (linkedToGraph p) btcl (baseTypesGraph btcl $ constrBaseTypes p)

-- solveBTConstr' :: PiTerm -> BTypeClasses -> AdjMap BVar -> Either SolverError [BVar] --old
solveBTConstr' :: AdjMap PiName -> BTypeClasses -> AdjMap BVar -> Either SolverError [BVar]
solveBTConstr' linkGr btcl btg = tCompTopSort btg (∅) (allBVarsSet btcl)
  where
    -- linkGr = linkedToGraph p
    -- constr = constrBaseTypes p
    bvar2names = Map.map classToNames $ bvar2class btcl
    classToNames = tvarsToNames . snd

    outDegZero btg bv = Set.null $ bv ? btg
    (?) = Map.findWithDefault (∅) -- different type from adjacent

    untied done bv
        | Set.size names < 2 = True
        | otherwise = not $ relTied linkGr done $ Set.deleteFindMin names
      where names  = bv ? bvar2names

    remove new g = Map.map (\\ new) $ Set.foldr Map.delete g new

    merge bts ns = Set.unions $ ns:map (? bvar2names) bts

    cyclesFound c = Left $ Cycles [Set.elems c]
    nonTcompat  = Left . TIncompat . Set.elems

    tCompTopSort btg doneNames rembvar
      | Set.null rembvar = return []
      | otherwise =
            case Set.partition (outDegZero btg) rembvar of
                (top,  rest)
                  | Set.null top -> cyclesFound rest -- todo: find cycles in rest
                  | otherwise    ->
                      case Set.partition (untied doneNames) top of
                          (roots, tied)
                            | Set.null roots -> nonTcompat top
                            | otherwise -> do
                                let rootsl = Set.elems roots
                                sorted <- tCompTopSort (remove roots btg) (merge rootsl doneNames) (rest ∪ tied)
                                return $ rootsl ++ sorted


data InferredTypes
    = ArityMismatch ArityError
    -- ^ Unification failed
    | Inconsistent {
        cycles :: [[PiName]],
        typing :: Map PiName BVar,
        types  :: Map BVar (Maybe [BVar])
    }
    -- ^ Base type constraints solving failed.
    --   Its argument is a list of cycles in the dependencies.
    | NotTShaped {
        conflicts :: [PiName],
        typing    :: Map PiName BVar,
        types     :: Map BVar (Maybe [BVar])
    }
    -- ^ The term is not T-shaped for the inferred T.
    --   Its argument is a list of names that need to have the same name
    --   have to be in the same scope.
    | Inferred {
        typing    :: Map PiName BVar,
        -- ^ typing @x ↦ i@ means @x :: τ_i@
        types     :: Map BVar (Maybe [BVar]),
        -- ^ type @i ↦ [j1..jn]@ means @τ_i = t_i[τ_j1..τ_jn]@
        baseTypes :: [BVar]
        -- ^ baseTypes @[i1..in]@ means @T = t_i1 ⤙ .. ⤙ t_in@
    }
    -- ^ Type inference succeeded
    deriving (Eq, Show)

inferTypes :: PiTerm -> InferredTypes
inferTypes = inferTypes' solveBTConstr

inferTypesIncomplete :: PiTerm -> InferredTypes
inferTypesIncomplete = inferTypes' solveBTConstrIncomplete

inferTypesSlow :: PiTerm -> InferredTypes
inferTypesSlow = inferTypes' solveBTConstrSlow

inferTypes' solve p =
    case unifyTypes p of
        Left err -> ArityMismatch err
        Right eq ->
            let btcl = typeClasses eq
                -- constr = constrBaseTypes p
                -- g = baseTypesGraph btcl constr
            in case solve p btcl of
                Left (Cycles  cs) -> Inconsistent {
                    cycles    = resolveBVars btcl cs
                  , typing    = getTypeAnnot btcl
                  , types     = buildTypes btcl
                }
                Left (TIncompat samet) -> NotTShaped {
                    conflicts = bvarToNames' (allRestr p) btcl samet
                  , typing    = getTypeAnnot btcl
                  , types     = buildTypes btcl
                }
                Right solution -> Inferred {
                    typing    = getTypeAnnot btcl
                  , types     = buildTypes btcl
                  , baseTypes = solution
                }
  where
    resolveBVars btcl = map (bvarToNames btcl)
    bvarToNames btcl = concatMap (getBVarNames btcl)
    bvarToNames' restr btcl = concatMap getBVarNames'
      where getBVarNames' bvar =
              Set.toList $ (tvarsToNames $ tvars bvar) ∩ restr
            tvars bvar = snd $ (bvar2class btcl) Map.! bvar

inferenceSucceeded :: InferredTypes -> Bool
inferenceSucceeded Inferred{} = True
inferenceSucceeded _ = False

isTypablyHierarchical :: PiTerm -> Bool
isTypablyHierarchical = inferenceSucceeded . inferTypes

