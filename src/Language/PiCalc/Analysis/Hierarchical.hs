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
module Language.PiCalc.Analysis.Hierarchical where

import Language.PiCalc.Syntax
import Language.PiCalc.Semantics

import Data.List(partition)

import Data.Set(Set)
import qualified Data.Set as Set
import Data.Map(Map)
import qualified Data.Map as Map
import qualified Data.MultiSet as MSet

import Data.Graph

import Data.Maybe(mapMaybe)
import Control.Monad
import Control.Monad.State

{-- TODO:
      * Simple T-shapedness test (made easier by linear order + most general base types)
      * Global types: when quotienting constr check if BVar is only assoc with global names → exclude from constraints
--}

(∪), (∩), (\\) :: Ord a => Set a -> Set a -> Set a
(∪) = Set.union
(∩) = Set.intersection
(\\) = Set.difference

disjointFrom :: Ord a => Set a -> Set a -> Bool
disjointFrom a b = Set.null $ a ∩ b

intersects :: Ord a => Set a -> Set a -> Bool
intersects a b = not $ a `disjointFrom` b

allActions :: PiTerm -> [(PiName, [PiName])]
allActions (Parall ps) = concatMap allActions (MSet.distinctElems ps)
allActions (Alt    as) =
    [strip a | a <- alts, not $ isTau a] ++ concatMap (allActions.snd) alts
  where
    alts = MSet.distinctElems as
    strip (Out n args, _) = (n, args)
    strip (In  n args, _) = (n, args)
allActions (New  _  p) = allActions p
allActions (Bang    p) = allActions p
allActions (PiCall _ _) = error "Process calls not supported yet"

freeNamesOfSeq :: PiTerm -> [Set PiName]
freeNamesOfSeq p = snd $ fnofseq Set.empty p
  where
    fnofseq rs (Parall ps) = (Set.unions $ map fst fnseqs, concatMap snd fnseqs)
      where fnseqs = map (fnofseq rs) $ MSet.distinctElems ps
    fnofseq rs (Alt alts) = (fn, (fn ∩ rs):seqs)
      where
        fnseqs = map freePreNames $ MSet.distinctElems alts
        fn = Set.unions $ map fst fnseqs
        seqs = concatMap snd fnseqs
        freePreNames (In x xs, cont) = (Set.insert x $ Set.difference fn' (Set.fromList xs), seqs')
          where (fn', seqs') = fnofseq Set.empty cont
        freePreNames (Out x xs, cont) = (Set.union fn' (Set.fromList $ x:xs), seqs')
          where (fn', seqs') = fnofseq Set.empty cont
        freePreNames (Tau, cont) = fnofseq Set.empty cont
    fnofseq rs (New ns proc) = (Set.difference fn ns, seqs)
      where (fn, seqs) = fnofseq (rs ∪ ns) proc
    fnofseq rs (Bang proc) = fnofseq rs proc
    fnofseq rs (PiCall pv xs) = (Set.fromList xs, []) -- not supported!


-----------------------------------------------------------
-- * Types and inference result
-----------------------------------------------------------

type BVar = Int

type AdjMap node = Map node (Set node)

type ArityError = (Int, Int, [PiName])

-----------------------------------------------------------
-- * Simple types inference via unification
-----------------------------------------------------------

-- | Type variable representation,
data TVar = NameType PiName    -- name
          | ArgType PiName Int -- name/arg position
            -- to support calls add PVarType PArgType
    deriving (Eq, Show, Ord)

type ArityC = Maybe Int
type TypeC = [(ArityC, Set TVar)]
type ConstrSys = StateT TypeC (Either ArityError)

emptyConstr = []

unsat :: ArityError -> ConstrSys a
unsat = lift . Left

unifyTypes :: PiTerm -> Either ArityError TypeC
unifyTypes p = execStateT (constrTypes p) emptyConstr

constrTypes :: PiTerm -> ConstrSys ()
constrTypes p = do
    let actions = allActions p
    -- forM_ actions constrArity
    ar <- constrArities actions
    forM_ actions constrArgs


onlyNames :: Set TVar -> [PiName]
onlyNames = onlyNames' . Set.toList
  where
    onlyNames' []              = []
    onlyNames' (NameType x:ts) = x : onlyNames' ts
    onlyNames' (_:ts)          = onlyNames' ts

tvarsToNames :: Set TVar -> Set PiName
tvarsToNames tvs = Set.map untag $ Set.filter isNameTvar tvs
  where untag (NameType x) = x

isNameTvar (NameType _) = True
isNameTvar _            = False

namesFromTVars tvars =  mapMaybe nameFromTVar $ Set.toList tvars
nameFromTVar (NameType n) = Just n
nameFromTVar _            = Nothing

tellEq :: ArityC -> Set TVar -> ConstrSys ()
tellEq arity tvars = do
    c <- get
    (c', new) <- merge arity tvars [] c
    put c'
    propagate new
  where
    merge arity tvars new [] = return ([(arity, tvars)], (arity, new))
    merge arity tvars new ((arity', tvars'):rest)
        | tvars `disjointFrom` tvars' = do
            (rest', anew') <- merge arity tvars new rest
            return ((arity', tvars'):rest', anew')
        | otherwise = do
            (arity'', a, b) <- mergeArities arity tvars arity' tvars'
            let tvars'' = tvars ∪ tvars'
                diff    = tvars \\ tvars'
                new'    = (onlyNames a, onlyNames b):new
            merge arity'' tvars'' new' rest

    mergeArities  Nothing  t1  Nothing  t2 = return (Nothing, Set.empty, Set.empty)
    mergeArities (Just  n) t1  Nothing  t2 = return (Just n, t1, t2 \\ t1 )
    mergeArities  Nothing  t1 (Just  n) t2 = return (Just n, t1 \\ t2, t2 )
    mergeArities (Just n1) t1 (Just n2) t2
        | n1 == n2  = return (Just n1, t1 \\ t2, t2 \\ t1)
        | otherwise = arityError n1 n2 tvars

    -- (\\) = Set.difference

propagate :: (ArityC, [([PiName], [PiName])]) -> ConstrSys ()
propagate (Nothing, _) = return ()
propagate (Just 0,  _) = return () -- optimisation
propagate (Just n, xs) =
    forM_ xs $ \(as,bs) ->
        forM_ [1..n] $ \i ->
            forM_ [(x,y) | x <- as, y <- bs] $ \(x,y) ->
                tellEq Nothing $ Set.fromList [ArgType x i, ArgType y i]

arityError n1 n2 tvars = lift $ Left (n1, n2, namesFromTVars tvars)
arityError' n1 n2 name = lift $ Left (n1, n2, [name])

{-- not needed anymore
constrArity (n, args) = do
    let arity = length args
    tellEq (Just arity) (Set.singleton (NameType n))
    -- could be made more efficient by constructing a map PiName -> arity and then
    -- transform it into constraints for subsequent use
--}

constrArities actions = do
    ar <- constrArities' Map.empty actions
    put [ (Just a, Set.singleton (NameType n)) | (n,a) <- Map.toList ar ]
    return ar

constrArities' ar [] = return ar
constrArities' ar ((n, args):rest) = do
    let arity = length args
    case Map.lookup n ar of
        Nothing -> constrArities' (Map.insert n arity ar) rest
        Just k
            | k == arity -> constrArities' ar rest
            | otherwise  -> arityError' k arity n


constrArgs (n, args) =
    forM_ (zip args [1,2..]) $ constrArg n

constrArg name (arg, i) =
    tellEq Nothing $ Set.fromList [NameType arg, ArgType name i]

data BTypeClasses = BTC {
    maxBVar :: BVar
  , tvar2bvar :: Map TVar BVar
  , bvar2class :: Map BVar (ArityC, Set TVar)
}

allBVars btcl = [0..maxBVar btcl]
allBVarsSet btcl = Map.keysSet $ bvar2class btcl
getRepr btcl name = (tvar2bvar btcl) Map.! (NameType name)
getReprArg btcl name i = (tvar2bvar btcl) Map.! (ArgType name i)
getBVarNames btcl bvar = onlyNames $ snd $ (bvar2class btcl) Map.! bvar

getTypeAnnot btcl =
    Map.mapKeysMonotonic untag $ Map.filterWithKey isNameType $ tvar2bvar btcl
  where
    untag (NameType x) = x
    isNameType (NameType _) _ = True
    isNameType _ _ = False


typeClasses :: TypeC -> BTypeClasses
typeClasses c = BTC {
        maxBVar    = lastBVar
      , tvar2bvar  = representatives
      , bvar2class = classes
    }
  where
    tagged          = zip [0..lastBVar] c
    lastBVar        = length c - 1
    classes         = Map.fromDistinctAscList tagged
    representatives = Map.fromList $ concatMap typeClasses' tagged
    typeClasses' (n, (_, tv)) = [ (x, n) | x <- Set.toAscList tv ]
                             -- [ (x, n) | (NameType x) <- Set.toAscList tv ]



-----------------------------------------------------------
-- * Tied to/Migratable relation
-----------------------------------------------------------

-- note: ns are the free names of the factor which are restricted in the normal form to which it belongs.
--       It is therefore unnecessary to intersect it with X (from νX.Π Pi)
isLinkedTo xs (StdFactor _ ns) = xs `intersects` ns

linkedTo xs s = filter (isLinkedTo xs) $ distFactors s

linkedToGraph :: PiTerm -> AdjMap PiName
linkedToGraph p = foldr adjmap Map.empty $ onlyRestr $ freeNamesOfSeq p
  where
    adjmap xs m = Set.foldr (adj xs) m xs
    adj xs x = Map.insertWith Set.union x xs
    restr = allRestr p
    onlyRestr = map (∩ restr)


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
    -- (\\) = Set.difference

-----------------------------------------------------------
-- * Constrain base types
-----------------------------------------------------------

data BConstr k = BLt k k
               | BLtOr [k] [k] k
           -- ^  BLtOr x  ys a ≡ txs < ta ∨ tys < ta
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
        ys' = lst $ Set.delete a  $ ys \\ xs

    proveAlt (_, p) = proveProc p

    lst s = filter (not.isGlobal) $ Set.elems s
    stdAlt (p,c) = (p, stdNF c)
    -- (\\) = Set.difference

-- -- | Base types sat instance
-- type BTSat = [(BVar, BVar, [BVar])]
--            -- dummy  key     adj

-- -- | A directed edge x → y in the graph represents y < x.
-- --   Nodes represent base type classes.
-- baseTypesGraph :: BTypeClasses -> [BConstr PiName] -> BTSat
-- baseTypesGraph btcl bcnstr = map adj $ toAdjList $ map quotient bcnstr
--   where
--     quotient (BLt x y) = (repr y, Set.singleton $ repr x)
--     quotient (BLtOr _ ys z) =  (repr z, Set.fromList $ map (repr) ys)
--     -- *IMPORTANT*: BLtOr is simplified by ignoring the first disjunct:
--     --              you can always circumvent it by not sending known things
--     --              i.e. the cases when you need it are uninteresting and can be avoided
--     insAll m = foldr defaultEmpty m $ allBVars btcl
--     toAdjList = Map.toList . insAll . (Map.fromListWith Set.union)
--     adj (x, ys) = (x, x, Set.toList ys)
--     defaultEmpty k = Map.insertWith (\_ x -> x) k Set.empty
--     repr = getRepr btcl

-- solveBTSat :: BTSat -> Either [[BVar]] [BVar]
-- solveBTSat g =
--     case partition acyclic $ stronglyConnComp g of
--         (solution, []) -> Right $ map untagA solution
--         (_,  conflict) -> Left  $ map untagC conflict
--   where
--     acyclic (AcyclicSCC _) = True
--     acyclic _              = False
--     untagA (AcyclicSCC x) = x
--     untagC (CyclicSCC x)  = x


-- | A directed edge x → y in the graph represents x > y.
--   Nodes represent base type classes.
baseTypesGraph :: BTypeClasses -> [BConstr PiName] -> AdjMap BVar
baseTypesGraph btcl bcnstr = toAdj $ map quotient bcnstr
  where
    quotient (BLt x y) = (repr y, Set.singleton $ repr x)
    quotient (BLtOr _ ys z) =  (repr z, Set.fromList $ map (repr) ys)
    -- *IMPORTANT*: BLtOr is simplified by ignoring the first disjunct:
    --              you can always circumvent it by not sending known things
    toAdj = insAll . (Map.fromListWith Set.union)
    insAll m = foldr defaultEmpty m $ allBVars btcl
    defaultEmpty k = Map.insertWith (\_ x -> x) k Set.empty
    repr = getRepr btcl

data SolverError = Cycles [BVar] | TIncompat [BVar]

solveBTConstr :: PiTerm -> BTypeClasses -> Either SolverError [BVar]
solveBTConstr p btcl = tCompTopSort (baseTypesGraph btcl constr) Set.empty (allBVarsSet btcl)
  where
    linkGr = linkedToGraph p
    constr = constrBaseTypes p
    bvar2names = Map.map classToNames $ bvar2class btcl
    classToNames = tvarsToNames . snd

    outDegZero btg bv = Set.null $ bv ? btg
    (?) = Map.findWithDefault Set.empty
    -- (∪) = Set.union
    -- (\\) = Set.difference

    untied done bv =
        let names = (bv ? bvar2names)
        in if Set.size names < 2
            then True
            else not $ relTied linkGr done $ Set.deleteFindMin names

    remove new g = Map.map (\\ new) $ Set.foldr Map.delete g new

    merge bts ns = Set.unions $ ns:map (? bvar2names) bts

    cyclesFound = Left . Cycles . Set.elems
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
        front'= Set.foldr (\x s -> (linked x) ∪ s) Set.empty front
        size  = Set.size curr
        size' = Set.size curr'

    linked x = (adjacent x) \\ xs
    adjacent x = Map.findWithDefault Set.empty x g
    -- (∪) = Set.union
    -- (∩) = Set.intersection
    -- (\\) = Set.difference


data InferredTypes
    = ArityMismatch ArityError
    -- ^ Unification failed
    | Inconsistent [[PiName]]
    -- ^ Base type constraints solving failed.
    --   Its argument is a list of cycles in the dependencies.
    | NotTShaped [PiName]
    -- ^ The term is not T-shaped for the inferred T.
    --   Its argument is a list of names that need to have the same name
    --   but appear together in the same sequential term.
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
inferTypes p =
    case unifyTypes p of
        Left err -> ArityMismatch err
        Right eq ->
            let btcl = typeClasses eq
                -- constr = constrBaseTypes p
                -- g = baseTypesGraph btcl constr
            in case solveBTConstr p btcl of
                Left (Cycles  cycles)  -> Inconsistent $ resolveBVars btcl [cycles]
                Left (TIncompat samet) -> NotTShaped $ bvarToNames' (allRestr p) btcl samet
                Right solution -> Inferred {
                    typing    = getTypeAnnot btcl
                  , types     = buildTypes btcl  -- TODO
                  , baseTypes = solution
                }

resolveBVars btcl = map (bvarToNames btcl)
bvarToNames btcl = concatMap (getBVarNames btcl)
bvarToNames' restr btcl = concatMap getBVarNames'
  where getBVarNames' bvar =
          Set.toList $ (tvarsToNames $ tvars bvar) ∩ restr
        tvars bvar = snd $ (bvar2class btcl) Map.! bvar

buildTypes btcl = Map.map genType $ bvar2class btcl
  where
    genType (Nothing, _) = Nothing
    genType (Just arity, ns) = Just $ map (argType ns) [1..arity]
    argType ns i = getReprArg btcl (anyNameInClass ns) i

    anyNameInClass ns =
        case Set.findMin ns of
            (NameType x) -> x
            _ -> error "Type inference: No name in class!"

buildTypingEnv :: TypeC -> (Map PiName BVar, Map BVar (Maybe [BVar]))
buildTypingEnv eq = let btcl = typeClasses eq in
    (getTypeAnnot btcl, buildTypes btcl)

