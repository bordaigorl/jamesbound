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


disjointFrom :: Ord a => Set a -> Set a -> Bool
disjointFrom a b = Set.null $ a `Set.intersection` b

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

-----------------------------------------------------------
-- * Types and inference result
-----------------------------------------------------------

type BVar = Int

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
            let tvars'' = tvars `Set.union` tvars'
                diff    = tvars `Set.difference` tvars'
                new'    = (onlyNames a, onlyNames b):new
            merge arity'' tvars'' new' rest

    mergeArities  Nothing  t1  Nothing  t2 = return (Nothing, Set.empty, Set.empty)
    mergeArities (Just  n) t1  Nothing  t2 = return (Just n, t1, t2 \\ t1 )
    mergeArities  Nothing  t1 (Just  n) t2 = return (Just n, t1 \\ t2, t2 )
    mergeArities (Just n1) t1 (Just n2) t2
        | n1 == n2  = return (Just n1, t1 \\ t2, t2 \\ t1)
        | otherwise = arityError n1 n2 tvars

    (\\) = Set.difference

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

tiedTo xs s = tiedTo' False xs [] $ distFactors s
  where
    tiedTo' True  _  _    [] = []
    tiedTo' False xs rest [] = tiedTo' False xs [] rest
    tiedTo' done  xs rest (f@(StdFactor t ns):fs)
        | xs `intersects` ns = f : tiedTo' True (xs `Set.union` ns) rest fs
        | otherwise          = tiedTo' done xs (f:rest) fs

tiedToClasses s = map extractFree $ stdNFcc s
  where
    extractFree (ns, mf) = (ns, freenames \\ ns, fcts)
      where
        fcts = MSet.distinctElems mf
        freenames = Set.unions [freeNames $ seqTerm f | f <- fcts]
    (\\) = Set.difference


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
    (\\) = Set.difference

-- | Base types sat instance
type BTSat = [(BVar, BVar, [BVar])]
           -- dummy  key     adj

-- | A directed edge x → y in the graph represents y < x.
--   Nodes represent base type classes.
baseTypesGraph :: BTypeClasses -> [BConstr PiName] -> BTSat
baseTypesGraph btcl bcnstr = map adj $ toAdjList $ map quotient bcnstr
  where
    quotient (BLt x y) = (repr y, Set.singleton $ repr x)
    quotient (BLtOr _ ys z) =  (repr z, Set.fromList $ map (repr) ys)
    -- *IMPORTANT*: BLtOr is simplified by ignoring the first disjunct:
    --              you can always circumvent it by not sending known things
    --              i.e. the cases when you need it are uninteresting and can be avoided
    insAll m = foldr defaultEmpty m $ allBVars btcl
    toAdjList = Map.toList . insAll . (Map.fromListWith Set.union)
    adj (x, ys) = (x, x, Set.toList ys)
    defaultEmpty k = Map.insertWith (\_ x -> x) k Set.empty
    repr = getRepr btcl

solveBTSat :: BTSat -> Either [[BVar]] [BVar]
solveBTSat g =
    case partition acyclic $ stronglyConnComp g of
        (solution, []) -> Right $ map untagA solution
        (_,  conflict) -> Left  $ map untagC conflict
  where
    acyclic (AcyclicSCC _) = True
    acyclic _              = False
    untagA (AcyclicSCC x) = x
    untagC (CyclicSCC x)  = x

data InferredTypes
    = ArityMismatch ArityError
    -- ^ Unification failed
    | Inconsistent [[PiName]]
    -- ^ Base type constraints solving failed
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
                constr = constrBaseTypes p
                g = baseTypesGraph btcl constr
            in case solveBTSat g of
                Left cycles    -> Inconsistent $ resolveBVars btcl cycles
                Right solution -> Inferred {
                    typing    = getTypeAnnot btcl
                  , types     = buildTypes btcl  -- TODO
                  , baseTypes = solution
                }

resolveBVars btcl = map (bvarToNames btcl)
bvarToNames btcl = concatMap (getBVarNames btcl)

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

-- solveBaseConstr edges = topSort [fst $ Map.findMin adj | not $ null adj ] Set.empty
--   where
--     adj = foldr (\(x,y) m -> Map.insertWith (++) x [y] m) Map.empty edges
--     topSort [] visited = []
--     topSort (x:xs) visited
--         | x `Set.member` visited = Nothing
--         | otherwise = x:topSort (succs x ++ xs)
--     succs x = Map.findWithDefault [] x adj


--     proveAlt (In a xs, p) =
-- --         --[HSubType (NameType x) (ArgType a i) | (x, i) <- zip xs [1..]] ++
-- --         [HTCompat (NameType a) (map NameType xs)] ++
--         [BLtOr a rxs zs |
--             not $ isGlobal a,
--             fct <- distFactors p,
--             let fn = freeNames $ seqTerm fct,
--             let rxs = Set.toList $ Set.intersection fn sxs,
--             not $ null rxs, -- would be filtered anyway otherwise
--             let zs = filter (not.isGlobal) $ Set.toList $ Set.delete a $
--                         Set.difference fn (sxs `Set.union` restrNames fct)
--         ] ++
--         --maybe following is enough when using compatibility
--         --[HGeqMax (NameType a) (map NameType zs) |
--         --    not $ isGlobal a,
--         --    fct <- distFactors p,
--         --    let fn = freeNames $ seqTerm fct,
--         --    let rxs = Set.toList $ Set.intersection fn sxs,
--         --    not $ null $ rxs,
--         --    let zs = filter (not.isGlobal) $ Set.toList $ Set.delete a $
--         --                Set.difference fn (sxs `Set.union` restrNames fct)
--         --] ++
--         --[HLeq (NameType z) (NameType a) |
--         --    fct <- distFactors p,
--         --    let fn = freeNames $ seqTerm fct,
--         --    not $ Set.null $ Set.intersection fn sxs,
--         --    z <- Set.toList $ Set.difference fn (sxs `Set.union` restrNames fct)
--         --] ++
--         -- the following only when subtyping is ⊑
--         --[HGeqMax (NameType x) (map NameType zs) |
--         --    x <- xs,
--         --    let zs = filter (not.isGlobal) $ Set.toList $ Set.unions
--         --          [ fn' | fct <- distFactors p,
--         --                 let fn = freeNames $ seqTerm fct,
--         --                 Set.member x fn,
--         --                 let fn' = Set.difference fn (sxs `Set.union` restrNames fct) ]
--         --] ++
--         proveProc p
--       where sxs = Set.fromList xs
--     proveAlt (Out a xs, p) =
--         --[HSubType (NameType x) (ArgType a i) | (x, i) <- zip xs [1..]] ++
--         HTCompat (NameType a) (map NameType xs):
--         proveProc p
--     proveAlt (Tau, p) = proveProc p

--     nontrivial (HLeq k1 k2)     = k1 /= k2
--     nontrivial (HGeqMax k1 ks)  = not $ null ks
--     nontrivial (HGeqOr a b1 b2) = not $ null b1 || null b2
--     nontrivial (HGt  k1 k2)     = True
--     nontrivial (HAllDiff ks)    = length ks > 1
--     nontrivial (HSubType t1 t2) = t1 /= t2
--     nontrivial _ = True

-- inferTypes :: PiTerm -> Map PiName (HType BType)
-- inferTypes p = error "TODO"
--   where
--     cs = constrainTypes p
    -- generate templates from compatibility info (HType structure for each var)
    -- in the form of a map PiName ↦ (HType Node) where Node is just an id for the level var
    -- generate leq couples (non-det because of OR use comprehensions)
    -- and diff couples (graph)
    -- find indegree-leq = 0 and assign arbitrary vals respecting diff arcs
    -- if fail, backtrack
    -- on success, substitute templates with computed levels

-----------------------------------------------------------
-- * Do later
-----------------------------------------------------------

data HType k = HType {base::k, argTypes::[HType k]}
    deriving (Eq, Show)

instance Functor HType where
    fmap f (HType k ks) = HType (f k) (map (fmap f) ks)

instance (Ord k) => Ord (HType k) where
    (HType k1 ks1) <= (HType k2 ks2) =
        k1 <= k2 &&
        and (zipWith (<=) ks1 ks2) &&
        length ks1 == length ks2

-- we only consider linear orders here, so no need for forests
-- (to emphasize this, we call nodes "levels", @Lvl@)
data BType = Global | Any | Lvl Integer
    deriving (Eq, Ord, Show)
-- data TypesForest n = TF [(n, TF n)] -- no need for this now

baseParent :: BType -> BType -> Bool
baseParent Global  Global  = True
baseParent Any     Any     = True
baseParent (Lvl i) (Lvl j) = i <= j
baseParent _       _       = False


-- checkConstraints :: [TConstr (HType BType)] -> [BConstr BType] -> Bool
-- checkConstraints tc bc = all checkBConstr bc && all checkTConstr tc

-- checkBConstr (BLt k1 k2)     = k1 <= k2
-- checkBConstr (BLtOr b1 b2 a) = all (a >=) b1 || all (a >=) b2

-- checkTConstr (TEq t1 t2) = t1 == t2
-- checkTConstr (TArity t n) = length (argtypes t) == n
