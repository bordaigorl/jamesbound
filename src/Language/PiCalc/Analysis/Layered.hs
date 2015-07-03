{- |
Module      :  Layered
Description :  Type system for Layered Systems
Copyright   :  (c) 2014 Oxford University
License     :  CRAPL

Maintainer  :  emanuele.dosualdo@cs.ox.ac.uk
Stability   :  experimental

Type system for Layered Systems
-}
module Language.PiCalc.Analysis.Layered where

import Language.PiCalc.Syntax
import Language.PiCalc.Semantics

import Data.Set(Set)
import qualified Data.Set as Set
import Data.Map(Map)
import qualified Data.Map as Map
import qualified Data.MultiSet as MSet

data LType k = LType k [LType k]
    deriving (Eq, Show)

type Level = Integer

instance (Ord k) => Ord (LType k) where
    (LType k1 ks1) <= (LType k2 ks2) =
        k1 <= k2 &&
        all (uncurry (<=)) (zip ks1 ks2) &&
        length ks1 == length ks2


instance Functor LType where
    fmap f (LType k ks) = LType (f k) (map (fmap f) ks)

level :: LType k -> k
level (LType k _) = k
argtypes :: LType k -> [LType k]
argtypes (LType _ ks) = ks

data TVar = NameType PiName | ArgType PiName Int
    deriving (Eq, Show, Ord)
-- to support calls add PVarType PArgType

data LConstr t k = LLeq k k
                 | LGeqMax k [k]
                 | LGeqOr k [k] [k]
                 | LGt k k
                 | LAllDiff [k]
                 | LSubType t t
                 | LTCompat t [t]
    deriving (Eq, Show, Ord)
-- ^ @LConstr TVar TVar@ will be used for inference
--   @LConstr (LType Level) Level@ for checking

instance Functor (LConstr t) where
    fmap f (LLeq k1 k2)     = LLeq (f k1) (f k2)
    fmap f (LGeqMax k1 ks)  = LGeqMax (f k1) (map f ks)
    fmap f (LGeqOr a l1 l2) = LGeqOr  (f a) (map f l1) (map f l2)
    fmap f (LGt  k1 k2)     = LGt  (f k1) (f k2)
    fmap f (LAllDiff ks)    = LAllDiff (map f ks)
    fmap f (LSubType t1 t2) = LSubType t1 t2
    fmap f (LTCompat t1 ts) = LTCompat t1 ts


checkConstraints :: [LConstr (LType Level) Level] -> Bool
checkConstraints = all checkConstr

checkConstr (LLeq k1 k2)     = k1 <= k2
checkConstr (LGeqMax k1 ks)  = all (k1 >=) ks
checkConstr (LGeqOr a b1 b2) = all (a >=) b1 || all (a >=) b2
checkConstr (LGt  k1 k2)     = k1 > k2
checkConstr (LAllDiff ks)    = all (uncurry (/=)) [(x,y) | (x, ys) <- takeout [] ks, y <- ys]
checkConstr (LSubType t1 t2) = t1 == t2  -- TRIVIAL SUBTYPING
--checkConstr (LSubType t1 t2) = t1 <= t2  -- PROPER SUBTYPING: problematic for invariance
checkConstr (LTCompat ta ts) = compat (ta, ts)
  where
    compat (ta@(LType ka ts), txs) =
        length ts == length txs &&
        all cond (zip ts txs) &&
        all compat (zip ts $ map argtypes txs)
      where cond (LType k1 _, LType k2 _) = (k1 <= ka && k2 <= ka) || k1 == k2
      --where cond (LType k1 _, LType k2 _) = (k1 <= ka && k2 <= k1) || k1 == k2


takeout r [] = []
takeout r (x:xs) = (x, r++xs):takeout (x:r) xs

-- change so the map can be from PiName instead of TVar
substConstr :: Map PiName (LType l)  -> [LConstr TVar TVar]-> [LConstr (LType l) l]
substConstr sub = map typsub
  where
    typsub (LLeq k1 k2)     = LLeq (lvlsub k1) (lvlsub k2)
    typsub (LGeqMax k1 ks)  = LGeqMax (lvlsub k1) (map lvlsub ks)
    typsub (LGeqOr a b1 b2) = LGeqOr (lvlsub a) (map lvlsub b1) (map lvlsub b2)
    typsub (LGt  k1 k2)     = LGt  (lvlsub k1) (lvlsub k2)
    typsub (LAllDiff ks)    = LAllDiff (map lvlsub ks)
    typsub (LSubType x1 x2) = LSubType (lookupvar x1) (lookupvar x2)
    typsub (LTCompat t ts)  = LTCompat (lookupvar t) (map lookupvar ts)

    lvlsub x = level $ lookupvar x

    lookupvar (NameType x)  = sub Map.! x
    lookupvar (ArgType x i) = let (LType k ks) = sub Map.! x in ks !! (i-1)


constrainTypes :: PiTerm -> [LConstr TVar TVar]
constrainTypes p = filter nontrivial $ proveProc (stdNF p)
  where
    proveProc s = concatMap proveFact (distFactors s)

    proveFact (StdFactor t ns) = LAllDiff vns:(proveGT ++ proveSeq t)
      where
        vns = map NameType $ Set.toList fn
        fn = freeNames t
        proveGT = [LGt (NameType x) (NameType y) | x <- Set.toList ns, y <- Set.toList (Set.difference fn ns) ]

    proveSeq (Alt alts)      =
        concatMap (proveAlt.stdAlt) (MSet.distinctElems alts)
    proveSeq (Bang proc)     = proveProc (stdNF proc)
    proveSeq (PiCall p args) = error "Process calls not supported yet"

    proveAlt (In a xs, p) =
        --[LSubType (NameType x) (ArgType a i) | (x, i) <- zip xs [1..]] ++
        [LTCompat (NameType a) (map NameType xs)] ++
        [LGeqOr (NameType a) (map NameType rxs) (map NameType zs) |
            not $ isGlobal a,
            fct <- distFactors p,
            let fn = freeNames $ seqTerm fct,
            let rxs = Set.toList $ Set.intersection fn sxs,
            not $ null rxs, -- would be filtered anyway otherwise
            let zs = filter (not.isGlobal) $ Set.toList $ Set.delete a $
                        Set.difference fn (sxs `Set.union` restrNames fct)
        ] ++
        --maybe following is enough when using compatibility
        --[LGeqMax (NameType a) (map NameType zs) |
        --    not $ isGlobal a,
        --    fct <- distFactors p,
        --    let fn = freeNames $ seqTerm fct,
        --    let rxs = Set.toList $ Set.intersection fn sxs,
        --    not $ null $ rxs,
        --    let zs = filter (not.isGlobal) $ Set.toList $ Set.delete a $
        --                Set.difference fn (sxs `Set.union` restrNames fct)
        --] ++
        --[LLeq (NameType z) (NameType a) |
        --    fct <- distFactors p,
        --    let fn = freeNames $ seqTerm fct,
        --    not $ Set.null $ Set.intersection fn sxs,
        --    z <- Set.toList $ Set.difference fn (sxs `Set.union` restrNames fct)
        --] ++
        -- the following only when subtyping is ⊑
        --[LGeqMax (NameType x) (map NameType zs) |
        --    x <- xs,
        --    let zs = filter (not.isGlobal) $ Set.toList $ Set.unions
        --          [ fn' | fct <- distFactors p,
        --                 let fn = freeNames $ seqTerm fct,
        --                 Set.member x fn,
        --                 let fn' = Set.difference fn (sxs `Set.union` restrNames fct) ]
        --] ++
        proveProc p
      where sxs = Set.fromList xs
    proveAlt (Out a xs, p) =
        --[LSubType (NameType x) (ArgType a i) | (x, i) <- zip xs [1..]] ++
        LTCompat (NameType a) (map NameType xs):
        proveProc p
    proveAlt (Tau, p) = proveProc p

    stdAlt (p,c) = (p, stdNF c)

    nontrivial (LLeq k1 k2)     = k1 /= k2
    nontrivial (LGeqMax k1 ks)  = not $ null ks
    nontrivial (LGeqOr a b1 b2) = not $ null b1 || null b2
    nontrivial (LGt  k1 k2)     = True
    nontrivial (LAllDiff ks)    = length ks > 1
    nontrivial (LSubType t1 t2) = t1 /= t2
    nontrivial _ = True

inferTypes :: PiTerm -> Map PiName (LType Level)
inferTypes p = error "TODO"
  where
    cs = constrainTypes p
    -- generate templates from compatibility info (LType structure for each var)
    -- in the form of a map PiName ↦ (LType Node) where Node is just an id for the level var
    -- generate leq couples (non-det because of OR use comprehensions)
    -- and diff couples (graph)
    -- find indegree-leq = 0 and assign arbitrary vals respecting diff arcs
    -- if fail, backtrack
    -- on success, substitute templates with computed levels
