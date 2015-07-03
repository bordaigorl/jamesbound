module Language.PiCalc.Semantics.Substitutions(
    NameSubst,
    mkSubst,
    matchSubst,
    blindSub,
    subFun,
    applySub,
    refresh,
    refreshWith
) where

import Language.PiCalc.Syntax.Term

import Data.Map(Map)
import qualified Data.Map as Map
import qualified Data.MultiSet as MSet
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Set.Infix

type NameSubst = Map PiName PiName

-- | creates a substitution from a name association list
mkSubst :: [(PiName, PiName)] -> NameSubst
mkSubst = Map.fromList

{- |
    creates a substitution matching the two lists of names (in the given order):
    @matchSubst [a,b,c] [x,y,z]@ = { a -> x, b -> y, c -> z }
    Note that if one of the lists is shorter, the variables missing a match are
    not included in the domain of the substitution
-}
matchSubst :: [PiName] -> [PiName] -> NameSubst
matchSubst xs ys = mkSubst $ zip xs ys

-- Could have a more general type signature but we want to use these on well formed terms.
applySub :: NameSubst -> PiTerm -> PiTerm
applySub σ p
    | Map.null σ = p
    | otherwise  = subst (∅) p
  where
    subst ρ (Parall ps)      = Parall (MSet.map (subst ρ) ps)
    subst ρ (Alt alts)       = Alt (MSet.map (substalt ρ) alts)
    subst ρ (New ns p)       = New ns (subst (ρ ∪ ns) p)
    subst ρ (PiCall pv args) = PiCall pv $ map (nonCapSub ρ σ) args
    subst ρ (Bang p)         = Bang $ subst ρ p

    substalt ρ (π, cont) =
        case π of
            In x xs  -> (In (nonCapSub ρ σ x) xs, subst (ρ ∪ Set.fromList xs) cont)
            Out x xs -> (Out (nonCapSub ρ σ x) (map (nonCapSub ρ σ) xs), subst ρ cont)
            Tau      -> (Tau, subst ρ cont)

nonCapSub :: Set PiName -> NameSubst -> PiName -> PiName
nonCapSub ρ σ x
    | x ∊ ρ     = x
    | otherwise = Map.findWithDefault x x σ

{-|
    Applies a substitution without taking scoping in account.
    Faster than @applySub@ but assumes no-conflict and non-conflicting
    substitution.
-}
blindSub :: NameSubst -> PiTerm -> PiTerm
blindSub σ
    | Map.null σ = id --optimisation for corner case
    | otherwise  = rename (subFun σ)

{-|
    Applies a substitution to a name, returning the same name if it is not in
    the domain of the substitution.
-}
subFun :: NameSubst -> PiName -> PiName
subFun σ x = Map.findWithDefault x x σ

{-|
    Substitutes *bound* names with fresh ones.
    This is useful to maintain the no-conflict invariant when unravelling a
    definition or a bang.
-}
-- This can be made faster if necessary by defining it from scratch instead of
-- reusing @freeNames@, @maxNameId@ and @rename@.
refresh :: NameId -> PiTerm -> (PiTerm, NameId)
refresh nextFree p = refreshWith nextFree (freeNames p) p

refreshWith :: NameId -> Set PiName -> PiTerm -> (PiTerm, NameId)
refreshWith nextFree free p = (p' , 1 + maxNameId p')
  where
    fresh x
        | Set.member x free = x
        | isGlobal x        = x
        | otherwise         = x{unique = nextFree+unique x}

    p' = rename fresh p
