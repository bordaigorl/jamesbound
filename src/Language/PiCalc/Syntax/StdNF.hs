module Language.PiCalc.Syntax.StdNF(
    StdNFTerm(..),
    StdFactor(..),
    isValidStdNF,
    seqFromStd,
    stdToTerm,
    isStdZero,
    stdNF,
    nf,
    mergeStd,
    renameStd,
    distFactors,
    allNFnames,
    stdNFcc,
    depth,
    restrNF,
    restrNF',
    classifyNames
) where

import Language.PiCalc.Syntax.Term

import Data.List (partition, minimumBy)
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set
import Data.MultiSet(MultiSet)
import qualified Data.MultiSet as MSet

{-| A data structure representing a term in standard normal form.
    It stands for a parallel composition of sequential processes.
-}
newtype StdNFTerm = StdNF (MultiSet StdFactor)
    deriving (Show, Read)

instance Eq StdNFTerm where
    (StdNF s) == (StdNF t) = all2 eq (MSet.toAscOccurList s) (MSet.toAscOccurList t)
      where
        all2 _    []     []     = True
        all2 (~~) (x:xs) (y:ys) = x ~~ y && all2 (~~) xs ys
        all2 _    _      _      = False

        eq (f1,o1) (f2,o2) =
               o1 == o2
            && seqTerm f1 == seqTerm f2
            && restrNames f1 == restrNames f2
            -- last two necessary because of Eq instances of StdFactor


{- |
    Important note about the @StdFactor@ data structure: it only makes sense
    under the no-conflict assumption on the @StdNFTerm@ it belongs to. In
    particular, if @StdFactor p ns@ and @StdFactor p' ns'@ are two @StdFactor@s
    of a @StdNFTerm@ @q@, then if @p == p'@ then @ns@ and @ns'@ must be equal too.
    This is necessarily true when @q = stdNF t@ where @t@ satisfies no-conflict.

    Invariants for @StdFactor p ns@:
      * @p@ is sequential,
      * all the names in @ns@ are free names of @p@.
-}
data StdFactor = StdFactor {seqTerm::PiTerm, restrNames::Set PiName}
    deriving (Show, Read)

instance Ord StdFactor where
    a <= b = seqTerm a <= seqTerm b

instance Eq StdFactor where
    a == b = seqTerm a == seqTerm b

-- | just the multiset of sequential processes
seqFromStd :: StdNFTerm -> MultiSet PiTerm
seqFromStd (StdNF m) = MSet.map seqTerm m

-- | Standard normal form of a term. No renaming is applied, names are preserved.
stdNF :: PiTerm -> StdNFTerm
stdNF p = StdNF stdp
  where
    stdp = MSet.mapMonotonic (\(p, x, _)-> StdFactor p x) (stdzr p)
        -- Assuming lexicographic ordering between tuples this is monotonic.
        -- Otherwise replace with @MSet.map@

    stdzr p | isZero p = MSet.empty
    stdzr p | isSeq p = MSet.singleton (p, Set.empty, freeNames p)
    stdzr (Parall ps) = MSet.unionsMap stdzr ps
    stdzr (New ns p) = MSet.map addnames $ stdzr p
      where addnames (p', ns', fns) = (p', Set.union (Set.intersection ns fns) ns', Set.difference fns ns)

-- | Normal form: transforms a term @t@ in a congruent standard normal form term
--                which has all sub-terms in standard normal form.
nf :: PiTerm -> PiTerm
nf p = stdToTerm $ StdNF fcts'
  where
    StdNF fcts = stdNF p
    fcts' = MSet.map factorNF fcts
    factorNF (StdFactor p x) = StdFactor (mapConts nf p) x

    mapConts f (Alt alts) = Alt $ MSet.map (mapCont f) alts
    mapConts f (Bang   p) = Bang $ f p
    mapConts f p = p
    mapCont f (act, p) = (act, f p)

isValidStdNF :: StdNFTerm -> Bool
isValidStdNF (StdNF ps) = and $ map isValid $ MSet.distinctElems ps
    where isValid (StdFactor p n) = isSeq p && n `Set.isSubsetOf` (freeNames p)

stdToTerm :: StdNFTerm -> PiTerm
stdToTerm (StdNF ps)
    | Set.null ns = par
    | otherwise   = New ns par
  where ns = Set.unions [restrNames f | f <- MSet.distinctElems ps]
        par | MSet.size ps == 1 = let [p] = MSet.elems ps in seqTerm p
            | otherwise         = Parall $ MSet.map seqTerm ps


isStdZero :: StdNFTerm -> Bool
isStdZero (StdNF s) = MSet.null s

-- | apply (blindly) a renaming of the names in the normal form.
--   This is only sound when the renaming is injective
renameStd :: (PiName -> PiName) -> StdNFTerm -> StdNFTerm
renameStd namemap (StdNF s) = StdNF $ MSet.map renameFact s
  where
    renameFact f = f { seqTerm = rename namemap (seqTerm f)
                     , restrNames = Set.map namemap (restrNames f)}

-- | the distinct factors of a process in a standard normal form
distFactors :: StdNFTerm -> [StdFactor]
distFactors (StdNF ps) = MSet.distinctElems ps

distSeq = MSet.distinctElems

-- | merges two standard normal forms, assuming the two processes were part of
-- the same standard form. This means a stronger assumption than no-conflict:
-- the protected names of the two processes may overlap, but when they do they are
-- identified.
mergeStd :: StdNFTerm -> StdNFTerm -> StdNFTerm
mergeStd (StdNF ps1) (StdNF ps2) =
    StdNF $ MSet.union ps1 ps2

allNFnames :: StdNFTerm -> Set PiName
allNFnames s = Set.unions [restrNames f | f <- distFactors s]

-- | Connected components of the communication topology of a standard normal form
stdNFcc :: StdNFTerm -> [(Set PiName, MultiSet StdFactor)]
stdNFcc (StdNF ps) = foldr ins [] $ MSet.toOccurList ps
  where
    ins (s,n) cur =
        case break (connected s) cur of
            (rest, (ns, ms):rest') ->
                let ns' = Set.union ns (restrNames s)
                    ms' = MSet.insertMany s n ms
                in  rest++((ns',ms'):rest')
            (_, []) -> (restrNames s, MSet.fromOccurList [(s,n)]):cur
    connected s (ns, _) = not $ Set.null $ Set.intersection (restrNames s) ns

{-
-- BEWARE: these only work on single strongly conn comp
betterDepth (StdNF ps) = minimum' $ map (dummydepth psl) sortings
  where
    (glob,norm,loc) = classifyNames ps
    sortings = [ Set.toList glob ++ p ++ Set.toList loc | p <- permutations norm]
    psl = MSet.distinctElems ps
    minimum' [] = 0
    minimum' x = minimum x

unoptDepth (StdNF ps) = minimum' $ map (dummydepth psl) (permutations names)
  where
    names = Set.unions $ map restrNames psl
    psl = MSet.distinctElems ps
    minimum' [] = 0
    minimum' x = minimum x

dummydepth _  [] = 0
dummydepth [] _  = 0
dummydepth ps (x:rest) = max (if null onlyx then 0 else 1) $
                             (if null remx then 0 else 1) + dummydepth (map delx remaining) rest
  where
    remx = filter hasx remaining
    (onlyx, remaining) = partition isx ps
    isx p = [x] == Set.elems (restrNames p)
    hasx p = Set.member x (restrNames p)
    delx p =  p{restrNames=Set.delete x $ restrNames p}
-}

restrNF :: StdNFTerm -> PiTerm
restrNF = fst . restrNF'

depth :: StdNFTerm -> Integer
depth   = snd . restrNF'


restrNF' s@(StdNF ps) = (normaliseAST rs, d)
  where
    rs = prl $ map fst restrComps
    d = maximum' $ map snd restrComps
    restrComps = [ restrFrag fr | (_, fr) <- stdNFcc s ]

    maximum' [] = 0
    maximum' x  = maximum x

restrFrag fr = optimal $ map (restrForm $ MSet.elems fr) sortings
  where
    (glob,norm,loc) = classifyNames fr
    sortings = [ Set.toList glob ++ p ++ Set.toList loc | p <- permutations norm]
    optimal [] = (stdToTerm (StdNF fr), 0)
    optimal x = minimumBy cmpDepth x
    cmpDepth a b = compare (snd a) (snd b)

restrForm ps  [] = (prl $ map seqTerm ps, 0)
restrForm [] _  = (zero, 0)
restrForm ps (x:rest)
    | noMoreX   = (parall (new [x] (prl $ map seqTerm onlyx)) restrest, max donlyx d)
    | otherwise = (new [x] (prl $ restrest:map seqTerm onlyx), max donlyx (1+d))
  where
    donlyx = if null onlyx then 0 else 1
    (restrest, d) = restrForm (map delx remaining) rest
    (onlyx, remaining) = partition isx ps
    noMoreX = not $ any hasx remaining
    isx  p  = [x] == Set.elems (restrNames p)
    hasx p  = Set.member x (restrNames p)
    delx p  = p{restrNames=Set.delete x $ restrNames p}


classifyNames ps = (globals, normal, locals)
  where
    globals
        | null names = Set.empty
        | otherwise = foldr1 Set.intersection names
    nonglobals = Set.difference (Set.unions names) globals
    (locals, normal) = Set.partition (onceIn names) nonglobals
    onceIn [] _ = False
    onceIn (ns:rest) x
        | Set.member x ns = alreadyonce rest x
        | otherwise       = onceIn rest x
    alreadyonce rest x = all (Set.notMember x) rest
    names = map restrNames $ MSet.distinctElems ps

permutations ns
    | Set.null ns = [[]]
    | otherwise  =
        [ x:xs | x <- Set.elems ns, xs <- permutations $ Set.delete x ns ]
