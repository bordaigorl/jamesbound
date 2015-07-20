{- |
    Module      :  Language.PiCalc.Syntax
    Description :  Abstract Syntax Trees for pi-calculus terms
    Copyright   :  Copyright (C) 2013 Emanuele D'Osualdo
    License     :  GPLv2
    Maintainer  :  emanuele.dosualdo@gmail.com
    Stability   :  experimental
    Portability :  portable

Abstract Syntax Trees for pi-calculus terms
-}
module Language.PiCalc.Syntax.AST(
    -- * Types for the abstract syntax tree
      PiAST(..)
    , PiPrefix(..)
    , PiDefsAST(..)
    , PiDefAST
    , PiProgAST(..)
    , PiPVar
    -- * Basic manipulation
    , normaliseAST
    , rename
    , emptyProg
    , progMap
    , getDef
    , defsList
    , getGlobals
    , freeNames
    , allNames
    , allRestr
    , allProcVar
    , factorCont
    -- * Predicates
    , isZero
    , isSeq
    , isIn
    , isOut
    , isTau
    -- * Construction
    , zero
    , parall
    , paralls
    , new, prl, alt
    , emptyPiDefs
    , makePiDefs
  ) where

import Data.Map(Map)
import qualified Data.Map as Map
import Data.MultiSet(MultiSet)
import qualified Data.MultiSet as MSet
import Data.Set(Set)
import qualified Data.Set as Set

data PiAST name =
    Parall (MultiSet (PiAST name))             -- ^ Parallel composition of @n@ processes.
  | Alt (MultiSet (PiPrefix name, PiAST name)) -- ^ Guarded Alternatives.
  | New (Set name) (PiAST name)                -- ^ Restriction of a @name@ in a process.
  | PiCall PiPVar [name]                       -- ^ Call to a process identifier with arguments; the identifier should be defined in a @PiDefsAST@ structure.
  | Bang (PiAST name)                          -- ^ Replication; mostly useful to represent limit configurations.
  -- not sure it's a good idea to include Bang here. Surely it must be included to represent limits.
  deriving (Show, Ord, Eq, Read)

data PiPrefix name = In name [name]
                   | Out name [name]
                   | Tau
  deriving (Show, Eq, Ord, Read)

-- | The type of a process identifier
type PiPVar = String

rename :: (Ord a, Ord b) => (a -> b) -> PiAST a -> PiAST b
rename f (Parall ps)    = Parall (MSet.map (rename f) ps)
rename f (Alt  alts)    = Alt (MSet.map (\(pre,cont)->(fmapPre pre, rename f cont)) alts)
    where fmapPre (In x xs)   = In (f x) (map f xs)
          fmapPre (Out x xs)  = Out (f x) (map f xs)
          fmapPre Tau         = Tau
rename f (New ns  p)    = New (Set.map f ns) (rename f p)
rename f (PiCall pv ns) = PiCall pv (map f ns)
rename f (Bang p)       = Bang (rename f p)


type PiDefsAST name = Map.Map PiPVar (PiDefAST name)

type PiDefAST name = ([name], PiAST name)

emptyPiDefs :: PiDefsAST name
emptyPiDefs = Map.empty

makePiDefs :: [(PiPVar, PiDefAST name)] -> PiDefsAST name
makePiDefs = Map.fromList

defsList :: PiDefsAST n -> [(PiPVar, PiDefAST n)]
defsList = Map.toList -- . defsMap

getDef :: PiDefsAST n -> PiPVar -> Maybe (PiDefAST n)
getDef pidefs p = Map.lookup p pidefs

getGlobals :: Ord name => PiDefsAST name -> Set name
getGlobals defs =
    Set.unions
        [ (Set.difference fn argset) |
            (_,(args, t)) <- defsList defs,
            let fn = freeNames t,
            let argset = Set.fromList args
        ]

data PiProgAST n = PiProg {start :: PiAST n, defs :: PiDefsAST n}
  deriving (Show, Eq)

emptyProg = PiProg zero emptyPiDefs

progMap :: (PiAST name -> PiAST name) -> PiProgAST name -> PiProgAST name
progMap f (PiProg s d) =
    PiProg (f s) (Map.map (\(a,pd)->(a,f pd)) d)


factorCont :: (PiPrefix name,PiAST name) -> PiAST name
factorCont = snd


freeNames :: Ord name => PiAST name -> Set name
freeNames (Parall ps) = Set.unions (map freeNames $ MSet.distinctElems ps)
freeNames (Alt alts) = Set.unions (map freePreNames $ MSet.distinctElems alts)
  where
    freePreNames (In x xs, cont) = Set.insert x $ Set.difference (freeNames cont) (Set.fromList xs)
    freePreNames (Out x xs, cont) = Set.union (freeNames cont) (Set.fromList $ x:xs)
    freePreNames (Tau, cont) = freeNames cont
freeNames (New ns proc) = Set.difference (freeNames proc) ns
freeNames (PiCall pv xs) = Set.fromList xs
freeNames (Bang proc) = freeNames proc

allNames :: Ord name => PiAST name -> Set name
allNames (Parall ps) = Set.unions [allNames p | p <- MSet.distinctElems ps]
allNames (Alt  alts) = Set.unions [Set.union (preNames pre) (allNames cont) | (pre, cont) <- MSet.distinctElems alts]
  where
    preNames (In x xs) = Set.insert x $ Set.fromList xs
    preNames (Out x xs) = Set.insert x $ Set.fromList xs
    preNames Tau = Set.empty
allNames (New ns  p) = Set.union (allNames p) ns
allNames (PiCall _ args) = Set.fromList args
allNames (Bang p) = allNames p

allRestr :: Ord name => PiAST name -> Set name
allRestr (Parall ps) = Set.unions [allRestr p | p <- MSet.distinctElems ps]
allRestr (Alt  alts) = Set.unions [allRestr cont | (_, cont) <- MSet.distinctElems alts]
allRestr (New ns  p) = Set.union (allRestr p) ns
allRestr (PiCall _ _) = Set.empty
allRestr (Bang p) = allRestr p

allProcVar :: PiAST name -> Set PiPVar
allProcVar (Parall ps) = Set.unions [allProcVar p | p <- MSet.distinctElems ps]
allProcVar (Alt  alts) = Set.unions [allProcVar cont | (_, cont) <- MSet.distinctElems alts]
allProcVar (New ns  p) = allProcVar p
allProcVar (PiCall pvar _) = Set.singleton pvar
allProcVar (Bang p) = allProcVar p


{- |
    Normalisation of abstract syntax.
    This avoids redundancy in the data structure resulting from nested
    parallels, irrelevant zero processes or nested restrictions of disjoint
    names.

    Some examples:

    > normaliseAST (prl [prl [p], zero, prl [q, r]])  == prl [p, q, r]
    > normaliseAST (prl [alt []])                     == zero
    > normaliseAST (new [x] (new [y] zero))           == new [x,y] zero

    when @p@ and @q@ are not @zero@ and @x/=y@.
    Note that @new xs zero@ is not normalised to @zero@.
-}
normaliseAST :: (Ord name) => PiAST name -> PiAST name
normaliseAST (PiCall pvar args) = PiCall pvar args
normaliseAST (Parall procs)
    | MSet.null normProcs = zero -- just in case zero changes representation
    | MSet.size normProcs == 1 = head $ MSet.elems normProcs
    | otherwise = Parall normProcs
  where procs' = MSet.unionsMap (depar.normaliseAST) procs
        normProcs = MSet.filter (not.isZero) procs'
        depar (Parall procs) = procs
        depar p              = MSet.singleton p
normaliseAST (Alt procs)
    | MSet.null procs = zero
    | otherwise       = Alt $ MSet.map (\(p,pr)->(p, normaliseAST pr)) procs
normaliseAST (New ns p)
    | isZero np   = zero
    | Set.null ns = np
    | otherwise   = mergeNew np
  where np =  normaliseAST p
        mergeNew (New ns' p')
            | Set.null (Set.intersection ns ns') = New (Set.union ns ns') p'
        mergeNew proc = New ns proc
normaliseAST (Bang p)
    | isZero np  = zero
    | otherwise  = Bang np
  where np =  normaliseAST p

-----------------------------------------------------------
-- * Construction
-----------------------------------------------------------

zero :: PiAST name
zero = Parall (MSet.empty)

-- Not sure about these names...export them or not?
prl :: (Ord name) => [PiAST name] -> PiAST name
prl = Parall.(MSet.fromList)

alt :: (Ord name) => [(PiPrefix name, PiAST name)] -> PiAST name
alt = Alt.(MSet.fromList)

new :: Ord name => [name] -> PiAST name -> PiAST name
new [] p = p
new ns p
  | isZero p  = zero
  | otherwise = insNew p
  where
    xs = Set.fromList ns
    insNew (New ys p')
        | Set.null $ Set.intersection xs ys = New (Set.union xs ys) p'
    insNew p = New xs p

parall :: (Ord name) => PiAST name -> PiAST name -> PiAST name
p `parall` p' | isZero p = p'
p `parall` p' | isZero p' = p
(Parall l1) `parall` (Parall l2) = Parall $ MSet.union l1 l2
(Parall l) `parall` p = Parall $ MSet.insert p l
p `parall` (Parall l) = Parall $ MSet.insert p l
p `parall` p' = Parall $ MSet.fromList [p,p']

paralls :: (Ord name) => [PiAST name] -> PiAST name
paralls = foldr parall zero
-----------------------------------------------------------
-- * Predicates on processes
-----------------------------------------------------------

-- | Determine if a term is a sequential process,
--   namely non-zero alternatives, bangs, or calls
isSeq :: PiAST name -> Bool
isSeq (Parall _)  = False
isSeq (Alt procs) = not $ MSet.null procs
isSeq (New _ _)   = False
isSeq _           = True


-- | Determine if a term is a representation for the zero process
isZero :: PiAST name -> Bool
isZero (Parall procs) = MSet.null procs
isZero (Alt procs) = MSet.null procs
isZero _ = False

-- | Determines if the root constructor is @Alt@.
isAlt :: PiAST name -> Bool
isAlt (Alt _) = True
isAlt _       = False

isIn (In _ _, _) = True
isIn _ = False

isOut (Out _ _, _) = True
isOut _ = False

isTau (Tau, _) = True
isTau _ = False


isGuarded :: Eq name => PiAST name -> Bool
isGuarded (Alt alts) = any nonTau $ MSet.distinctElems alts
  where nonTau (pre,_) = pre /= Tau
isGuarded _          = False

-- example:: PiAST String
-- example = prl [ (new ["a"] (alt [ (Out "a" [], (alt [(Tau, zero), (In "c" [], zero)]))
--                                  , (In "b" ["x"], alt [(Out "x" ["a"], zero)])
--                                  , (Tau, prl [zero, prl [zero, PiCall "P" ["a","x"]]])]))
--                  , alt [(Out "b" ["c"], zero)]
--                  ]
-- big_example = alt [(Out "c" ["d","e"], prl [example,example]), (Tau, prl [PiCall "P" ["b"],example])]
