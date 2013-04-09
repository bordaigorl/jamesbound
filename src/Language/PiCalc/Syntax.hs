{- |
Module      :  Language.PiCalc.Syntax
Description :  Abstract Syntax Trees for π-calculus terms
Copyright   :  (c) 2012 Oxford University
License     :  CRAPL

Maintainer  :  emanuele.dosualdo@cs.ox.ac.uk
Stability   :  experimental
Portability :  portable

Abstract Syntax Trees for π-calculus terms
-}
module Language.PiCalc.Syntax(
    PiTerm(..),
    PiPrefix(..),
    PiDefs,
    defsMap,
    normalize,
    isZero,
    zero,
    defsList,
    getDef,
    isSeq,
    -- remove when tested :
    (∥),(⊕), (<!>), (<?>), τ, eAlt,
    example,
    big_example,
    example_defs
  ) where

import qualified Data.Map as Map
import Data.List

data PiTerm procid name =
    Parall [PiTerm procid name]                 -- ^ Parallel composition of @n@ processes.
  | Alt [(PiPrefix name, PiTerm procid name)]   -- ^ Guarded Alternatives.
  | New name (PiTerm procid name)               -- ^ Restriction of a @name@ in a process.
  | PiCall procid [name]                        -- ^ Call to a process identifier with arguments; the identifier should be defined in a @PiDefs@ structure.
  | Bang (PiTerm procid name)                   -- ^ Replication; mostly useful to represent limit configurations.
  -- not sure it's a good idea to include Bang here. Surely it must be included to represent limits.
  deriving (Show, Ord, Eq)

newtype PiDefs procid name = PiDefs {defsMap :: Map.Map procid (PiDef procid name)}
type PiDef p n = ([n], PiTerm p n)


defsList :: PiDefs p n -> [(p, PiDef p n)]
defsList = Map.toList . defsMap

getDef :: (Ord p) => PiDefs p n -> p -> Maybe (PiDef p n)
getDef pidefs p = Map.lookup p $ defsMap pidefs

data PiPrefix name = In name [name]
                   | Out name [name]
                   | Tau
  deriving (Show, Eq, Ord)


zero = Parall []

isZero (Parall []) = True
isZero (Alt []) = True
isZero _ = False

isAlt (Alt _) = True
isAlt _       = False

normalize (PiCall p a) = PiCall p a
normalize (Parall xs) =
    case nxs of
        []  -> zero
        [x] -> x
        ys  -> Parall ys
  where procs = concatMap (depar.normalize) xs
        nxs = filter (not.isZero) procs
        depar (Parall xs) = xs
        depar p           = [p]
normalize (Alt []) = zero
normalize (Alt xs) = Alt $ map (\(p,pr)->(p, normalize pr)) xs
normalize (New n p)
    | isZero np  = zero
    | otherwise  = New n np
  where np =  normalize p
normalize (Bang p)
    | isZero np  = zero
    | otherwise  = Bang np
  where np =  normalize p



example:: PiTerm String String
example = Parall [ (New "a" (Alt [ (Out "a" [], (Alt [(Tau, zero), (In "c" [], zero)]))
                                 , (In "b" ["x"], Alt [(Out "x" ["a"], zero)])
                                 , (Tau, Parall [zero, Parall [zero, PiCall "P" ["a","x"]]])]))
                 , Alt [(Out "b" ["c"], zero)]
                 ]
big_example = Alt [(Out "c" ["d","e"], Parall [example,example]), (Tau, Parall [PiCall "P" ["b"],example])]

example_defs = PiDefs $ Map.fromList [("P",([],normalize example)),("B",(["x","y"],normalize big_example))]

-- Syntax HELPERS, not sure you want to export these
(Parall l1) ∥ (Parall l2) = Parall $ l1++l2
(Parall l) ∥ p = Parall $ p:l
p ∥ (Parall l) = Parall $ p:l
p ∥ p' = Parall [p,p']

infixr ⊕
(p,pr) ⊕ (Alt l) = Alt $ (p,pr):l
eAlt = Alt []

n <!> l = Out n l
n <?> l = In n l
τ = Tau

-----------------------------------------------------------
-- * Predicates on processes
-----------------------------------------------------------

-- | Determine if it is a sequential process,
--   namely non-zero alternatives, bangs, or calls
isSeq :: PiTerm p n -> Bool
isSeq (Parall _) = False
isSeq (Alt [])   = False
isSeq (New _ _)  = False
isSeq _          = True
