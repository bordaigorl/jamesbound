module Language.PiCalc.Syntax.Term(
      NameId
    , PiName(..)
    , PiTerm
    , PiPrefTerm
    , PiProg
    , PiDefs
    , PiDef
    , noName
    , maxNameId
    , nestRestr
    , nestPrl
    , numSeq
    , module AST
) where

-- TODO: polish exports, redefining AST function so they are restricted to PiTerm.
import qualified Language.PiCalc.Syntax.AST as AST hiding (PiAST)
import Language.PiCalc.Syntax.AST

import qualified Data.Set as Set
import qualified Data.MultiSet as MSet

type NameId = Int

{-|
    Data structure to represent alpha renamed names.
-}
data PiName = PiName {
      -- TODO: change ctxt :: (Int, Int) = position in the source of restriction
      --       and maybe rename to creationPt ?
      -- shall unique be Either String NameId replacing isGlobal?
      ctxt::String -- ^ a string representing the definition in which the name is used
    , static::String -- ^ a string holding the original name used in the code
    , unique::NameId -- ^ a number uniquely identifying the name in the term
    , isGlobal::Bool -- ^ whether the name is global or not (public top-level)
} deriving (Show, Read)

-- The order is (glob, static) then (nonGlob, unique)
instance Ord PiName where
    n <= n' =
        case (isGlobal n, isGlobal n') of
            (True , True ) -> static n <= static n'
            (False, False) -> unique n <= unique n'
            (False, True ) -> False
            (True , False) -> True

instance Eq PiName where
    n == n' =
        case (isGlobal n, isGlobal n') of
            (True , True ) -> static n == static n'
            (False, False) -> unique n == unique n'
            _ -> False


noName = PiName {ctxt = "", static = "", unique = error "Name not ensured to be unique!", isGlobal = False}

maxNameId :: PiTerm -> NameId
maxNameId p
    | Set.null names = 0
    | otherwise      = unique $ Set.findMax names
  where names = allNames p

-- | A term in conflict-free form: names are represented with @PiName@ records and
-- process variables by strings. It is assumed to be a normalised AST.
type PiTerm = PiAST     PiName
type PiPrefTerm = (PiPrefix PiName, PiTerm)
type PiProg = PiProgAST PiName
type PiDefs = PiDefsAST PiName
type PiDef  = PiDefAST  PiName


nestRestr :: PiTerm -> Int
nestRestr (Parall ps) = maximum $ 0:[nestRestr p | p <- MSet.distinctElems ps]
nestRestr (New ns  p) = (Set.size ns) + (nestRestr p)
nestRestr _ = 0


-- | This only really makes sense on fragments
nestPrl :: PiTerm -> Int
nestPrl (Parall ps) = maximum $ 0:[nestPrl p | p <- MSet.distinctElems ps]
nestPrl (New ns (Parall ps)) = maximum $ (MSet.size ps):[nestPrl p | p <- MSet.distinctElems ps]
nestPrl _ = 1

numSeq :: PiTerm -> Int
numSeq p | isZero p = 0
numSeq (Parall ps) = sum [numSeq p | p <- MSet.distinctElems ps]
numSeq (New ns  p) = numSeq p
numSeq _ = 1

