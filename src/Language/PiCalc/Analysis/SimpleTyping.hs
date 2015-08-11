{- |
    Module      :  SimpleTyping
    Description :  Simple Types inference
    Copyright   :  (c) 2014 Oxford University
    License     :  CRAPL

    Maintainer  :  emanuele.dosualdo@cs.ox.ac.uk
    Stability   :  experimental

Type inference for simple types.

-}
module Language.PiCalc.Analysis.SimpleTyping(
    -- * Type inference
      TVar(..)
    , TypeC(..)
    , ArityC
    , ArityError
    , unifyTypes
    , onlyNames
    , isNameTvar
    -- * Base type classes and typing environments
    , BVar
    , BTypeClasses(..)
    , allBVars
    , allBVarsSet
    , getRepr
    , getReprArg
    , getBVarNames
    , getTypeAnnot
    , tvarsToNames
    , typeClasses
    , buildTypes
    , buildTypingEnv
) where

import Language.PiCalc.Syntax

import Data.List(partition)

import Data.Set(Set)
import qualified Data.Set as Set
import Data.Set.Infix
import Data.Map(Map)
import qualified Data.Map as Map
import qualified Data.MultiSet as MSet

import Data.Maybe(mapMaybe)
import Control.Monad
import Control.Monad.State

-- | Type variable representation,
data TVar = NameType {tvarName::PiName}    -- name
          | ArgType {tvarName::PiName, tvarArity::Int} -- name/arg position
            -- to support calls add PVarType PArgType
    deriving (Eq, Show, Ord)

isNameTvar (NameType _) = True
isNameTvar _            = False

type ArityC = Maybe Int
type TypeC = [(ArityC, Set TVar)]

type ArityError = (Int, Int, [PiName])
-- ^ Expected arity, found arity, guilty names
--
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
            let tvars'' = tvars ∪ tvars'
                diff    = tvars \\ tvars'
                new'    = (onlyNames a, onlyNames b):new
            merge arity'' tvars'' new' rest

    mergeArities  Nothing  t1  Nothing  t2 = return (Nothing, (∅), (∅))
    mergeArities (Just  n) t1  Nothing  t2 = return (Just n, t1, t2 \\ t1 )
    mergeArities  Nothing  t1 (Just  n) t2 = return (Just n, t1 \\ t2, t2 )
    mergeArities (Just n1) t1 (Just n2) t2
        | n1 == n2  = return (Just n1, t1 \\ t2, t2 \\ t1)
        | otherwise = arityError n1 n2 tvars


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

-----------------------------------------------------------
-- * Base type classes from simple types
-----------------------------------------------------------

type BVar = Int

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
    Map.mapKeysMonotonic tvarName $
    Map.filterWithKey (\x _ -> isNameTvar x) $
    tvar2bvar btcl

tvarsToNames :: Set TVar -> Set PiName
tvarsToNames tvs = Set.map tvarName $ Set.filter isNameTvar tvs

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

buildTypes :: BTypeClasses -> Map BVar (Maybe [BVar])
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

