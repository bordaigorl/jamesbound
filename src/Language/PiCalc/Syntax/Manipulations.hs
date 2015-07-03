module Language.PiCalc.Syntax.Manipulations(
      resolveProg
    , Warnings
) where

import Language.PiCalc.Syntax.AST
import Language.PiCalc.Syntax.Term

import Control.Monad
import Control.Monad.State
import Control.Monad.Maybe

import Data.List (intercalate)
import Data.Map(Map)
import qualified Data.Map as Map
import qualified Data.MultiSet as MSet
import qualified Data.Set as Set
import Data.Set.Infix

data ClashState = Clash {
      scope    :: Map String [PiName]
    , nextFree :: NameId
    , warnings :: Warnings
    , errMsg   :: String
    , inDef    :: Maybe PiPVar
} deriving Show

type Warnings = [String]

initClash = Clash {scope = Map.empty, nextFree = 0, warnings = [], errMsg = "", inDef=Nothing}


{-|
    Resolves name clashes deriving a clash-free program with names represented
    by PiName records.

    It additionally checks that no definition contains free names and that all
    the process variables are defined. This should only be used to validate user
    input once; the semantics then preserves validity of terms.

    The return value is:
      * @Right (prog, next, warnings)@ where
          - the checks are passed
          - the alpha-renamed program is @prog@
          - @warnings@ is a list of possible problems (e.g. shadowing of variables)
          - @next@ is the next free unique id for a name (of type @NameId@)
      * @Left errMsg@ if invalid with error message
-}
resolveProg :: (PiProgAST String, [String]) -> Either String (PiProg, NameId, Warnings)
resolveProg (prog, glob) =
    case runState (runMaybeT $ solveProg prog glob) initClash of
        (Nothing, clash)
            | null $ warnings clash -> Left $ errMsg clash
            | otherwise ->
                Left $
                    errMsg clash
                    ++ "\n  There were warnings too:"
                    ++ concatMap ("\n    Warning: "++) (warnings clash)
        (Just p, clash) -> Right (p, nextFree clash, warnings clash)



-- TODO: resolveProc for a single process, not checking existance of process definitions

solveProg :: PiProgAST String -> [String] -> MaybeT (State ClashState) PiProg
solveProg PiProg{start=startProc, defs=procDefs} glob =
     do sequence_ $ map allocGlob glob
        gns       <- gets scope
        start'    <- alphaRename startProc
        procDefs' <- sequence [alphaRenameDef gns d | d <- Map.toAscList procDefs ]
        return $ PiProg{start=start', defs=Map.fromAscList procDefs'}
  where

    alphaRenameDef gns (pvar, (args,proc)) =
         do when (not $ allDistinct args) $
                giveUp "overlapping formal arguments"
            args' <- resetScope pvar gns args
            proc' <- alphaRename proc
            return (pvar, (args', proc'))


    resetScope ct gns xs =
         do modify (\c->c{inDef=Just ct})
            c  <- get
            ns <- sequence $ map alloc xs
            let bindings = zipWith (\x y->(x,[y])) xs ns
            modify (\c->c{scope=Map.union gns $ Map.fromList bindings})
            return ns

    giveUp s = modify (\c->c{errMsg=ctxtfy c s}) >> fail s
    warn s = modify (\c->c{warnings=((ctxtfy c s):warnings c)})

    ctxtfy c s = s ++ " in " ++ ctxtOf c

    lookupVar x =
        do  c <- get
            case lookupName x $ scope c of
                []    ->
                    case inDef c of
                        Nothing -> allocGlob x
                        Just pv -> giveUp $ "undeclared variable "++(show x)
                (n:_) -> return n

    lookupName x = Map.findWithDefault [] x

    allocGlob x =
         do c <- get
            let i = nextFree c
            let n' = PiName{static=x, ctxt=ctxtOf c, unique=i, isGlobal=True}
            put $ c{nextFree = i+1, scope=Map.alter (pushBinding n') x (scope c)}
            return n'
    alloc x =
         do s <- gets scope
            when (not $ null $ lookupName x s) $
                warn ("variable "++show x++" is shadowed")
            c <- get --horrible! just to keep the warning...
            let i = nextFree c
            let n' = PiName{static=x, ctxt=ctxtOf c, unique=i, isGlobal=False}
            put $ c{nextFree = i+1, scope=Map.alter (pushBinding n') x (scope c)}
            return n'

    dealloc x =
        do c <- get
           case lookupName x $ scope c of
               [] -> giveUp $ "variable "++show x++" not in scope"
               (_:ns) -> put $ c{scope=Map.insert x ns (scope c)}

    pushBinding n Nothing = Just [n]
    pushBinding n (Just ns) = Just (n:ns)

    ctxtOf Clash{inDef=Nothing} = "top-level"
    ctxtOf Clash{inDef=Just pv} = pv

    alphaRename (Parall procs) =
         do procs' <- sequence $ map alphaRename $ MSet.elems procs
            return $ Parall $ MSet.fromList procs'
    alphaRename (Alt alts)     =
         do alts' <- sequence $ map renamePre $ MSet.elems alts
            return $ Alt $ MSet.fromList alts'
    alphaRename (New xs_set proc) =
         do xs'   <- sequence [alloc x | x <- xs]
            proc' <- alphaRename proc
            sequence_ [dealloc x | x <- xs]
            return $ New (Set.fromList xs') proc'
      where xs = Set.elems xs_set
    alphaRename c@(PiCall pvar args) =
         do when (Nothing==pdef) $ warn $ "process " ++ (show pvar) ++ " not defined, but called"
            case pdef of
                Just (vars, _) | length vars /= length args ->
                        giveUp $ "the call " ++ (showCall pvar args)
                                             ++ " has the wrong number of arguments (expected "
                                             ++ (show $ length vars) ++ ")"
                _ -> return ()
            ns <- sequence [lookupVar x | x <- args]
            return $ PiCall pvar ns
      where pdef = Map.lookup pvar procDefs
            -- case (Map.lookup pvar procDefs) of
            --     Nothing ->
            --         giveUp $ "process " ++ (show pvar) ++ " not defined, but called"
            --     Just (vars, _)
            --         | length vars /= length args ->
            --             giveUp $ "the call " ++ (show $ pretty c)
            --                                  ++ " has the wrong number of arguments (expected "
            --                                  ++ (show $ length vars) ++ ")"
            --         | otherwise ->
            --              do ns <- sequence [lookupVar x | x <- args]
            --                 return $ PiCall pvar ns
    alphaRename (Bang proc)    =
         do proc' <- alphaRename proc
            return $ Bang proc'

    renamePre (pre, cont) =
        case pre of
            Tau ->
                 do cont' <- alphaRename cont
                    return $ (Tau, cont')
            In x xs
                | allDistinct xs ->
                     do n <- lookupVar x
                        ns <- sequence $ [alloc x | x <- xs]
                        cont' <- alphaRename cont
                        sequence_ $ [dealloc x | x <- xs]
                        return (In n ns, cont')
                | otherwise ->
                    giveUp $ "variable(s) in input prefix must be all distinct!"
                -- Left $ "variable "++(show $ pretty x) ++" in prefix "++(show $ pretty pre) ++" not in scope."
            Out x xs ->
                 do n <- lookupVar x
                    ns <- sequence $ [lookupVar x | x <- xs]
                    cont' <- alphaRename cont
                    return (Out n ns, cont')


    allDistinct = dist (∅)
        where dist seen (x:xs)
                | x ∊ seen  = False
                | otherwise = dist (Set.insert x seen) xs
              dist s [] = True

showCall pvar args = pvar ++ "[" ++ (intercalate "," args) ++ "]"
