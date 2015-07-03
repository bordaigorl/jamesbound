{- |
    Module      :  Language.PiCalc
    Description :  Syntax and Semantics of pi-calculus
    Copyright   :  Copyright (C) 2013 Emanuele D'Osualdo
    License     :  BSD-like
    Maintainer  :  emanuele.dosualdo@gmail.com

This module defines data structures and functions for the representation of the
syntax and operational semantics of the pi-calculus.

For more information about pi-calculus see
    <https://en.wikipedia.org/wiki/Pi_calculus>.

Another (more theoretical) reference for a quick introduction is

 * Milner, R. 1993. /The polyadic pi-calculus: a tutorial./
   Logic and Algebra of Specification (1993).
   Available at <http://hdl.handle.net/1842/6050>.

This module is not intended to define a pi-calculus style embedded domain
specific language but rather to represent, transform, analyse and interpret
pi-calculus terms. For this reason the interpretation is not tuned for speed and
it is not meant to be used for executing systems but rather to explore the
semantics of the terms.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
--TODO: cleanup exports
module Language.PiCalc (
  -- * Syntax
  -- ** Abstract Syntax Trees and Terms
    module Language.PiCalc.Syntax
  -- ** Parsing
  , module Language.PiCalc.Parser
  -- ** Pretty Printing
  , module Language.PiCalc.Pretty
  -- , module Language.PiCalc.Dot
  -- * Semantics
  , module Language.PiCalc.Semantics
  -- , module Language.PiCalc.Infix
  -- , module Language.PiCalc.Semantics.Cover
  , module Language.PiCalc
) where

import Language.PiCalc.Syntax
import Language.PiCalc.Infix
import Language.PiCalc.Semantics

import Language.PiCalc.Parser
import Language.PiCalc.Pretty
import Language.PiCalc.Dot

import Language.PiCalc.Semantics.Cover

import Data.Set(toList)

#ifdef __GLASGOW_HASKELL__

import GHC.Exts( IsString(..) )

instance IsString PiTerm where
    fromString s =
        case parsePiCalc "<implicit>" s of
            Left e  -> error $ "*** Parsing Error:\n" ++ show e
            Right (ast, gl) ->
                case resolveProg $ (progMap normaliseAST ast, gl) of
                    Left e -> error $ "*** Scoping Error: " ++ e
                    Right (prog, _, _) -> start prog

instance IsString StdNFTerm where
    fromString s = stdNF (fromString s)

#endif

type SourceName = String

-- | Parses a 'PiProg' returning either an error message or a triple with the parsed program
readPiProg :: SourceName -- ^ A string with the name of the source (usually the filename)
           -> String     -- ^ The raw input
           -> Either String (PiProg, NameId, Warnings)
              -- ^ A successful parse returns the program, the next usable 'NameId' and a list of warnings
readPiProg source str =
    case parsePiCalc source str of
        Right (ast, gl) ->
            resolveProg $ (progMap normaliseAST ast, gl)
        Left bad -> Left $ showParseErr bad str

-- TODO: move to Frontend, make readPiProg return ParseError
showParseErr :: ParseError -> String -> String
showParseErr e s =
    sherr ++ "\n\t" ++ ln ++ "\n\t" ++ indic
  where
    pos = errorPos e
    lns = lines s
    ln | null lns = "NO INPUT!"
       | otherwise = lns !! (sourceLine pos - 1)
    pad = replicate (sourceColumn pos - 1) ' '
    indic = pad ++ "^"
    shpos = sourceName pos ++ ":" ++ (show $ sourceLine pos) ++ ":" ++ (show $ sourceColumn pos)
    sherr = shpos ++ ":" ++ (dropWhile (=='\n') $
              showErrorMessages "or" "unknown parse error"
                                "expecting" "unexpected" "end of input"
                               (errorMessages e))

-- TESTING -- 8< -------------------------------------

-- * Testing

norm p =
    case resolveProg (PiProg (normaliseAST p) emptyPiDefs, []) of
        Right (prog, _, _) -> start prog
        Left err -> error $ "Error: " ++ err

gimmeProc s = start $ gimme s

gimme s =
    case parsePiCalc "<commandline>" s of
    Left e  -> error $ "*** Parsing Error:\n" ++ show e
    Right (ast, gl) ->
        case resolveProg (progMap normaliseAST ast, gl) of
            Left e -> error $ "*** Scoping Error: " ++ e
            Right (prog, _, _) -> prog

printscc s = mapM_ putStrLn [
        (show $ map pretty $ toList ns) ++ (show $ pretty (StdNF ps)) |
            (ns, ps) <- s
    ]

-- 8< ------------------------------------------------

