{- |
    Module      :  Language.PiCalc.Parser
    Description :  A Parser for pi-calculus
    Copyright   :  Copyright (C) 2013 Emanuele D'Osualdo
    License     :  BSD-like
    Maintainer  :  emanuele.dosualdo@gmail.com

A Parser for pi-calculus based on @Parsec@.
-}
module Language.PiCalc.Parser(
      Parser
    , parsePiCalc
    , parsePiCalcTerm
    , piProg
    , piTerm
    , sourceLine
    , sourceColumn
    , sourceName
    , module Text.Parsec.Error
) where

import Language.PiCalc.Syntax.AST

import Text.Parsec
import Text.Parsec.Combinator
import Text.Parsec.String
import Text.Parsec.Char
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (javaStyle)
import Text.Parsec.Error

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.MultiSet as MSet

parsePiCalc :: SourceName -> String -> Either ParseError (PiProgAST String, [String])
parsePiCalc = parse piProg

parsePiCalcTerm :: SourceName -> String -> Either ParseError (PiAST String)
parsePiCalcTerm = parse piTerm

piLang = javaStyle
              { P.commentLine = "//"
              , P.caseSensitive = True
              , P.identStart = lower <|> oneOf "'_"  -- identifiers are only names, process variables are treated separately
              -- , P.identLetter    = alphaNum <|> oneOf "_':"
              , P.opLetter = oneOf "" -- no custom operators in this language!
              , P.reservedOpNames = ["|", "‖", "+", "!", "?",":=", "*"]
              , P.reservedNames = ["new", "ν", "zero", "tau", "τ", "#global"]
              }

P.TokenParser{
             P.identifier = pidentif
           , P.lexeme = lexeme
           , P.reservedOp = operator
           , P.reserved = reserved
           , P.commaSep = commaList
           , P.commaSep1 = commaList1
           , P.semi = semi
           , P.symbol = symbol
           , P.dot = dot
           , P.parens   = parens
           , P.braces   = braces
           , P.brackets = brackets
           , P.angles   = real_angles
           , P.whiteSpace = skipSpaces } = P.makeTokenParser piLang

-- operator = symbol
parSym = operator "|" <|> operator "‖" <?> "parallel"
altSym = operator "+" <?> "alternative (+)"

defSym = operator ":="
newSym = reserved "new" <|> (string "ν" >> skipSpaces) <?> "new"
tauSym = reserved "tau" <|> reserved "τ" <?> "tau"

bangSym = operator "*"

zeroSym = (lexeme (string "0" >> return ()) <|> reserved "zero")>>return zero <?> "zero"

name = pidentif <?> "name"

procVar = (lexeme $ try $
            do{ c <- upper
              ; r <- many (alphaNum <|> char '_')
              ; return (c:r)
              }) <?> "process identifier (starting uppercase)"

globals = option [] $ reserved "#global" >> manyTill name semi

-- eol::Parser String
-- eol =   try (string "\n\r")
--     <|> try (string "\r\n")
--     <|> string "\n"
--     <|> string "\r"
--     <?> "end of line"

angles p = real_angles p <|> unicode_angles p <?> "angle brackets"
    where unicode_angles p = between (symbol "⟨") (symbol "⟩") p



-- | The parser for a PiCalc program
piProg :: Parser (PiProgAST String, [String])
piProg  = do skipSpaces
             glob <- globals
             start <- parseProc
             defs <- parsePiDefs
             eof
             return $ (PiProg start defs, glob)

piTerm :: Parser (PiAST String)
piTerm = do
    skipSpaces
    t <- parseProc
    eof
    return t

parsePiDefs = do
    deflist <- many parsePiDef
    checkDups (Map.empty) deflist
  where
    checkDups m [] = return m
    checkDups m ((v,d):xs)
        | Map.member v m = fail $ "Duplicate definition for "++(show v)
        | otherwise      = checkDups (Map.insert v d m) xs

parsePiDef :: Parser (String, ([String], (PiAST String)) )
parsePiDef = do (pvar, args) <- procCall
                defSym
                proc <- parseProc
                return (pvar, (args, proc))
                <?> "definition"

parseProc :: Parser (PiAST String)
parseProc = term `chainl1` parseParall <?> "term"

term:: Parser (PiAST String)
term  = zeroSym
    <|> parseCall
    <|> parseNew
    <|> parseBang
    <|> parens parseProc
    <|> (factor `chainl1` parseAltern)
factor:: Parser (PiAST String)
factor  = parsePrefixed <|> parens factor -- <|> parse prefix

procCall = do pvar <- procVar
              args <- option [] procArgs
              return (pvar, args)
              <?> "process call"

procArgs = brackets (commaList name) <?> "call arguments"

parseNew = do newSym
              xs <- nameList
              dot
              pro <- (try simpleTerm) <|> parseNew
              return $ new xs pro
              <?> "restriction"
  where
    nameList = parens (commaList name)
           <|> do {x <- name; return $ [x]}


parseBang = do bangSym
               t <- simpleTerm
               return $ Bang t

parsePrefixed = do pre <- parsePrefix
                   option (alt [(pre,zero)]) $
                      do{ dot;
                          pro <- simpleTerm;
                          return $ alt [(pre, pro)]}

simpleTerm = zeroSym <|> parseCall <|> parens parseProc <|> parsePrefixed

parsePrefix =  (tauSym >> return Tau)
           <|> do { x <- name; (op, msgs) <- parseInOut; return $ op x msgs}
           <?> "prefix"

parseInOut = (parsePreInfix "?"   >>= ret_in  <?> "input prefix")
         <|> (parsePreInfix "!"   >>= ret_out <?> "output prefix")
         <|> (parsePreStd parens  >>= ret_in  <?> "input prefix")
         <|> (parsePreStd angles  >>= ret_out <?> "output prefix")
  where
    ret_in x  = return (In,  x)
    ret_out x = return (Out, x)

    parsePreInfix op = operator op >> msg
    parsePreStd par = par (commaList name)

    msg = parens (commaList name) <|> do {x <- name; return [x]} <|> return []

altern (Alt x) (Alt y) = Alt (MSet.union x y)

parseParall:: Parser (PiAST String->PiAST String->PiAST String)
parseParall = parSym >> return parall

parseAltern:: Parser (PiAST String->PiAST String->PiAST String)
parseAltern = altSym >> return altern

parseCall:: Parser (PiAST String)
parseCall = do (p,a) <- procCall
               return $ PiCall p a
