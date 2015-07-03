{-# LANGUAGE DeriveDataTypeable #-}
{-
Copyright (c) 2013 Emanuele D'Osualdo <emanuele.dosualdo@gmail.com>.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.
-}
{- |
    Module    : Main
    Copyright : Copyright (C) 2013 Emanuele D'Osualdo
    License   : CRAPL

    Maintainer: Emanuele D'Osualdo <emanuele.dosualdo@gmail.com>
    Stability : experimental

This is James Bound, a tool to manipulate and analyse (depth-bounded) pi-calculus.
The code is released under the CRAPL licence, the "PiCalc" library under a BSD-like licence.
-}
module Main where

import Language.PiCalc

import System.Console.CmdArgs
import System.Directory (createDirectoryIfMissing, getTemporaryDirectory, doesFileExist, removeFile)

import Control.Monad (when)
import Data.List (break)


import Version
import Frontend
-- Modes:
import Explore
import Analyse
import Convert
import Type

main = do
    opt <- parseOptions
    case opt of
        Explore{} -> runExplore opt
        Analyse{} -> runAnalyse opt
        Convert{} -> runConvert opt
        TypeInf{} -> runTypeInference opt
