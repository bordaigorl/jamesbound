{-# LANGUAGE OverloadedStrings #-}
module Data.GraphVizEither where

import Data.GraphViz.Printing

instance (PrintDot a, PrintDot b) => PrintDot (Either a b) where
    unqtDot (Right a) = (unqtText "R") <> (unqtDot a)
    unqtDot (Left  b) = (unqtText "L")  <> (unqtDot b)
