{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Language.PiCalc.Pretty where

import Text.PrettyPrint
import Language.PiCalc.Syntax

import Data.List

-- TODO: add options for hiding ending 0 etc..

class Pretty a where
    pretty :: a -> Doc

prettyPi :: (Pretty a) => a -> String
prettyPi = render.pretty

instance Pretty String where
    pretty = text

instance Pretty Int where
    pretty = int

instance Pretty Doc where
    pretty = id

instance (Pretty p, Pretty n) => Pretty (PiTerm p n) where
    pretty (Parall [])          = zeroSym
    pretty (Parall ps)          = parens $ sep $ punctOp parallSym (map pretty ps)
    pretty (Alt [])             = zeroSym
    pretty (Alt [alt])          = prefix alt
    pretty (Alt alts)           = parens $ sep $ punctOp sumSym $ map prefix alts
    pretty (New name proc)      = parens $ prefix (char 'ν' <> pretty name, proc)
    pretty (PiCall procid args) = pretty procid <> argList args
    pretty (Bang proc)          = bangSym <> pretty proc

instance (Pretty n) => Pretty (PiPrefix n) where
    pretty (In x ns) = (pretty x) <> parens (nameList ns)
    pretty (Out x ns) = (pretty x) <> angles (nameList ns)
    pretty Tau = text "τ"

instance (Pretty p, Pretty n) => Pretty (PiDefs p n) where
    pretty defs = enlist $ map prettydef $ defsList defs
      where
        prettydef (p,(a,d)) = hang ((pretty p <> argList a )<+> text ":=") 4 (pretty d)
        enlist = foldr1 (\x d->(x <> text "\n" $+$ d))

nameList l = sep $ punctuate comma $ map pretty l

argList args = brackets $ nameList args

punctOp _ [] = []
punctOp op (x:xs) = x:map (op<+>) xs

prefix (pre,proc)
    | isZero proc = pretty pre
    | otherwise   = pretty pre <> char '.' <> pretty proc

angles p = char '⟨' <> p <> char '⟩'

parallSym   = char '|'
sumSym = char '+'
zeroSym = text "0"
bangSym     = text "!"

