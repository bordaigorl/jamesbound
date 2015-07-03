{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, RecordWildCards #-}
module Language.PiCalc.Pretty(
    -- * Pretty printing
      Pretty
    , pretty
    , prettyProg
    , prettyTerm
    , prettyShort
    -- * Program pretty printing options
    , PrettyProgOpts(..)
    , parseableProgOpts
    , defProgOpts
    -- * Term pretty printing options
    , PrettyTermOpts(..)
    , baseTermOpts
    , parseableTermOpts
    , defTermOpts
    , unicodeStyle
    , asciiStyle
    , milnerStyle
    , hoareStyle
    -- ** Non parseable outputs
    -- These options generate output which cannot parsed back by the parsers
    -- defined in "Language.PiCalc.Parser"
    , cspStyle
    , ccsStyle
    , colorHoareStyle
    -- * Re-exports from "Text.PrettyPrint"
    , render
    , renderStyle
    , Style(..)
    , Mode(..)
    , style
    , nest
) where

import Text.PrettyPrint

import Language.PiCalc.Syntax.AST
import Language.PiCalc.Syntax.Term
import Language.PiCalc.Syntax.StdNF

import Language.PiCalc.Semantics.Substitutions
import Language.PiCalc.Semantics.Process


import qualified Data.MultiSet as MSet
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map

import Data.Char (isDigit)


angles p = char '<' <> p <> char '>'
-- angles p = char '⟨' <> p <> char '⟩' -- unicode angles are cool but look too similar to ()

dot = char '.'


-- | The function @pretty@ should return a @Doc@ which, when rendered, should be
-- parsed successfully by the parsers defined in "Language.PiCalc.Parser".
class Pretty a where
    pretty :: a -> Doc

instance Pretty String where
    pretty = text

instance Pretty Int where
    pretty = int

instance Pretty PiName where
    pretty PiName{static=name, unique=i,isGlobal=global}
        | global = text name
        | i < 0 = text $ attach name $ (show $ negate i)++"'"
        | otherwise = text $  attach name $ show i
      where
        attach "" n = "unk" ++ n -- this should actually never happen...
        attach name n
            | isDigit $ last name = name ++ '_':n
            | otherwise = name ++ n

instance Pretty Doc where
    pretty = id

instance Pretty n => Pretty (PiAST n) where
    pretty = prettyTerm parseableTermOpts
    -- pretty ps | isZero ps     = zeroSym
    -- pretty (Parall ps)        = parens $ sep $ punctOp parallSym $ map pretty $ MSet.elems ps
    -- pretty (Alt alts)
    --     | MSet.size alts == 1 = prefix $ head $ MSet.elems alts
    --     | otherwise           = parens $ sep $ punctOp sumSym $ map prefix $ MSet.elems alts
    -- pretty (New names proc)   = char 'ν' <> parens1 (Set.elems names) <> char '.' <> pretty proc
    -- pretty (PiCall pvar args) = pretty pvar <> argList args
    -- pretty (Bang proc)        = bangSym <> pretty proc

instance (Pretty n) => Pretty (PiPrefix n) where
    pretty (In x ns) = (pretty x) <> text "?" <> par1 comma parens (map pretty ns)
    -- pretty (In x ns) = (pretty x) <> parens (nameList ns)
    pretty (Out x ns) = (pretty x) <>  text "!" <> par1 comma parens (map pretty ns)
    -- pretty (Out x ns) = (pretty x) <> angles (nameList ns)
    pretty Tau = text "τ"

instance (Pretty n, Ord n) => Pretty (PiProgAST n) where
    pretty = prettyProg parseableProgOpts

instance Pretty NameSubst where
    pretty σ = braces (sep $ punctuate comma $ map prettyassoc $ Map.toList σ)
      where
        prettyassoc (x,y) = pretty x <+> text "↦" <+> pretty y

instance Pretty StdNFTerm where
    pretty = pretty.stdToTerm


instance Pretty PiAction where
    pretty TauAction     = text "τ"
    pretty (SyncOn x)    = text "Synch on" <+> pretty x
    pretty (Unfolding t) = text "Unfolding def" <+> pretty t
    pretty InitState     = text "Initial state"


instance Pretty StdFactor where
    pretty x = pretty $ new (Set.elems $ restrNames x) (seqTerm x)

instance Pretty p => Pretty (Set p) where
    pretty x = braces $ sep $ punctuate comma $ map pretty $ Set.elems x

instance Pretty () where
    pretty () = text "•"


data PrettyProgOpts = POpt {
      termOpts :: PrettyTermOpts
    , defSym :: Doc
    , defList :: [Doc] -> Doc
    , wrapProg :: Doc -> Doc
    , wrapDef  :: Doc -> Doc
    }

parseableProgOpts = POpt {
      termOpts = parseableTermOpts
    , defSym = text ":="
    , defList = listing
    , wrapProg = id
    , wrapDef = id
    }
defProgOpts = parseableProgOpts

listing = foldr (\x d->(x $+$ d)) empty


data PrettyTermOpts = TOpt {
      maxLvl :: Maybe Int -- ^ stop at a certain nesting level
    , ellipsis :: Doc -- ^ displayed when omitting parts
    , explicitZeros :: Bool -- ^ whether to omit zeros when unambiguous
    , wrapTerm :: Doc -> Doc -- ^ used to print something before and after
    , zeroSym :: Doc
    , parallSym :: Doc
    , sumSym :: Doc
    , bangSym :: Doc
    , prefixSym :: Doc
    , argList  :: [Doc] ->  Doc
    , nameList :: (Doc -> Doc) -> [Doc] ->  Doc
    , tauSym :: Doc
    , inpSyn :: Doc -> [Doc] -> Doc
    , outSyn :: Doc -> [Doc] -> Doc
    , restrSyn :: [Doc] -> Doc -> Doc
    , group :: Doc -> Doc
    }

baseTermOpts = TOpt {
      maxLvl = Nothing
    , explicitZeros = False
    , wrapTerm = id
    --
    , nameList = par1 comma
    , zeroSym = text "0"
    , sumSym = char '+'
    , bangSym = char '*'
    , prefixSym = dot
    , argList = par0 comma brackets
    , group = parens
    --
    , ellipsis = text "..."
    , parallSym = char '|'
    , restrSyn = (\ns p -> text "new" <+> par1 comma parens ns <> dot <> p)
    , tauSym = text "tau"
    --
    , inpSyn = (\n ns -> n <> char '?' <> par1 comma parens ns)
    , outSyn = (\n ns -> n <> char '!' <> par1 comma parens ns)
    }

parseableTermOpts = hoareStyle $ unicodeStyle baseTermOpts
defTermOpts = parseableTermOpts


unicodeStyle opt = opt {
      ellipsis = text "…"
    , parallSym = char '‖'
    , restrSyn = (\ns p -> char 'ν' <> nameList opt parens ns <> dot <> p)
    , tauSym = char 'τ'
}

asciiStyle opt = opt{
      ellipsis = text ".."
    , parallSym = char '|'
    , restrSyn = (\ns p -> text "new" <+> nameList opt parens ns <> dot <> p)
    , tauSym = text "tau"
}

milnerStyle opt = opt{
      inpSyn = (\n ns -> n <> prtNames parens ns)
    , outSyn = (\n ns -> n <> prtNames angles ns)
    }
  where
    prtNames p [] = p empty
    prtNames p [x] = p x
    prtNames p xs = nameList opt parens xs

hoareStyle opt = opt{
      inpSyn = (\n ns -> n <> char '?' <> nameList opt parens ns)
    , outSyn = (\n ns -> n <> char '!' <> nameList opt parens ns)
    }

-- non parseable:
cspStyle opt = hoareStyle opt{
      prefixSym = text "->"
    , restrSyn = (\ns p -> p <+> char '\\' <+> (braces $ sep $ punctuate comma ns))
    }
ccsStyle opt = milnerStyle opt{
      prefixSym = dot
    , restrSyn = (\ns p -> (sep $ map parens ns) <> p)
    , bangSym = char '!'
    }
colorHoareStyle opt = opt{
      inpSyn = (\n ns -> text "\x1b[31m" <> n <> char '?' <> nameList opt parens ns <> text "\x1b[0m")
    , outSyn = (\n ns -> text "\x1b[32m" <> n <> char '!' <> nameList opt parens ns <> text "\x1b[0m")
    , restrSyn = (\ns p -> text "\x1b[34mν" <> nameList opt parens ns <> text "\x1b[0m" <> dot <> p)
    }

prettyProg :: (Pretty n, Ord n) => PrettyProgOpts -> PiProgAST n -> Doc
prettyProg POpt{..} PiProg{..} = wrapProg $ globals $$ prettyTerm termOpts start $+$ prettyDefs
      where
        prettyDefs = defList $ map prettydef $ defsList defs
        prettydef (p,(a,d)) = wrapDef $ hang ((pretty p <> prArgs a) <+> defSym) 4 (prettyTerm termOpts d)
        prArgs args = argList termOpts $ map pretty args

        globals | Set.null glob = empty
                | otherwise     = text "#global" <+> (sep $ punctuate space pglob) <+> text ";"
          where
            glob  = getGlobals defs
            pglob = map pretty $ Set.elems glob


prettyTerm :: (Pretty name) => PrettyTermOpts -> PiAST name -> Doc
prettyTerm TOpt{..} t = wrapTerm $ prt maxLvl t
  where
    prt (Just n) _ | n <= 0 = ellipsis
    prt d t = case t of
        _  | isZero t      -> zeroSym
        (Parall ps)        -> group $ sep $ punctOp parallSym $ map (prt d') $ MSet.elems ps
        (Alt alts)
            | MSet.size alts == 1 -> prefix $ head $ MSet.elems alts
            | otherwise           -> group $ sep $ punctOp sumSym $ map prefix $ MSet.elems alts
        (New names proc)   -> restrSyn (map pretty $ Set.elems names) (prt d proc)
        (PiCall pvar args) -> pretty pvar <> prArgs args
        (Bang proc)        -> parens $ bangSym <> prt d proc
      where
        d' = case d of Nothing -> Nothing; Just i -> Just (i-1);

        prefix (pre,proc)
            | isZero proc && not explicitZeros = prtPre pre
            | otherwise   = prtPre pre <> prefixSym <>
                            case proc of
                                (New _ _) -> group $ prt d' proc
                                _         -> prt d' proc

        prtPre (In x ns) = inpSyn (pretty x) (map pretty ns)
        prtPre (Out x ns) = outSyn (pretty x) (map pretty ns)
        prtPre Tau = tauSym

        prArgs args = argList $ map pretty args

        punctOp _ [] = []
        punctOp op (x:xs) = x:map (op<+>) xs

prettyShort:: Int -> PiTerm -> Doc
prettyShort d = prettyTerm defTermOpts{maxLvl=Just d}


par1 _ _ [] = empty
par1 _ _ [d] = d
par1 s p y = p $ sep $ punctuate s y

par0 _ _ [] = empty
par0 s p y = p $ sep $ punctuate s y

-- nameList l = sep $ punctuate comma $ map pretty l
