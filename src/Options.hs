{-# LANGUAGE DeriveDataTypeable, RecordWildCards #-}
{-# OPTIONS_GHC -fno-cse #-}
module Options(
      JBOpt(..)
    , ExplStrategy(..)
    , ReprType(..)
    , RTDetail(..)
    , Quotienting(..)
    , PreorderRed(..)
    , TypeInfAlg(..)
    , jbModes
    , whenLoud
    , isLoud
    , whenNormal
    , isNormal
) where

import Version

import System.Console.CmdArgs

data JBOpt =
      Explore { -- interactive execution of operational semantics
          inputFile    :: FilePath
        , strategy     :: ExplStrategy
        , nonStop      :: Bool
        , withStats    :: Bool
        , strDotFile   :: Maybe FilePath
        , optUnfolding :: Bool
        }
    | Analyse { -- generation of reachability tree
          inputFile    :: FilePath
        -- , nonStop      :: Bool
        , rtDetails    :: [RTDetail]
        , maxPathLen   :: Maybe Integer
        , maxDepth     :: Maybe Integer
        , reachDotFile :: Maybe FilePath
        , reduction    :: PreorderRed
        , quotienting  :: Quotienting
        }
    | Convert { -- transformation of pi-terms into other representations
          inputFiles   :: [FilePath]
        , inputTerm    :: Maybe String
        , outputFile   :: Maybe FilePath
        , extension    :: Maybe String
        , withStats    :: Bool
        , outType      :: ReprType
        }
    | TypeInf { -- hierarchical type inference
          inputFiles      :: [FilePath]
        , inputTerm       :: Maybe String
        , skipUnsupported :: Bool
        , showFileNames   :: Maybe Bool
        , colored         :: Bool
        , algorithm       :: TypeInfAlg
        , abstract        :: Bool
        , withStats       :: Bool
        }
    deriving (Show, Data, Typeable)

data ExplStrategy = Ask | LeftMost | Random deriving (Show, Eq, Data, Typeable)

data RTDetail = AllCovering | FstCovering | ShowCongr | TermSnippet | HideQuot | HideUnfLbl deriving (Show, Eq, Data, Typeable)
data Quotienting = NoQuot | SiblingsQuot | GlobalQuot deriving (Show, Eq, Ord, Data, Typeable)
data PreorderRed = NoRed | GroupUnf deriving (Show, Eq, Ord, Data, Typeable)

data ReprType = NoOutput | Normalised | NormalForm | Standard | Restricted | StdPict | JavaScript --  | StrPict
    deriving (Show, Eq, Data, Typeable)

data TypeInfAlg = AlgComplete | AlgAltCompl | AlgIncomplete | AlgSimple
    deriving (Eq, Data, Typeable)

instance Show TypeInfAlg where
    show AlgComplete   =  "complete"
    show AlgAltCompl   =  "alternative"
    show AlgIncomplete =  "incomplete"
    show AlgSimple     =  "simple typing"

explore :: JBOpt
explore = Explore {
      inputFile = def
        &= typFile &= argPos 0
        -- &= help "File containing the input PiCalc program"

    , strategy = enum [ Ask      &= help "Let the user select the redex (default)"
                      , LeftMost &= help "Pick the leftmost redex"
                      , Random   &= help "Pick a redex at random" ]
    -- , strategy = Ask
    --     &= help ("Redex selection strategy in reductions. Choices: ask, leftmost, random")
    --     &= typ "STRATEGY"
    --     &= name "s"

    , optUnfolding = False
        &= name "group-unf" &= name "u" &= explicit
        &= help "Preorder reduction on successors"

    , nonStop = False
        &= name "n"
        &= help "Do not prompt the user after each reduction"

    , withStats  = False
        &= name "stats" &= name "S" &= explicit &= typFile
        &= help "Print some stats about the input program"

    , strDotFile = Nothing &= typFile
        &= name "o" &= name "dump" &= explicit
        &= help "Save the current state as a dot graph in FILE"
    } &= auto
      &= details ["Execute the operational semantics of the term, step by step"]

analyse :: JBOpt
analyse = Analyse {
      inputFile = def &= typFile &= argPos 0

    , reachDotFile = Nothing &= typFile
        &= name "o" &= name "dump" &= explicit
        &= help "Save the reachability graph as a dot file in FILE"

    , reduction    = enum [
          NoRed &= ignore
        , GroupUnf
            &= name "group-unf" &= name "u" &= explicit
            &= help "Performs unfolding actions together to reduce ininfluent interleaving"
        ]

    , quotienting = NoQuot &= typ "QUOT"
        &= name "Q" &= name "quot" &= explicit
        &= help "Quotient states by congruence (no, siblings, global)"
    -- , quotienting = enum [
    --       NoQuot &= ignore
    --     , SiblingsQuot
    --         &= help "Quotient siblings by congruence"
    --     , GlobalQuot
    --         &= help "Quotient states by congruence"
    --     ]

    , rtDetails = enum [
          [] &= ignore
        , [FstCovering] &= name "fst-cov"   &= help "Show closest covered ancestor"
        , [AllCovering] &= name "all-cov"   &= help "Show all covered ancestors (slow)"
        , [ShowCongr]   &= name "congr"     &= help "Show congruence relation (slow)"
        , [HideQuot]    &= name "hide-quot" &= help "Hide edges to quotiented nodes"
        , [HideUnfLbl]  &= name "hide-unf"  &= help "Hide unfolding actions on edges"
        , [TermSnippet] &= name "snippet"   &= help "Show a snippet of the term in the state nodes"
        ]
        -- &= typ "0-4"
        -- &= name "D" &= name "detail" &= explicit
        -- &= help "0 - successors, 1 - processes, 2 - closest covered ancestor, 3 - all covered ancestors, 4 - congruence."

    , maxPathLen = Nothing
        &= typ "N" &= name "p"
        &= help "Stop exploring a path when it's longer than N"

    , maxDepth = Nothing
        &= typ "N" &= name "d"
        &= help "Stop exploring a path when reaching a term exceeding N in depth"

    } &= details ["Generate the reachability tree"]

convert :: JBOpt
convert = Convert {
      -- TODO: 1. get args and default to stdin,
      --       2. add --term piterm option skipping reading file
      --       3. accept more than one file at once, option "--ext" allows to output to FILE.ext
      inputFiles = [] &= typFile &= args

    , outputFile = Nothing &= typFile
        &= name "output" &= name "o" &= explicit
        &= help "Converted output file (use `-` for stdout)"

    , inputTerm = Nothing
        &= name "term" &= name "t" &= explicit &= typ "PITERM"
        &= help "The term to be converted"

    , extension = Nothing &= typ "EXT"
        &= name "ext" &= name "e" &= explicit
        &= help "Converted term is output in INPUTFILEPATH.EXT"

    , withStats  = False
        &= name "S" &= name "stats" &= explicit &= typFile
        &= help "Print some stats about the input program"

    , outType    = enum [
          Normalised &= help "No-confl and normalised (default)"
        , Standard   &= help "Standard normal form"
        , NormalForm &= name "nf" &= help "Normal form (see hierarchical systems)"
        , Restricted &= help "Minimal restricted normal form"
        , StdPict    &= name "graph" &= name "g" &= explicit &= help "Standard Normal Form graph"
        , JavaScript &= name "js" &= name "j" &= explicit &= help "JavaScript representation"
        -- , StrPict    &= name "struct" &= explicit &= help "Structural graph"
        , NoOutput   &= name "n" &= name "none" &= explicit &= help "Mainly useful with --stats"
        ]
    -- , outType = Normalised
    --     &= help "Redex selection strategy in reductions."
    --     &= typ "TYPE"
    --     &= name "t" &= name "type" &= explicit
    } &= details ["Transform the input pi term into different representations"]

typeinf :: JBOpt
typeinf = TypeInf {
      inputFiles = [] &= typ "[FILE..]" &= args

    , inputTerm = Nothing
        &= name "t" &= name "term" &= explicit &= typ "PITERM"
        &= help "The term to be typed"

    , skipUnsupported = False
        &= name "skip" &= name "u" &= explicit
        &= help "Skip unsupported input terms"

    , colored = False
        &= help "Use colors in output"

    , showFileNames = Nothing
        &= name "filenames" &= name "f" &= explicit
        &= help "Show filename of input"

    , algorithm = enum [
          AlgComplete   &= name "complete"    &= explicit &= help "Default complete inference"
        , AlgAltCompl   &= name "alternative" &= name "a" &= explicit &= help "Alternative implementation of complete inference"
        , AlgIncomplete &= name "incomplete"  &= name "i" &= explicit &= help "Fast Incomplete inference"
        , AlgSimple     &= name "simple"      &= name "s" &= explicit &= help "Only perform simple typing"
        ]
        &= help "Inference algorithm"

    -- , simple = False
    --     &= help "Only perform simple typing"

    -- , incomplete = False
    --     &= help "Use incomplete type system"

    , abstract = False
        &= help "TODO! - Abstract a term until it can be proved depth-bounded"

    , withStats = False
        &= name "stats" &= name "S" &= explicit &= typFile
        &= help "TODO! - Print some stats about the typing"

    } &= details ["Infer hierarchical types from a pi term"]


jbModes :: String -> IO JBOpt
jbModes pun = cmdArgs $ modes [explore, analyse, convert, typeinf {- , verify, bound, cfa, abstract -}]
    &= program "jb"
    &= help "Play with π-calculus terms and their semantics"
    &= summary (versionInfoWith pun)
    &= verbosity


test = jbModes "\n"
