{-# LANGUAGE CPP #-}
-- | A module to fetch the version of the program
module Version (
    programName
  , version
  , versionInfo
  , versionInfoWith
  , welcome
  , banner
  , getPun
) where


import Data.Version

import System.Random(randomRIO)

#ifdef __CABAL_BUILD__
import qualified Paths_picalc as Paths (version)
#ifdef __REV__
version = showVersion Paths.version ++ " rev " ++ __REV__
#else
version = showVersion Paths.version
#endif
#else
version = "custom"
#endif

programName :: String
programName = "jb"

versionInfoWith pun = banner ++ pun ++ "\n\n" ++ welcome
versionInfo = versionInfoWith ""

welcome :: String
welcome = "James Bound, a depth-bounded π-calculus playground.\n"
           ++ "Version " ++ version

banner :: String
banner = "     __  ___,_____\n __ / / / _ ) ;=='\n/ // / / _  |/\n\\___/ /____/   "

getPun :: IO String
getPun = pick puns

pick :: [b] -> IO b
pick xs = randomRIO (0, (length xs - 1)) >>= return . (xs !!)

puns :: [String]
puns =
    [ "Nobody does it better."
    , "You only live a bounded number of times."
    , "On her majesty νservice."
    , "The sπ who loved me."
    , "Licence to abstract."
    , "Licence to branch."
    , "Ideals are forever."
    , "Dr. No/Yes/Don't know."
    , "Dr. Wqo."
    , "From Oxford with love."
    , "Octoprocess."
    , "Sπfall."
    , "Thunderbang."
    ]
