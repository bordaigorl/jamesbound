module Language.PiCalc.Analysis.PetriNet(module PetriNet) where

import Data.List(partition)

import Data.Map(Map)
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set

-- TODO: add places :: Set pl field for efficiency
newtype PN pl = PN {
    -- rules :: [(Map pl TokenNum, Map pl TokenNum)]
    rules :: [PNRule pl]
    -- ^ each transition @([(pi,ni)..],[(pj,nj)..])@ takes ni token from place @pi@ and puts @nj@ tokens to place @pj@
    --   each place must appear at most once in the two lists.
    --   I could have chosen Map to represent these but I did not want to over-complicate things.
} deriving (Show, Eq, Ord)

type PNRule pl = ([(pl,TokenNum)] , [(pl,TokenNum)])
type Marking pl = Map pl TokenLim

type TokenNum = Int -- ^ Should be always positive!
data TokenLim = Tok TokenNum | OmegaTok
    deriving (Eq, Ord, Show)

places :: Ord pl => PN pl -> Set pl 
places pn = foldr Set.insert Set.empty $ concatMap extract $ rules pn
  where extract (pre,post) = map fst $ pre ++ post

places' :: Ord a => PN a -> Set a 
places' pn = Set.unions $ map extract $ rules pn
  where extract (pre,post) = Set.fromList $ map fst $ pre ++ post 

tokensIn :: Ord pl => pl -> Marking pl -> TokenLim 
tokensIn pl m = Map.findWithDefault (Tok 0) pl m

addTokensTo :: Ord pl => (pl, TokenNum) -> Marking pl -> Marking pl
addTokensTo   (pl, n) m = Map.insert pl (tokAdd n (tokensIn pl m)) m

remTokensFrom :: Ord pl => (pl, TokenNum) -> Marking pl -> Marking pl
remTokensFrom (pl, n) m = Map.insert pl (tokRem n (tokensIn pl m)) m

-- | Lift a unary operation on "TokenNum" to "TokenLim", with the invariant @tokLift op OmegaTok = OmegaTok@.
tokLift :: (TokenNum -> TokenNum) -> TokenLim -> TokenLim 
tokLift _  OmegaTok = OmegaTok
tokLift op (Tok n)  = Tok $ op n

tokAdd :: TokenNum -> TokenLim -> TokenLim 
tokAdd n = tokLift (+ n)
tokRem :: TokenNum -> TokenLim -> TokenLim 
tokRem n = tokLift (subtract n)

addRule :: [(pl, TokenNum)] -> [(pl, TokenNum)] -> PN pl -> PN pl 
addRule pre post pn = pn{ rules = (pre, post):rules pn }
  -- where
    -- toMap = Map.fromListWith (+)
    -- tag = Map.map (Tok . abs)

emptyPN :: PN pl 
emptyPN = PN{ rules = [] }

emptyMarking :: Marking pl
emptyMarking = Map.empty

partitionEnabled :: Ord pl => PN pl -> Marking pl -> ([PNRule pl], [PNRule pl]) 
partitionEnabled pn m = partition (isEnabled m) $ rules pn

enabledRules :: Ord pl => PN pl -> Marking pl -> [PNRule pl] 
enabledRules pn m = filter (isEnabled m) $ rules pn

isEnabled :: Ord pl => Marking pl -> PNRule pl -> Bool 
isEnabled m (pre, _) = validMarking $ remTokens pre m
    -- all enoughTok pre

enoughTok :: Ord pl => (pl, TokenNum) -> Marking pl -> Bool 
enoughTok (pl, n) m = tokensIn pl m >= (Tok n)

succMarkings :: Ord pl => PN pl -> Marking pl -> [Marking pl] 
succMarkings pn m = map fire $ enabledRules pn m
  where
    fire (pre, post) = addTokens post $ remTokens pre m

remTokens :: Ord pl => [(pl, TokenNum)] -> Marking pl -> Marking pl 
remTokens pre m = foldr remTokensFrom m pre

addTokens :: Ord pl => [(pl, TokenNum)] -> Marking pl -> Marking pl 
addTokens pre m = foldr addTokensTo m pre

validMarking :: Marking pl -> Bool 
validMarking m = all (>= Tok 0) $ Map.elems m

-- limDiff OmegaTok OmegaTok = Tok 0 
-- limDiff OmegaTok _        = OmegaTok
-- limDiff (Tok n) (Tok m)   = Tok $ n-m

-- | Partial order on markings:
--   * @Nothing@ means incomparable
--   * @Just c@ means comparison results in @c@ (@EQ@, @LT@ or @GT@)
compareMarkings :: Ord pl => Marking pl -> Marking pl -> Maybe Ordering 
compareMarkings m1 m2 = foldr join (Just EQ) $ map cmp $ Map.toList m1
  where
    cmp (pl, n) = compare n (tokensIn pl m2)
    join _ Nothing    = Nothing
    join EQ x         = x
    join LT (Just GT) = Nothing
    join LT _         = Just LT
    join GT (Just LT) = Nothing
    join GT _         = Just GT

{--
  TODO: make karpMiller parametric on a function
  
    PN pl -> Marking pl -> PN pl

  that can update the transitions at each step wrt the new marking.
  When the transitions are known beforehand one can just supply
  (\_ _ -> p) but you can now also support generating them on-the-fly
--}
karpMiller :: Ord pl => PN pl -> Marking pl -> [Marking pl] 
karpMiller pn m = explore [m]
  where
    explore ms@(m:_) = m : concat [ explore (m' : ms) | s <- succMarkings pn m, m' <- accellerate s ms ]

    accellerate m [] = [m] -- it is a new state
    accellerate m (m':ms) =
        case compareMarkings m m' of
            Just GT -> [widenMarking m m'] -- continue with widened state
            Just EQ -> []                  -- already seen: nothing to explore
            _       -> accellerate m ms    -- look for comparable states in rest of path

widenMarking :: Ord pl => Marking pl -> Marking pl -> Marking pl
widenMarking m1 m2 = Map.unionWith widen m1 m2
  where
    widen x y
        | x > y     = OmegaTok
        | otherwise = x

isUnbounded :: Ord pl => PN pl -> Marking pl -> pl -> Bool 
isUnbounded pn m pl = any (\x -> tokensIn pl x == OmegaTok) $ karpMiller pn m

isCoverable :: Ord pl => PN pl -> Marking pl -> Marking pl -> Bool 
isCoverable pn m0 m = any (covers m) $ karpMiller pn m0
  where covers m m' =
            case compareMarkings m m' of
                Just EQ -> True
                Just LT -> True
                _       -> False

showMarking m = concat ["[" ++ show p ++ " " ++ showTok n ++ "] " | (p,n) <- Map.toList m]
    where showTok OmegaTok = "ω"
          showTok (Tok  n) = show n