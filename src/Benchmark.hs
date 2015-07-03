import Language.PiCalc.Syntax.Congruence

main = sequence_ $ map print $ [stressPrl t | t <- [15,20..50] ] ++ [stressNest t | t <- [1..12]]
