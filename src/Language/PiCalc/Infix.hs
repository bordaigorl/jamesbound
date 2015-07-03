module Language.PiCalc.Infix((‖), (⊕), eAlt, τ, (!:), (?:), (.:), (≡), ν) where

import Language.PiCalc.Syntax

import qualified Data.MultiSet as MSet

infixl 2 ≡
infixl 5 ‖
infixr 6 ⊕
infixr 8 !:, ?:
infixr 7 .:

(‖) :: Ord name => PiAST name -> PiAST name -> PiAST name
(‖) = parall

(p,pr) ⊕ (Alt l) = Alt $ MSet.insert (p,pr) l
eAlt = Alt $ MSet.empty

n !: l = Out n l
n ?: l = In n l
τ = Tau
ν :: Ord name => [name] -> PiAST name -> PiAST name
ν = new

n .: l = (n,l)

(≡) = congruent
