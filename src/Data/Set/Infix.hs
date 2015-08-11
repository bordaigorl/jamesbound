module Data.Set.Infix( (∪) , (∩) , (\\) , (∊) , (⊆), (∅), disjointFrom, intersects ) where

import Data.Set as Set

(∪) :: Ord a => Set a -> Set a -> Set a
(∪) = Set.union

(∩) :: Ord a => Set a -> Set a -> Set a
(∩) = Set.intersection

(∊) :: Ord a => a -> Set a -> Bool
(∊) = Set.member

(⊆) :: Ord a => Set a -> Set a -> Bool
(⊆) = Set.isSubsetOf

(∅) = Set.empty

disjointFrom :: Ord a => Set a -> Set a -> Bool
disjointFrom a b = Set.null $ a ∩ b

intersects :: Ord a => Set a -> Set a -> Bool
intersects a b = not $ a `disjointFrom` b
