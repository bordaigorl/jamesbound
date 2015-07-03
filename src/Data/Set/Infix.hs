module Data.Set.Infix( (∪) , (∩) , (∊) , (⊆), (∅) ) where

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
