{-# OPTIONS --without-K #-}

module SelSort where

open import Data.Nat
open import Data.Fin hiding (_<?_)
open import General
open import Relation.Nullary
open import Data.Product using (∃ ; _,_ ; _×_)

data List (A : Set) : Set where
    [] : List A
    _::_ : A -> List A -> List A

Permutation : Set
Permutation = List (ℕ × ℕ)

-- sort : (l : List ℕ) -> Permutation
-- sort [] = []
-- sort (x :: []) = []
-- sort (x :: (y :: l)) with x <? y
-- ... | yes _ = {!   !}
-- ... | no  _ = {!   !}

selSort : List ℕ -> List ℕ
selSort [] = []
selSort (x :: []) = []
selSort (x :: (y :: l)) with x <? y
... | yes _ = {!   !}
... | no  _ = {!   !}
