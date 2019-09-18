{-# OPTIONS --without-K #-}

module BubbleSort where

open import Data.Nat
open import Data.Fin hiding (_<?_)
open import General
open import Relation.Nullary
open import Data.Product using (∃ ; _,_)

data List (A : Set) : Set where
    [] : List A
    _::_ : A -> List A -> List A

data Permutation {A : Set} : List A -> List A -> Set where
    perm-nil : Permutation [] []
    perm-skip : (x : A) -> (l l' : List A) -> Permutation l l' -> Permutation (x :: l) (x :: l')
    perm-swap : (x y : A) -> (l : List A) -> Permutation (y :: (x :: l)) (x :: (y :: l))
    perm-trans : (l l' l'' : List A) -> Permutation l l' -> Permutation l' l'' -> Permutation l l''


sort : (l : List ℕ) -> (∃ (λ l' -> Permutation l l'))
sort [] = [] , perm-nil
sort (x :: []) = (x :: []) , perm-skip x [] [] perm-nil
sort (x :: (y :: l)) with x <? y
... | yes _ = {!   !}
... | no  _ = {!   !}
