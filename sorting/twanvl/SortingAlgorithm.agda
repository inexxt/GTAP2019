-- source : https://gist.github.com/twanvl/5635740

{-# OPTIONS --without-K #-}

open import Level using () renaming (zero to ℓ₀;_⊔_ to lmax)
open import Data.List
open import Data.List.Properties
open import Data.Nat hiding (_≟_;_≤?_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
import Relation.Binary.PropositionalEquality as PE
open PE using (_≡_)
open import Function
open import Induction.Nat

module SortingAlgorithm
    {A : Set}
    {_≤_ : Rel A ℓ₀}
    (isPartialOrder : IsPartialOrder _≡_ _≤_)
    (_≤?_ : (x y : A) → (x ≤ y ⊎ y ≤ x)) where

  open import Permutations A
  open import SortedList isPartialOrder

  -- Insertion sort
  insert : ∀ {xs} → (x : A) → Sorted xs → Sorted (x ∷ xs)
  insert x [] = cons x here [] []
  insert x (cons u p0 u≤*us us) with (x ≤? u)
  ... | (inj₁ p) = cons x here (insert-less p0 p (trans* p u≤*us)) $ cons u p0 u≤*us us
  ... | (inj₂ p) = cons u (there p0) (p ∷ u≤*us) (insert x us)

  insertion-sort : (xs : List A) → Sorted xs
  insertion-sort [] = []
  insertion-sort (x ∷ xs) = insert x (insertion-sort xs)
