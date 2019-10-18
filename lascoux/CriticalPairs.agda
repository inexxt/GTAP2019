{-# OPTIONS --allow-unsolved-metas #-}

module CriticalPairs where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; _×_; _,_)
open import General
open import Relation.Nullary
open import Data.Empty
open import Data.Sum hiding (swap)
open import Data.Bool hiding (_<_; _≤_)
open import Data.Bool.Properties hiding (≤-reflexive)

open import Arithmetic hiding (n)
open import Diamond hiding (n; l)
open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to ≤∎) hiding (_≡⟨_⟩_; _≡⟨⟩_)


open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)

variable
  n : ℕ
  l : List ℕ

--- critical pairs

ss : (a b c : ℕ) -> (m m1 m2 : List ℕ) -> (a > suc b) -> (b > suc c) -> (m ≡ a ∷ b ∷ c ∷ []) -> (m ≅ m1) -> (m ≅ m2) -> ∃ (λ mm -> (m1 ≃ mm) × (m2 ≃ mm))
ss a b c .(a ∷ b ∷ c ∷ []) m1 m2 pab pbc refl pm1 pm2 = {!!}
