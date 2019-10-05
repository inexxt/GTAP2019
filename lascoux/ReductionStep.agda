{-# OPTIONS --allow-unsolved-metas #-}

module ReductionStep where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; Σ; _×_; _,_; _,′_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)

open import General
open import Relation.Nullary
open import Data.Empty
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Canonization using (F-canonize-p>; F-canonize-p≡; F-canonize-p<; _≃_; _↓_ )

open _≃_

variable
  n : ℕ
  l : List ℕ

data _∈_ : ℕ -> List ℕ -> Set where
    here : (n : ℕ) -> (l : List ℕ) -> n ∈ (n ∷ l)
    there : (k : ℕ) -> {n : ℕ} -> {l : List ℕ} -> (n ∈ l) -> n ∈ (k ∷ l)

data _∉_ : ℕ -> List ℕ -> Set where
    not-here : (n : ℕ) -> n ∉ []
    not-there : {k : ℕ} -> {n : ℕ} -> {¬ (k == n)} -> {l : List ℕ} -> (n ∉ l) -> n ∉ (k ∷ l)

data _>=_ : ℕ -> List ℕ -> Set where
  [] : {n : ℕ} -> n >= []
  _:⟨_⟩:_ : {n : ℕ} -> {l : List ℕ} -> (k : ℕ) -> (k ≤ n) -> n >= l -> n >= (k ∷ l)

≤-≠-≤ : {n m : ℕ} -> (n ≤ suc m) -> ¬ (n ≡ suc m) -> (n ≤ m)
≤-≠-≤ z≤n q = z≤n
≤-≠-≤ (s≤s p) q = {!!}

step : (ll : (suc n) >= l) -> Σ (List ℕ × ℕ) (λ (l' , r) -> (n >= l') × (l' ++ ((suc (suc n)) ↓ r)) ≃ l)
step {n} {.[]} [] = ([] , 0) , ([] , refl)
step {n} {k ∷ l} (_ :⟨ x ⟩: ll) with k ≟ (suc n)
step {n} {k ∷ l} (.k :⟨ x ⟩: ll) | yes p =  {!all-reduce!}
step {n} {k ∷ l} (.k :⟨ x ⟩: ll) | no ¬p =
  let k≤n : k ≤ n
      k≤n = ≤-≠-≤ x ¬p
      (l , r) , (ll , pp) = step ll
  in ((k ∷ l) , r) , ((k :⟨ k≤n ⟩: ll) , (prepend k pp))

data Canonical : (n : ℕ) -> Set where
  CanZ : Canonical 0
  CanS : {n : ℕ} -> (k r : ℕ) -> (n < k) -> (r ≤ k) -> (l : Canonical n) -> Canonical k

immersion : {n : ℕ} -> Canonical n -> List ℕ
immersion {zero} CanZ = []
immersion {suc n} (CanS k r n<k r≤k l) = (k ↓ r) ++ immersion l

open import Data.Fin

canonical-form-lemma : {n : ℕ} -> (l : List (Fin n)) -> ∃ (λ cl -> (map (λ x -> toℕ x) l) ≃ (immersion {n} cl))

canonical-form-lemma-Free : (l : List ℕ) -> ∃ (λ n -> ∃ (λ cl -> l ≃ (immersion {n} cl)))
