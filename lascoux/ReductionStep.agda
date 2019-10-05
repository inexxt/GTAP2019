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

open import Canonization using (F-canonize-p>; F-canonize-p≡; F-canonize-p<; _≃_)

data _∈_ : ℕ -> List ℕ -> Set where
    here : (n : ℕ) -> (l : List ℕ) -> n ∈ (n ∷ l)
    there : (k : ℕ) -> {n : ℕ} -> {l : List ℕ} -> (n ∈ l) -> n ∈ (k ∷ l)

data _∉_ : ℕ -> List ℕ -> Set where
    not-here : (n : ℕ) -> n ∉ []
    not-there : {k : ℕ} -> {n : ℕ} -> {¬ (k == n)} -> {l : List ℕ} -> (n ∉ l) -> n ∉ (k ∷ l)

first-occ : {n : ℕ} -> {l : List ℕ} -> (n ∈ l) -> Σ ((List ℕ) × (List ℕ)) (λ (l' , l'') -> (n ∉ l') × ((l' ++ [ n ] ++ l'') ≡ l)))

data _>=_ : ℕ -> List ℕ -> Set where
  [] : {n : ℕ} -> n >= []
  _:⟨_⟩:_ : {n : ℕ} -> (k : ℕ) -> (k ≤ n) -> n >= l -> n >= (k ∷ l)


data Canonical : (n : ℕ) -> Set where
  CanZ : Canonical 0
  CanS : {n : ℕ} -> (k r : ℕ) -> (n < k) -> (r ≤ k) -> (l : Canonical n) -> Canonical k

immersion : {n : ℕ} -> Canonical n -> List ℕ
immersion {zero} CanZ = []
immersion {suc n} (CanS k r n<k r≤k l) = (k ↓ r) ++ immersion l

reduction-lemma : {n ∈ l} -> ∃ (λ l' -> ∃ (λ r -> (n ∉ l) × (l ≃ (l' ++ (n ↓ r)))))
reduction-lemma = {!   !}

open import Data.Fin

canonical-form-lemma : {n : ℕ} -> (l : List (Fin n)) -> ∃ (λ cl -> (map (λ x -> toℕ x) l) ≃ (immersion {n} cl))

canonical-form-lemma-Free : (l : List ℕ) -> ∃ (λ n -> ∃ (λ cl -> l ≃ (immersion {n} cl)))
