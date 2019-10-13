{-# OPTIONS --allow-unsolved-metas #-}

module Reduction where

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

open import Coxeter hiding (n; l)
open import Arithmetic hiding (n)
open import Canonization hiding (n; l)
open import CanonizationInterface hiding (n; l)
open import ReductionStep using (all-reduce; _>>_)

open _≃_
open ≃-Reasoning
open Σ
open _>>_

variable
  n : ℕ
  l : List ℕ

data Canonical : (n : ℕ) -> Set where
  CanZ : Canonical 0
  CanS : {n : ℕ} -> (l : Canonical n) -> {k r : ℕ} -> (n < k) -> (r ≤ k) -> Canonical k

immersion : {n : ℕ} -> Canonical n -> List ℕ
immersion {zero} CanZ = []
immersion {suc n} (CanS l {k} {r} n<k r≤k) = (immersion l) ++ (k ↓ r)

step : (0 < n) -> (ll : (suc n) >> l) -> Σ (List ℕ × ℕ) (λ (l' , r) -> (n >> l') × (r ≤ (suc n)) × (l' ++ ((suc n) ↓ r)) ≃ l)
step {n} {l} pn ll = all-reduce {[]} {l} {n} pn {0} z≤n [] ll

open import Data.Fin

canonical-form-lemma : {n : ℕ} -> {l : List ℕ} -> (l' : n >> l) -> ∃ (λ cl -> l ≃ (immersion {n} cl))
canonical-form-lemma {0} {.[]} [] = CanZ , refl
canonical-form-lemma {1} {l} l' = {!!}
canonical-form-lemma {suc (suc n)} {l} l' =
  let (w , r) , (w' , pr , p) = step {suc n} {l} (s≤s z≤n) l'
      (cl , pp) = canonical-form-lemma {suc n} {w} w'

      xx : w ≃ immersion cl
      xx = pp

      lemma =
        ≃begin
          w ++ (suc (suc n) ↓ r)
        ≃⟨ ++-≃ pp refl ⟩
          immersion cl ++ suc (suc n) ↓ r
        ≃∎
  in  CanS cl {suc (suc n)} {r} (s≤s (≤-reflexive refl)) pr , trans (comm p) lemma

canonical-form-lemma-Free : (l : List ℕ) -> ∃ (λ n -> ∃ (λ cl -> l ≃ (immersion {n} cl)))
