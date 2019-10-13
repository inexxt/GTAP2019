module ReductionProps where

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
open import Canonization using (_↓_)
open import ReductionStep using (all-reduce; _>>_; >>-++)
open import Reduction using (Canonical; immersion; canonical-form-lemma)

open _≃_
open ≃-Reasoning
open Σ
open _>>_
open Canonical

variable
  n : ℕ
  l : List ℕ

-- data Canonical : (n : ℕ) -> Set where
--   CanZ : Canonical 0
--   CanS : {n : ℕ} -> (l : Canonical n) -> {k r : ℕ} -> (n < k) -> (r ≤ k) -> Canonical k

-- canonical-form-lemma : {n : ℕ} -> {l : List ℕ} -> (l' : n >> l) -> ∃ (λ cl -> l ≃ (immersion {n} cl))

>>-↓ : {n k r : ℕ} -> (k ≤ n) -> (n >> (k ↓ r))
>>-↓ {n} {zero} {zero} kn = []
>>-↓ {n} {suc k} {zero} kn = []
>>-↓ {n} {zero} {suc r} kn = []
>>-↓ {n} {suc k} {suc r} kn = k :⟨ kn ⟩: (>>-↓ (≤-down kn))

>>-lift : {m : ℕ} -> (n ≤ m) -> (n >> l) -> (m >> l)
>>-lift {m = m} nm [] = []
>>-lift {m = m} nm (k :⟨ p ⟩: l') = k :⟨ (≤-trans p nm) ⟩: >>-lift nm l'

canonical-lift : {m : ℕ} -> (n ≤ m) -> (cl : Canonical n) -> Σ (Canonical m) (λ cll -> immersion {n} cl ≡ immersion {m} cll)
canonical-lift {.0} nm CanZ = ?
canonical-lift {m} nm (CanS cl x x₁) = ?

immersion->> : {n : ℕ} -> Canonical n -> ∃ (λ l -> n >> l)
immersion->> {.0} CanZ = [] , []
immersion->> {n} (CanS {n'} cl {k} {r} nk rk) =
  let (l , p) = immersion->> {n'} cl
  in  l ++ (k ↓ r) , >>-++ (>>-lift (≤-down nk) p) (>>-↓ (≤-reflexive refl))

only-one-canonical : (cl1 cl2 : Canonical n) -> (immersion {n} cl1) ≃ (immersion {n} cl2) -> cl1 ≡ cl2
only-one-canonical {.0} CanZ CanZ pr = refl
only-one-canonical {n} (CanS cl1 x x₁) (CanS cl2 x₂ x₃) pr =
  let n'' = {!!}
      rec = only-one-canonical {n''} {!!} {!!} pr
  in  {!!}

identity-on-canonical-forms : (cl : Canonical n) -> (proj₁ (canonical-form-lemma (proj₂ (immersion->> {n} cl)))) ≡ cl
identity-on-canonical-forms {.0} CanZ = refl
identity-on-canonical-forms {n} (CanS {n'} cl x x₁) =
  let rec = identity-on-canonical-forms {n'} cl
  in  {!!}
