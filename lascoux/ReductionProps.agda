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

-- >>-lift : {m : ℕ} -> (n ≤ m) -> (n >> l) -> (m >> l)
-- >>-lift {m = m} nm [] = []
-- >>-lift {m = m} nm (k :⟨ p ⟩: l') = k :⟨ (≤-trans p nm) ⟩: >>-lift nm l'

>>-suc : (n >> l) -> ((suc n) >> l)
>>-suc  [] = []
>>-suc  (k :⟨ p ⟩: l') = k :⟨ ≤-up p ⟩: >>-suc l'

++-≡2 : {la lb lc ld : List ℕ} -> (la ≡ lb) -> (lc ≡ ld) -> (la ++ lc) ≡ (lb ++ ld)
++-≡2 {la} {lb} {lc} {ld} pab pcd =
  begin
    la ++ lc
  ≡⟨ cong (λ x -> x ++ lc) pab ⟩
    lb ++ lc
  ≡⟨ cong (λ x -> lb ++ x) pcd ⟩
    lb ++ ld
  ∎

-- canonical-lift : {m : ℕ} -> (n ≤ m) -> (cl : Canonical n) -> Σ (Canonical m) (λ cll -> immersion {n} cl ≡ immersion {m} cll)
-- canonical-lift {n} {m} nm cl = {!!}

canonical-suc : (cl : Canonical n) -> Σ (Canonical (suc n)) (λ cll -> immersion {n} cl ≡ immersion {suc n} cll)
canonical-suc {n} cl = (CanS cl {r = 0} z≤n) , ≡-sym ++-unit

immersion->> : {n : ℕ} -> Canonical n -> ∃ (λ l -> (suc n) >> l)
immersion->> {.0} CanZ = [] , []
immersion->> {n} (CanS {n'} cl {r} rn) =
  let (l , p) = immersion->> {n'} cl
  in  l ++ ((suc n) ↓ r) , >>-++ (>>-suc p) (>>-↓ (≤-reflexive refl))

postulate
  ≡-canonical : {cl1 cl2 : Canonical n} -> {r1 r2 : ℕ} -> (rn1 : r1 ≤ (suc n)) -> (rn2 : r2 ≤ (suc n)) -> (cl1 ≡ cl2) -> (r1 ≡ r2) -> (CanS cl1 rn1) ≡ (CanS cl2 rn2)

≃-abs-l : {x : ℕ} -> (x ∷ []) ≃ [] -> ⊥
≃-abs-r : {x : ℕ} -> [] ≃ (x ∷ []) -> ⊥


≃-abs-l {n} (respects-r [] {r' = []} p refl x₁) = ≃-abs-l p
≃-abs-l {n} (respects-l {x₁ ∷ []} {l' = []} .[] p x refl) = ≃-abs-l p
≃-abs-l {n} (comm p) = ≃-abs-r p
≃-abs-l {n} (trans {l' = []} p q) = ≃-abs-l p
≃-abs-l {n} (trans {l' = x ∷ []} p q) = ≃-abs-l q
≃-abs-l {n} (trans {l' = x ∷ x₁ ∷ l'} p q) = {!!}

≃-abs-r {x} (respects-r [] {r' = x ∷ .[]} p refl refl) = ≃-abs-r p
≃-abs-r {n} (respects-l {[]} {y ∷ []} [] p x q) = ≃-abs-r p
≃-abs-r {n} (comm p) = ≃-abs-l p
≃-abs-r {n} (trans {l' = []} p q) = ≃-abs-r q
≃-abs-r {n} (trans {l' = x ∷ []} p q) = ≃-abs-r p
≃-abs-r {n} (trans {l' = x ∷ x₁ ∷ l'} p q) = {!!}

-- ≃-abs (trans {x ∷ []} {l'} {[]} (l≃l') (l'≃l'')) = ?
-- ≃-abs {suc x} p = {!!}
-- ≃-abs (++-respects-r {l} {m} {m'} (m≃m')) = ?
-- ≃-abs (++-respects-l {l} {l'} {m} (l≃l')) = ?
-- ≃-abs (comm {l} {l'} (l≃l')) = ?
-- ≃-abs (trans {l} {l'} {l''} (l≃l') (l'≃l'')) = ?


only-one-canonical : (cl1 cl2 : Canonical n) -> (immersion {n} cl1) ≃ (immersion {n} cl2) -> cl1 ≡ cl2
only-one-canonical {.0} CanZ CanZ pr = refl
only-one-canonical {.(suc n1)} (CanS {n1} cl1 {zero} rn1) (CanS {.n1} cl2 {zero} rn2) pr =
  let rec = only-one-canonical cl1 cl2 (trans (refl≡ (≡-sym ++-unit)) (trans pr (refl≡ ++-unit)))
  in  ≡-canonical rn1 rn2 rec refl
only-one-canonical {.1} (CanS {.0} CanZ {zero} rn1) (CanS {.0} CanZ {suc r2} rn2) pr = {!!}
only-one-canonical {.(suc (suc _))} (CanS {.(suc _)} (CanS cl1 x) {zero} rn1) (CanS {.(suc _)} cl2 {suc r2} rn2) pr = {!!} -- contradiction
only-one-canonical {.(suc n1)} (CanS {n1} cl1 {suc r1} rn1) (CanS {.n1} cl2 {zero} rn2) pr = {!!} -- contradiction
only-one-canonical {.(suc n1)} (CanS {n1} cl1 {suc r1} rn1) (CanS {.n1} cl2 {suc r2} rn2) pr =
  let rec = only-one-canonical cl1 cl2 {!!}
  in  ≡-canonical rn1 rn2 rec {!!}

  -- let n'' = {!!}
  --     rec = only-one-canonical {n''} {!!} {!!} pr
  -- in  {!!}

-- identity-on-canonical-forms : (cl : Canonical n) -> (proj₁ (canonical-form-lemma (proj₂ (immersion->> {n} cl)))) ≡ cl
-- identity-on-canonical-forms {.0} CanZ = refl
-- identity-on-canonical-forms {n} (CanS {n'} cl x) =
--   let rec = identity-on-canonical-forms {n'} cl
--   in  {!!}
