module ReductionProps where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; Σ; _×_; _,_; _,′_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)

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
open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to ≤∎) hiding (_≡⟨_⟩_; _≡⟨⟩_)
open Σ
open _>>_
open Canonical

variable
  n : ℕ
  l : List ℕ

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
  canonical-eta : {cl1 cl2 : Canonical n} -> {r1 r2 : ℕ} -> (rn1 : r1 ≤ (suc n)) -> (rn2 : r2 ≤ (suc n)) -> (cl1 ≡ cl2) -> (r1 ≡ r2) -> (CanS cl1 rn1) ≡ (CanS cl2 rn2)

≅-abs-l : {x : ℕ} -> (x ∷ []) ≅ [] -> ⊥
≅-abs-r : {x : ℕ} -> [] ≅ (x ∷ []) -> ⊥

≅-abs-l {n} (respects=r [] {r' = []} p refl x₁) = ≅-abs-l p
≅-abs-l {n} (respects=l {x₁ ∷ []} {l' = []} .[] p x refl) = ≅-abs-l p
≅-abs-l {n} (comm≅ p) = ≅-abs-r p

≅-abs-r {x} (respects=r [] {r' = x ∷ .[]} p refl refl) = ≅-abs-r p
≅-abs-r {n} (respects=l {[]} {y ∷ []} [] p x q) = ≅-abs-r p
≅-abs-r {n} (comm≅ p) = ≅-abs-l p

-- ≅-len : {m1 m2 : List ℕ} -> (m1 ≅ m2) -> (length m2 ≤ length m1)
-- ≅-len {.(_ ∷ _ ∷ [])} {.[]} cancel≅ = z≤n
-- ≅-len {.(_ ∷ _ ∷ [])} {.(_ ∷ _ ∷ [])} (swap≅ x) = s≤s (s≤s z≤n)
-- ≅-len {.(suc _ ∷ _ ∷ suc _ ∷ [])} {.(_ ∷ suc _ ∷ _ ∷ [])} braid≅ = s≤s (s≤s (s≤s z≤n))
-- ≅-len {m1} {m2} (respects=r l {r} {r'} p e1 e2) rewrite e1 rewrite e2 rewrite (length-++ l {r}) rewrite (length-++ l {r'}) =
--   let rec = ≅-len p
--   in  ≤-up2-+ rec
-- ≅-len {m1} {m2} (respects=l {l} {l'} r p e1 e2) rewrite e1 rewrite e2 rewrite (length-++ l {r}) rewrite (length-++ l' {r}) =
--   let rec = ≅-len p
--   in ≤-up2-r-+ rec
-- ≅-len {m1} {m2} (comm≅ p) = {!≅-len p!}

≃-abs : {x : ℕ} -> (x ∷ []) ≃ [] -> ⊥
≃-abs (trans≅ x refl) = ≅-abs-l x
≃-abs (trans≅ {m2 = []} x q) = ≅-abs-l x
≃-abs (trans≅ {m2 = x₁ ∷ m2} x q) = {!!}

ZeroCanonical : (n : ℕ) -> Canonical n
ZeroCanonical zero = CanZ
ZeroCanonical (suc n) = CanS (ZeroCanonical n) z≤n

≃-canonize : (cl : Canonical n) -> (l : List ℕ) -> (l' : (suc n) >> l) -> ((l , l') ≡ immersion->> {n} cl) -> (l ≅ []) -> cl ≡ ZeroCanonical n
≃-canonize CanZ .[] .[] refl q = refl
≃-canonize (CanS cl x) .(proj₁ (immersion->> cl) ++ (suc (suc _) ↓ _)) .(>>-++ (>>-suc (proj₂ (immersion->> cl))) (>>-↓ (s≤s (s≤s (≤-reflexive refl))))) refl q = {!!}

≃-down2 : {l1 l2 : List ℕ} -> ((n ∷ l1) ≃ (n ∷ l2)) -> (l1 ≃ l2)
≃-down2 {n} {[]} {[]} p = refl
≃-down2 {n} {[]} {x ∷ l2} p = {!!}
≃-down2 {n} {x ∷ l1} {l2} p = {!!}

≅-reverse : {l1 l2 : List ℕ} -> (l1 ≅ l2) -> (reverse l1 ≃ reverse l2)
≅-reverse .{_ ∷ _ ∷ []} {.[]} cancel≅ = cancel
≅-reverse .{_ ∷ _ ∷ []} .{_ ∷ _ ∷ []} (swap≅ x) = comm (swap x)
≅-reverse .{suc _ ∷ _ ∷ suc _ ∷ []} .{_ ∷ suc _ ∷ _ ∷ []} braid≅ = braid
≅-reverse {l1} {l2} (respects=r l {r1} {r2} p e1 e2) =
  ≃begin
    reverse l1
  ≃⟨ refl≡ (cong (λ x -> reverse x) e1) ⟩
    reverse (l ++ r1)
  ≃⟨ refl≡ (reverse-++-commute l r1) ⟩
    reverse r1 ++ reverse l
  ≃⟨ ++-respects-l (≅-reverse p) ⟩
    reverse r2 ++ reverse l
  ≃⟨ refl≡ (≡-sym (reverse-++-commute l r2)) ⟩
    reverse (l ++ r2)
  ≃⟨ refl≡ (cong (λ x -> reverse x) (≡-sym e2)) ⟩
    reverse l2
  ≃∎
≅-reverse {l1} {l2} (respects=l {l} {l'} r p e1 e2) =
  ≃begin
    reverse l1
  ≃⟨ refl≡ (cong (λ x -> reverse x) e1) ⟩
    reverse (l ++ r)
  ≃⟨ refl≡ (reverse-++-commute l r) ⟩
    reverse r ++ reverse l
  ≃⟨ ++-respects-r (≅-reverse p) ⟩
    reverse r ++ reverse l'
  ≃⟨ refl≡ (≡-sym (reverse-++-commute l' r)) ⟩
    reverse (l' ++ r)
  ≃⟨ refl≡ (cong (λ x -> reverse x) (≡-sym e2)) ⟩
    reverse l2
  ≃∎
≅-reverse {l1} {l2} (comm≅ p) = comm (≅-reverse p)

≃-reverse : {l1 l2 : List ℕ} -> (l1 ≃ l2) -> (reverse l1 ≃ reverse l2)
≃-reverse {l1} {.l1} refl = refl
≃-reverse {l1} {l2} (trans≅ p x) =
 let rec-l = ≅-reverse p
     rec-r = ≃-reverse x
 in  trans rec-l rec-r


stupid-lemma : {l r : List ℕ} -> {x : ℕ} -> n >> (x ∷ (l ++ r)) -> n >> (l ++ r) × (n > x)
stupid-lemma (x :⟨ p ⟩: m) = m , p

>>-part : {m : List ℕ} -> (l r : List ℕ) -> (l ++ r ≡ m) -> (n >> m) -> ((n >> l) × (n >> r))
>>-part {n} {m} [] r p mm rewrite p = [] , mm
>>-part {n} {m} (x ∷ l) r p mm =
  let (m , px) = stupid-lemma {n} {l} {r} (subst (λ y -> n >> y) (≡-sym p) mm)

      recl , recr = >>-part l r refl m
  in  (x :⟨ px ⟩: recl) , recr

-- -- this is not true :/
-- -- >>-≃-r : (l : List ℕ) -> (n >> l) -> (l2 : List ℕ) -> (l ≃ l2) -> (n >> l2)
-- -- >>-≃-r .(_ ∷ _ ∷ []) ll .[] cancel = []
-- -- >>-≃-r .(k ∷ k₁ ∷ []) (k :⟨ x₁ ⟩: (k₁ :⟨ x₂ ⟩: ll)) .(k₁ ∷ k ∷ []) (swap x) = k₁ :⟨ x₂ ⟩: (k :⟨ x₁ ⟩: ll)
-- -- >>-≃-r .(k ∷ suc k ∷ k ∷ []) (k :⟨ x ⟩: (.(suc k) :⟨ x₁ ⟩: (.k :⟨ x₂ ⟩: ll))) .(suc k ∷ k ∷ suc k ∷ []) braid = suc k :⟨ x₁ ⟩: (k :⟨ x₂ ⟩: (suc k :⟨ x₁ ⟩: ll))
-- -- >>-≃-r {n} l ll l2 (respects-r m {r} {r'} p x q) rewrite (≡-sym q) =
-- --   let lp , rp = >>-part m r x ll
-- --       rec = >>-≃-r r rp r' p
-- --   in  >>-++ {n} {m} {r'} lp rec
-- -- >>-≃-r {n} l ll l2 (respects-l {m} {m'} r p x q) rewrite (≡-sym q) =
-- --   let lp , rp = >>-part m r x ll
-- --       rec = >>-≃-r m lp m' p
-- --   in  >>-++ {n} {m'} {r} rec rp
-- -- >>-≃-r l ll .l refl = ll
-- -- >>-≃-r l ll l2 (trans {l} {l'} p p₃) = >>-≃-r l' (>>-≃-r l ll l' p) l2 p₃
-- -- >>-≃-r l ll l2 (comm p) = >>-≃-l l ll l2 p

only-one-canonical : (cl1 cl2 : Canonical n) -> (immersion {n} cl1) ≅ (immersion {n} cl2) -> cl1 ≡ cl2
only-one-canonical {.0} CanZ CanZ p = refl
only-one-canonical {suc n} (CanS cl1 {zero} pr1) (CanS cl2 {zero} pr2) p =
  let q = subst ((λ y -> (immersion cl1) ≅ y)) ++-unit (subst (λ x -> x ≅ (immersion cl2 ++ [])) ++-unit p)
      rec = only-one-canonical cl1 cl2 q
  in  canonical-eta pr1 pr2 rec refl
only-one-canonical {suc n} (CanS cl1 {zero} pr1) (CanS cl2 {suc r2} pr2) p = {!!}
only-one-canonical {suc n} (CanS cl1 {suc r1} pr1) (CanS cl2 {zero} pr2) p = {!!}
only-one-canonical {suc n} (CanS cl1 {suc r1} pr1) (CanS cl2 {suc r2} pr2) p =
  let rec = only-one-canonical {suc n} (CanS cl1 {r1} (≤-down pr1)) (CanS cl2 {r2} (≤-down pr2)) {!!}
  in  {!!}


-- -- identity-on-canonical-forms : (cl : Canonical n) -> (proj₁ (canonical-form-lemma (proj₂ (immersion->> {n} cl)))) ≡ cl
-- -- identity-on-canonical-forms {.0} CanZ = refl
-- -- identity-on-canonical-forms {n} (CanS {n'} cl x) =
-- --   let rec = identity-on-canonical-forms {n'} cl
-- --   in  {!!}
