{-# OPTIONS --allow-unsolved-metas --without-K #-}
module _ where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (Σ; ∃; _×_; _,_)

open import Relation.Nullary
open import Data.Empty
open import Data.Sum hiding (swap)
open import Data.Bool hiding (_<_; _≤_; _≟_; _<?_)
open import Data.Bool.Properties hiding (≤-reflexive; ≤-trans; _≟_; _<?_)
open import Function

open import Arithmetic hiding (n)
open import Lists
open import Compact hiding (n; l)
open import ImpossibleLemmas
open import SwapLemmas

open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to ≤∎) hiding (_≡⟨⟩_)


open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)

open ≅*-Reasoning
open Relation.Binary.PropositionalEquality.≡-Reasoning
open _⊎_


variable
  n : ℕ
  l : List ℕ

data Canonical : (n : ℕ) -> Set where
  CanZ : Canonical 0
  CanS : {n : ℕ} -> (l : Canonical n) -> {r : ℕ} -> (r ≤ suc n) -> Canonical (suc n)

immersion : {n : ℕ} -> Canonical n -> List ℕ
immersion {zero} CanZ = []
immersion {suc n} (CanS l {r} r≤1+n) = (immersion l) ++ (((suc n) ∸ r) ↓ r)

canonical-lift : {n : ℕ} -> (m : ℕ) -> (n ≤ m) -> (cln : Canonical n) -> Σ (Canonical m) (λ clm -> immersion {m} clm ≡ immersion {n} cln)
canonical-lift {n} m p cln with ≤-∃ _ _ p
canonical-lift {.m} m p cln | zero , refl = cln , refl
canonical-lift {n} .(suc (fst + n)) p cln | suc fst , refl =
  let rec-m , rec-p = canonical-lift {n} (fst + n) (≤-up-+ rrr) cln
  in  (CanS rec-m z≤n) , (≡-trans ++-unit rec-p)

canonical-append : {n : ℕ} -> (cl : Canonical n) -> (x : ℕ) -> (n ≤ x) -> ∃ (λ clx -> immersion {suc x} clx ≡ immersion {n} cl ++ [ x ])
canonical-append cl x px =
  let lifted-m , lifted-p = canonical-lift x px cl
  in  CanS lifted-m (s≤s z≤n) , start+end lifted-p refl

postulate
  canonical-eta : {n : ℕ} -> {cl1 cl2 : Canonical n} -> {r1 r2 : ℕ} -> (rn1 : r1 ≤ (suc n)) -> (rn2 : r2 ≤ (suc n)) -> (cl1 ≡ cl2) -> (r1 ≡ r2) -> (CanS cl1 rn1) ≡ (CanS cl2 rn2)

data _>>_ : ℕ -> List ℕ -> Set where
  [] : {n : ℕ} -> n >> []
  _:⟨_⟩:_ : {n : ℕ} -> {l : List ℕ} -> (k : ℕ) -> (k < n) -> n >> l -> n >> (k ∷ l)

extract-proof : {a : ℕ} -> (n >> (a ∷ l)) -> (a < n)
extract-proof (_ :⟨ p ⟩: _) = p

final≅-↓ : (n k1 : ℕ) -> (m : List ℕ) -> (n ↓ k1) ≅ m -> ⊥
final≅-↓ n k1 m (cancel≅ {n₁} l r .(n ↓ k1) .m defm defmf) = repeat-long-lemma n k1 n₁ l r defm
final≅-↓ n k1 m (swap≅ x l r .(n ↓ k1) .m defm defmf) = incr-long-lemma _ _ _ _ x l r defm
final≅-↓ n k1 m (long≅ {n₁} k l r .(n ↓ k1) .m defm defmf) =
  repeat-spaced-long-lemma n k1 (suc (k + n₁)) l ((n₁ ↓ (1 + k))) r defm

data _||_||_ (A : Set) (B : Set) (C : Set) : Set where
  R1 : A -> A || B || C
  R2 : B -> A || B || C
  R3 : C -> A || B || C

-- a technical lemma about splitting lists
lemma-l++2++r : (a b : ℕ) -> (l1 r1 l2 r2 : List ℕ) -> (l1 ++ r1 ≡ l2 ++ a ∷ b ∷ r2)
                -> (Σ (List ℕ × List ℕ) (λ (rl2 , rr2) -> (r2 ≡ rl2 ++ rr2) × (l1 ≡ l2 ++ a ∷ b ∷ rl2) × (r1 ≡ rr2))) || -- the case when both a ∷ b are in left
                   (Σ (List ℕ × List ℕ) (λ (ll2 , lr2) -> (l2 ≡ ll2 ++ lr2) × (l1 ≡ ll2) × (r1 ≡ lr2 ++ a ∷ b ∷ r2))) || -- the case when both a ∷ b are in right
                   ((l1 ≡ l2 ++ [ a ]) × (r1 ≡ b ∷ r2)) -- the case when one a is in left, and b in right
lemma-l++2++r a b [] r1 l2 r2 p = R2 (([] , l2) , (refl , (refl , p)))
lemma-l++2++r a b (x ∷ []) r1 [] r2 p =
  let h = cut-tail p
  in  R3 ((cong [_] h) , (cut-head p))
lemma-l++2++r a b (x ∷ x₁ ∷ l1) r1 [] r2 p =
  let h1 = cut-tail p
      h2 = cut-tail (cut-head p)
  in  R1 ((l1 , r1) , (cut-head (cut-head (≡-sym p)) , (head+tail h1 (head+tail h2 refl)) , refl))
lemma-l++2++r a b (x ∷ l1) r1 (x₁ ∷ l2) r2 p with lemma-l++2++r a b l1 r1 l2 r2 (cut-head p)
... | R1 ((fst , snd) , fst₁ , fst₂ , snd₁) = R1 ((fst , snd) , (fst₁ , ((head+tail (cut-tail p) fst₂) , snd₁)))
... | R2 ((fst , snd) , fst₁ , fst₂ , snd₁) = R2 (((x₁ ∷ fst) , snd) , ((cong (λ e -> x₁ ∷ e) fst₁) , ((head+tail (cut-tail p) fst₂) , snd₁)))
... | R3 (fst , snd) = R3 (head+tail (cut-tail p) fst , snd)


final≅-↓-↓ : (n k n1 k1 : ℕ) -> (m : List ℕ) -> (k + n < k1 + n1) -> ((n ↓ k) ++ (n1 ↓ k1)) ≅ m -> ⊥
final≅-↓-↓ n k n1 k1 m pkn (cancel≅ {n₁} l r .((n ↓ k) ++ (n1 ↓ k1)) .m defm defmf) with (lemma-l++2++r n₁ n₁ (n ↓ k) (n1 ↓ k1) l r defm)
... | q = {! q  !}
final≅-↓-↓ n k n1 k1 m pkn (swap≅ x l r .((n ↓ k) ++ (n1 ↓ k1)) .m defm defmf) with (lemma-l++2++r _ _ (n ↓ k) (n1 ↓ k1) l r defm)
... | q = {!   !}
final≅-↓-↓ n k n1 k1 m pkn (long≅ k₁ l r .((n ↓ k) ++ (n1 ↓ k1)) .m defm defmf) = {!   !}

++-assoc-≡ : {l r1 r2 m : List ℕ} -> m ≡ ((l ++ r1) ++ r2) -> m ≡ (l ++ (r1 ++ r2))
++-assoc-≡ {l} {r1} {r2} {m} p = ≡-trans p (++-assoc l r1 r2)

final≅-canonical : (cl : Canonical n) -> (m mf : List ℕ) -> (defm : m ≡ (immersion {n} cl)) -> m ≅ mf -> ⊥
final≅-canonical {zero} CanZ .[] mf refl p = empty-reduction p
final≅-canonical {suc zero} (CanS CanZ {zero} x) .[] mf refl p = empty-reduction p
final≅-canonical {suc zero} (CanS CanZ {suc zero} (s≤s x)) .(0 ∷ []) mf refl p = one-reduction p
final≅-canonical {suc (suc n)} (CanS (CanS cl x₁) x) m mf defm (cancel≅ {n₁} l r .m .mf defm₁ defmf) rewrite (++-assoc-≡ {l = immersion cl} defm) with (lemma-l++2++r n₁ n₁ (immersion cl) _ l r defm₁)
... | p = {!   !}
final≅-canonical {suc (suc n)} (CanS (CanS cl x₁) x) m mf defm (swap≅ x₂ l r .m .mf defm₁ defmf) rewrite (++-assoc-≡ {l = immersion cl} defm) with (lemma-l++2++r _ _ (immersion cl) _ l r defm₁)
... | p = {!   !}
final≅-canonical {suc (suc n)} (CanS (CanS cl x₁) x) m mf defm (long≅ k l r .m .mf defm₁ defmf) = {!   !}
