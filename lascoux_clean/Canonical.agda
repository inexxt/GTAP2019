{-# OPTIONS --without-K #-}
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

open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to ≤∎) hiding (_≡⟨_⟩_; _≡⟨⟩_)


open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)

open ≅*-Reasoning
open Relation.Binary.PropositionalEquality.≡-Reasoning

variable
  n : ℕ
  l : List ℕ

data Canonical : (n : ℕ) -> Set where
  CanZ : Canonical 0
  CanS : {n : ℕ} -> (l : Canonical n) -> {r : ℕ} -> (r ≤ suc n) -> Canonical (suc n)

immersion : {n : ℕ} -> Canonical n -> List ℕ
immersion {zero} CanZ = []
immersion {suc n} (CanS l {r} r≤1+n) = (immersion l) ++ (((suc n) ∸ r) ↓ r)

postulate
  canonical-eta : {n : ℕ} -> {cl1 cl2 : Canonical n} -> {r1 r2 : ℕ} -> (rn1 : r1 ≤ (suc n)) -> (rn2 : r2 ≤ (suc n)) -> (cl1 ≡ cl2) -> (r1 ≡ r2) -> (CanS cl1 rn1) ≡ (CanS cl2 rn2)

data _>>_ : ℕ -> List ℕ -> Set where
  [] : {n : ℕ} -> n >> []
  _:⟨_⟩:_ : {n : ℕ} -> {l : List ℕ} -> (k : ℕ) -> (k < n) -> n >> l -> n >> (k ∷ l)

extract-proof : {a : ℕ} -> (n >> (a ∷ l)) -> (a < n)
extract-proof (_ :⟨ p ⟩: _) = p

only-one≅-↓ : (n k1 : ℕ) -> (m : List ℕ) -> (n ↓ k1) ≅ m -> ⊥
only-one≅-↓ n k1 m (cancel≅ {n₁} l r .(n ↓ k1) .m defm defmf) = repeat-long-lemma n k1 n₁ l r defm
only-one≅-↓ n k1 m (swap≅ x l r .(n ↓ k1) .m defm defmf) = incr-long-lemma _ _ _ _ x l r defm
only-one≅-↓ n k1 m (long≅ {n₁} k l r .(n ↓ k1) .m defm defmf) =
  repeat-spaced-long-lemma n k1 (suc (k + n₁)) l ((n₁ ↓ (1 + k))) r defm

data _||_||_ (A : Set) (B : Set) (C : Set) : Set where
  R1 : A -> A || B || C
  R2 : B -> A || B || C
  R3 : C -> A || B || C

-- some technical lemmas about lists
lemma-l++2++r : (a : ℕ) -> (l1 r1 l2 r2 : List ℕ) -> (l1 ++ r1 ≡ l2 ++ a ∷ a ∷ r2)
                -> (Σ (List ℕ × List ℕ) (λ (rl2 , rr2) -> (r2 ≡ rl2 ++ rr2) × (l1 ≡ l2 ++ a ∷ a ∷ rl2) × (r1 ≡ rr2))) || -- the case when both a ∷ a are in left
                   (Σ (List ℕ × List ℕ) (λ (ll2 , lr2) -> (l2 ≡ ll2 ++ lr2) × (l1 ≡ ll2) × (r1 ≡ lr2 ++ a ∷ a ∷ r2))) || -- the case when both a ∷ a are in right
                   ((l1 ≡ l2 ++ [ a ]) × (r1 ≡ a ∷ r2)) -- the case when one a is in left, and one in right
lemma-l++2++r a [] r1 l2 r2 p = R2 (([] , l2) , (refl , (refl , p)))
lemma-l++2++r a (x ∷ []) r1 [] r2 p =
  let h = cut-tail p
  in  R3 ((cong [_] h) , (cut-head p))
lemma-l++2++r a (x ∷ x₁ ∷ l1) r1 [] r2 p =
  let h1 = cut-tail p
      h2 = cut-tail (cut-head p)
  in  R1 ((l1 , r1) , (cut-head (cut-head (≡-sym p)) , (head+tail h1 (head+tail h2 refl)) , refl))
lemma-l++2++r a (x ∷ l1) r1 (x₁ ∷ l2) r2 p with lemma-l++2++r a l1 r1 l2 r2 (cut-head p)
... | R1 ((fst , snd) , fst₁ , fst₂ , snd₁) = R1 ((fst , snd) , (fst₁ , ((head+tail (cut-tail p) fst₂) , snd₁)))
... | R2 ((fst , snd) , fst₁ , fst₂ , snd₁) = R2 (((x₁ ∷ fst) , snd) , ((cong (λ e -> x₁ ∷ e) fst₁) , ((head+tail (cut-tail p) fst₂) , snd₁)))
... | R3 (fst , snd) = R3 (head+tail (cut-tail p) fst , snd)


only-one≅-↓-↓ : (n k n1 k1 : ℕ) -> (m : List ℕ) -> (k + n < k1 + n1) -> ((n ↓ k) ++ (n1 ↓ k1)) ≅ m -> ⊥
only-one≅-↓-↓ n k n1 k1 m pkn (cancel≅ l r .((n ↓ k) ++ (n1 ↓ k1)) .m defm defmf) = {!   !}
only-one≅-↓-↓ n k n1 k1 m pkn (swap≅ x l r .((n ↓ k) ++ (n1 ↓ k1)) .m defm defmf) = {!   !}
only-one≅-↓-↓ n k n1 k1 m pkn (long≅ k₁ l r .((n ↓ k) ++ (n1 ↓ k1)) .m defm defmf) = {!   !}


only-one-canonical≅ : (cl : Canonical n) -> (m : List ℕ) -> (immersion {n} cl) ≅ m -> ⊥
only-one-canonical≅ cl m (cancel≅ l r .(immersion cl) .m defm defmf) = {!   !}
only-one-canonical≅ cl m (swap≅ x l r .(immersion cl) .m defm defmf) = {!   !}
only-one-canonical≅ cl m (long≅ k l r .(immersion cl) .m defm defmf) = {!   !}
