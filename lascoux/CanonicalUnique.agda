{-# OPTIONS --allow-unsolved-metas #-}
module _ where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; _×_; _,_)
open import Relation.Nullary
open import Data.Empty
open import Data.Sum hiding (swap)
open import Data.Bool hiding (_<_; _≤_)
open import Data.Bool.Properties hiding (≤-reflexive)
open import Function

open import Arithmetic hiding (n)
open import DiamondCompact hiding (n ; l)

open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to ≤∎) hiding (_≡⟨_⟩_; _≡⟨⟩_)

variable
  n : ℕ

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)

_↓_ : (n : ℕ) -> (r : ℕ) -> List ℕ
zero ↓ r = []
suc n ↓ zero = []
suc n ↓ suc r = n ∷ n ↓ r

data Canonical : (n : ℕ) -> Set where
  CanZ : Canonical 0
  CanS : {n : ℕ} -> (l : Canonical n) -> {r : ℕ} -> (r ≤ suc n) -> Canonical (suc n)

immersion : {n : ℕ} -> Canonical n -> List ℕ
immersion {zero} CanZ = []
immersion {suc n} (CanS l {r} r≤1+n) = (immersion l) ++ ((suc n) ↓ r)

cut-head : (a1 a2 : ℕ) -> (l1 l2 : List ℕ) -> (a1 ∷ l1 ≡ a2 ∷ l2) -> (l1 ≡ l2)
cut-head a1 .a1 l1 .l1 refl = refl

abs-const-↓ : (n k a : ℕ) -> (l r : List ℕ) -> (n ↓ k) ≡ (l ++ a ∷ a ∷ r) -> ⊥
abs-const-↓ zero k a (x ∷ l) r ()
abs-const-↓ (suc zero) (suc k) a [] r ()
abs-const-↓ (suc (suc n)) (suc zero) a [] r ()
abs-const-↓ (suc (suc n)) (suc (suc k)) a [] r ()
abs-const-↓ (suc n) (suc k) a (x ∷ l) r p  = abs-const-↓ n k a l r (cut-head n x (n ↓ k) (l ++ a ∷ a ∷ r) p)

abs-inc-↓ : (n k a : ℕ) -> (l r : List ℕ) -> (n ↓ k) ≡ (l ++ a ∷ suc a ∷ r) -> ⊥
abs-inc-↓ n k a l r p = {!!}

abs-jump-↓ : (n k a b : ℕ) -> (suc a < b) -> (l r : List ℕ) -> (n ↓ k) ≡ (l ++ b ∷ a ∷ r) -> ⊥
abs-jump-↓ n k a l r p = {!!}

--- And versions for 2-⇣

abs-const2-↓ : (n1 k1 n2 k2 a : ℕ) -> (n1 < n2) -> (l r : List ℕ) -> (n1 ↓ k1) ++ (n2 ↓ k2) ≡ (l ++ a ∷ a ∷ r) -> ⊥
abs-const2-↓ zero k1 n2 k2 a pnn l r p = abs-const-↓ _ _ _ l r p
abs-const2-↓ (suc n1) zero n2 k2 a pnn l r p = abs-const-↓ _ _ _ l r p
abs-const2-↓ (suc zero) (suc k1) (suc .0) (suc k2) .0 (s≤s ()) [] .[] refl
abs-const2-↓ (suc (suc n1)) (suc zero) (suc .(suc n1)) (suc k2) .(suc n1) pnn [] .(suc n1 ↓ k2) refl = (⊥-elim (1+n≰n pnn))
abs-const2-↓ (suc n1) (suc k1) n2 k2 a pnn (x ∷ l) r p = abs-const2-↓ n1 k1 n2 k2 a (≤-down pnn) l r (cut-head _ _ _ _ p)

abs-braid2-↓ : (n1 k1 n2 k2 a : ℕ) -> (n1 < n2) -> (l r : List ℕ) -> (n1 ↓ k1) ++ (n2 ↓ k2) ≡ (l ++ suc a ∷ a ∷ suc a ∷ r) -> ⊥
abs-braid2-↓ n1 k1 n2 k2 a pnn l r p = {!!}

abs-jump2-↓ : (n1 k1 n2 k2 a b : ℕ) -> (n1 < n2) -> (suc a < b) -> (l r : List ℕ) -> (n1 ↓ k1) ++ (n2 ↓ k2) ≡ (l ++ b ∷ a ∷ r) -> ⊥
abs-jump2-↓ n1 k1 n2 k2 a b pnn pab l r p = {!!}

--- and versions for many-↓
abs-const-many-↓ : (n a : ℕ) -> (l r : List ℕ) -> (cl : Canonical n) -> (immersion {n} cl) ≡ (l ++ a ∷ a ∷ r) -> ⊥
abs-const-many-↓ .0 a [] r CanZ ()
abs-const-many-↓ .0 a (x ∷ l) r CanZ ()
abs-const-many-↓ .(suc _) a l r (CanS cl x) p = {!!}

abs-braid-many-↓ : (n a : ℕ) -> (l r : List ℕ) -> (cl : Canonical n) -> (immersion {n} cl) ≡ (l ++ suc a ∷ a ∷ suc a ∷ r) -> ⊥
abs-braid-many-↓ .0 a [] r CanZ ()
abs-braid-many-↓ .0 a (x ∷ l) r CanZ ()
abs-braid-many-↓ .(suc _) a l r (CanS cl x) p = {!!}

abs-jump-many-↓ : (n a b : ℕ) -> (suc a < b) -> (l r : List ℕ) -> (cl : Canonical n) -> (immersion {n} cl) ≡ (l ++ b ∷ a ∷ r) -> ⊥
abs-jump-many-↓ .0 a b pab [] r CanZ ()
abs-jump-many-↓ .0 a b pab (x ∷ l) r CanZ ()
abs-jump-many-↓ .(suc _) a b pab l r (CanS cl x) p = {!!}

only-one≅-↓ : (n k1 k2 : ℕ)  -> (k1 ≤ n) -> (k2 ≤ n) -> (n ↓ k1) ≅ (n ↓ k2) -> ⊥
only-one≅-↓ n k1 k2 pk1 pk2 (cancel≅ l r .(n ↓ k1) .(n ↓ k2) defm defmf) = abs-const-↓ _ _ _ l r defm
only-one≅-↓ n k1 k2 pk1 pk2 (swap≅ x l r .(n ↓ k1) .(n ↓ k2) defm defmf) = abs-jump-↓ _ _ _ _ x l r defm
only-one≅-↓ n k1 k2 pk1 pk2 (braid≅ l r .(n ↓ k1) .(n ↓ k2) defm defmf) = abs-inc-↓ _ _ _ l (_ ∷ r) defmf

++-∷ : {l r : List ℕ} -> l ++ n ∷ r ≡ (l ++ [ n ]) ++ r
++-∷ {n} {l} {r} = ≡-sym (++-assoc l (n ∷ []) r)

abs≅-↓ : (n k : ℕ) -> (k ≤ n) -> (m : List ℕ) -> ((n ↓ k) ≅ m) -> ⊥
abs≅-↓ n k pk m (cancel≅ l r .(n ↓ k) .m defm defmf) = abs-const-↓ _ _ _ l r defm
abs≅-↓ n k pk m (swap≅ x l r .(n ↓ k) .m defm defmf) = abs-jump-↓ _ _ _ _ x l r defm
abs≅-↓ n k pk m (braid≅ {n₁} l r .(n ↓ k) .m defm defmf) =
  let lemma = ≡-trans defm ++-∷
  in  abs-inc-↓ n k n₁ (l ++ [ suc n₁ ]) r lemma

one-reduction : (n : ℕ) -> (m : List ℕ) -> ((n ∷ []) ≅ m) -> ⊥
one-reduction zero m p = abs≅-↓ 1 1 (s≤s z≤n) m p
one-reduction (suc n) m p = abs≅-↓ (suc (suc n)) 1 (s≤s z≤n) m p

abs2≅-↓ : (n1 k1 n2 k2 : ℕ) -> (k1 ≤ n1) -> (k2 ≤ n2) -> (n1 < n2) -> (m : List ℕ) -> ((n1 ↓ k1) ++ (n2 ↓ k2)) ≅ m -> ⊥
abs2≅-↓ n1 k1 n2 k2 pkn1 pkn2 pnn m (cancel≅ l r .((n1 ↓ k1) ++ (n2 ↓ k2)) .m defm defmf) = abs-const2-↓ n1 k1 n2 k2 _ pnn l r defm
abs2≅-↓ n1 k1 n2 k2 pkn1 pkn2 pnn m (swap≅ x l r .((n1 ↓ k1) ++ (n2 ↓ k2)) .m defm defmf) = abs-jump2-↓ n1 k1 n2 k2 _ _ pnn x l r defm
abs2≅-↓ n1 k1 n2 k2 pkn1 pkn2 pnn m (braid≅ l r .((n1 ↓ k1) ++ (n2 ↓ k2)) .m defm defmf) = abs-braid2-↓ n1 k1 n2 k2 _ pnn l r defm

only-one-canonical≅ : (cl : Canonical n) -> (m : List ℕ) -> (immersion {n} cl) ≅ m -> ⊥
only-one-canonical≅ cl m (cancel≅ l r .(immersion cl) .m defm defmf) = abs-const-many-↓ _ _ _ r cl defm
only-one-canonical≅ cl m (swap≅ x l r .(immersion cl) .m defm defmf) = abs-jump-many-↓ _ _ _ x l r cl defm
only-one-canonical≅ cl m (braid≅ l r .(immersion cl) .m defm defmf) = abs-braid-many-↓ _ _ _ r cl defm

≡immersion : (cl1 cl2 : Canonical n) -> (immersion {n} cl1 ≡ immersion {n} cl2) -> cl1 ≡ cl2
≡immersion CanZ CanZ refl = refl
≡immersion (CanS cl1 x) (CanS cl2 x₁) p = {!!}

only-one-canonical≅* : (cl1 cl2 : Canonical n) -> (m1 m2 : List ℕ) -> (immersion {n} cl1 ≡ m1) -> (immersion {n} cl2 ≡ m2) -> (m1 ≅* m2)-> cl1 ≡ cl2
only-one-canonical≅* cl1 cl2 m1 .m1 pm1 pm2 refl = ≡immersion _ _ (≡-trans pm1 (≡-sym pm2))
only-one-canonical≅* cl1 cl2 m1 m2 pm1 pm2 (trans≅ x p) =
  let ss = subst (λ t → t ≅ _) (≡-sym pm1) x
  in  ⊥-elim (only-one-canonical≅ cl1 _ ss)

only-one-canonical≃ : (cl1 cl2 : Canonical n) -> (m1 m2 : List ℕ) -> (immersion {n} cl1 ≡ m1) -> (immersion {n} cl2 ≡ m2) -> (m1 ≃ m2) -> cl1 ≡ cl2
only-one-canonical≃ cl1 cl2 m1 .m1 pm1 pm2 (R refl refl) = ≡immersion _ _ (≡-trans pm1 (≡-sym pm2))
only-one-canonical≃ cl1 cl2 m1 m2 pm1 pm2 (R refl (trans≅ x p2)) =
  let ss = subst (λ t → t ≅ _) (≡-sym pm2) x
  in  ⊥-elim (only-one-canonical≅ cl2 _ ss)
only-one-canonical≃ cl1 cl2 m1 m2 pm1 pm2 (R (trans≅ x p1) p2) =
  let ss = subst (λ t → t ≅ _) (≡-sym pm1) x
  in  ⊥-elim (only-one-canonical≅ cl1 _ ss)
