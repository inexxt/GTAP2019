{-# OPTIONS --without-K #-}
module Lists where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; _×_; _,_)

open import Relation.Nullary
open import Data.Empty
open import Data.Sum hiding (swap)
open import Data.Bool hiding (_<_; _≤_)
open import Data.Bool.Properties hiding (≤-reflexive; ≤-trans)
open import Function

open import Arithmetic hiding (n)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)

open Relation.Binary.PropositionalEquality.≡-Reasoning


_↓_ : (n : ℕ) -> (k : ℕ) -> List ℕ
n ↓ 0 = []
n ↓ (suc k) = (k + n) ∷ (n ↓ k)

++-unit : {l : List ℕ} -> l ++ [] ≡ l
++-unit {[]} = refl
++-unit {x ∷ l} rewrite (++-unit {l}) = refl

cut-head : {a1 a2 : ℕ} -> {l1 l2 : List ℕ} -> (a1 ∷ l1 ≡ a2 ∷ l2) -> (l1 ≡ l2)
cut-head {a1} {.a1} {l1} {.l1} refl = refl

cut-tail : {a1 a2 : ℕ} -> {l1 l2 : List ℕ} -> (a1 ∷ l1 ≡ a2 ∷ l2) -> (a1 ≡ a2)
cut-tail {a1} {.a1} {l1} {.l1} refl = refl

cut-t1 : {a1 a2 : ℕ} -> {l1 l2 : List ℕ} -> (a1 ∷ l1 ≡ a2 ∷ l2) -> (a1 ≡ a2)
cut-t1 {a1} {.a1} {l1} {.l1} refl = refl

cut-t2 : {a1 a2 b1 b2 : ℕ} -> {l1 l2 : List ℕ} -> (a1 ∷ b1 ∷ l1 ≡ a2 ∷ b2 ∷ l2) -> (b1 ≡ b2)
cut-t2 {l1 = l1} {l2 = .l1} refl = refl

cut-t3 : {a1 a2 b1 b2 c1 c2 : ℕ} -> {l1 l2 : List ℕ} -> (a1 ∷ b1 ∷ c1 ∷ l1 ≡ a2 ∷ b2 ∷ c2 ∷ l2) -> (c1 ≡ c2)
cut-t3 {l1 = l1} {l2 = .l1} refl = refl

cut-t4 : {a1 a2 b1 b2 c1 c2 d1 d2 : ℕ} -> {l1 l2 : List ℕ} -> (a1 ∷ b1 ∷ c1 ∷ d1 ∷ l1 ≡ a2 ∷ b2 ∷ c2 ∷ d2 ∷ l2) -> (d1 ≡ d2)
cut-t4 {l1 = l1} {l2 = .l1} refl = refl

cut-h2 : {a1 a2 b1 b2 : ℕ} -> {l1 l2 : List ℕ} -> (a1 ∷ b1 ∷ l1 ≡ a2 ∷ b2 ∷ l2) -> (l1 ≡ l2)
cut-h2 {l1 = l1} {l2 = .l1} refl = refl

cut-h3 : {a1 a2 b1 b2 c1 c2 : ℕ} -> {l1 l2 : List ℕ} -> (a1 ∷ b1 ∷ c1 ∷ l1 ≡ a2 ∷ b2 ∷ c2 ∷ l2) -> (l1 ≡ l2)
cut-h3 {l1 = l1} {l2 = .l1} refl = refl

cut-h4 : {a1 a2 b1 b2 c1 c2 d1 d2 : ℕ} -> {l1 l2 : List ℕ} -> (a1 ∷ b1 ∷ c1 ∷ d1 ∷ l1 ≡ a2 ∷ b2 ∷ c2 ∷ d2 ∷ l2) -> (l1 ≡ l2)
cut-h4 {l1 = l1} {l2 = .l1} refl = refl

head+tail : {h1 h2 : ℕ} -> {t1 t2 : List ℕ} -> (h1 ≡ h2) -> (t1 ≡ t2) -> (h1 ∷ t1) ≡ (h2 ∷ t2)
head+tail refl refl = refl

start+end : {h1 h2 : List ℕ} -> {t1 t2 : List ℕ} -> (h1 ≡ h2) -> (t1 ≡ t2) -> (h1 ++ t1) ≡ (h2 ++ t2)
start+end refl refl = refl


↓-+ : (n k1 k2 : ℕ) -> n ↓ (k1 + k2) ≡ ((n + k2) ↓ k1) ++ (n ↓ k2)
↓-+ n zero k2 = refl
↓-+ n (suc k1) k2 rewrite (↓-+ n k1 k2) rewrite (+-comm n k2) = head+tail (+-assoc k1 k2 n) refl

_↑_ : (n : ℕ) -> (k : ℕ) -> List ℕ
n ↑ 0 = []
n ↑ (suc k) = n ∷ (suc n ↑ k)

++-↓ : (n k : ℕ) -> ((suc n) ↓ k) ++ [ n ] ≡ n ↓ (suc k)
++-↓ n zero = refl
++-↓ n (suc k) rewrite ++-↓ n k = head+tail (+-three-assoc {k} {1} {n}) refl

++-↑ : (n k : ℕ) -> (n ↑ k) ++ [ k + n ] ≡ n ↑ (suc k)
++-↑ n zero = refl
++-↑ n (suc k) rewrite ≡-sym (++-↑ (suc n) k) rewrite (+-three-assoc {k} {1} {n}) = refl

rev : List ℕ -> List ℕ
rev [] = []
rev (x ∷ l) = (rev l) ++ [ x ]

rev-d : (k p : ℕ) -> rev (k ↓ p) ≡ k ↑ p
rev-d k zero = refl
rev-d k (suc p) rewrite (rev-d k p) = ++-↑ k p

rev-u : (k p : ℕ) -> rev (k ↑ p) ≡ k ↓ p
rev-u k zero = refl
rev-u k (suc p) rewrite (rev-u (suc k) p) = ++-↓ k p

rev-++ : (l r : List ℕ) -> rev (l ++ r) ≡ (rev r) ++ (rev l)
rev-++ [] r = ≡-sym ++-unit
rev-++ (x ∷ l) r =
  let rec = start+end (rev-++ l r) refl
  in  ≡-trans rec (++-assoc (rev r) (rev l) (x ∷ []))

rev-rev : {l : List ℕ} -> l ≡ rev (rev l)
rev-rev {[]} = refl
rev-rev {x ∷ l} = ≡-trans (head+tail refl (rev-rev {l})) (≡-sym (rev-++ (rev l) [ x ]))

telescope-rev : (n k : ℕ) -> (r : List ℕ) -> ((rev (suc (suc n) ↑ k) ++ suc n ∷ []) ++ n ∷ []) ++ r ≡ (n ↓ (2 + k)) ++ r
telescope-rev n k r =
  begin
    ((rev (suc (suc n) ↑ k) ++ suc n ∷ []) ++ n ∷ []) ++ r
  ≡⟨ start+end (start+end (start+end (rev-u (2 + n) k) refl) refl) refl ⟩
    (((suc (suc n) ↓ k) ++ suc n ∷ []) ++ n ∷ []) ++ r
  ≡⟨ start+end (start+end (++-↓ (1 + n) k) refl) refl ⟩
    (((suc n) ↓ (1 + k)) ++ n ∷ []) ++ r
  ≡⟨ start+end (++-↓ n (1 + k)) refl ⟩
    (n ↓ (2 + k)) ++ r
  ∎

-- highly specific lemma...
telescope-l-rev-+1 : (n k : ℕ) -> (l r : List ℕ) -> ((((l ++ rev ((3 + n) ↑ k)) ++ (2 + n) ∷ []) ++ (1 + n) ∷ []) ++ n ∷ []) ++ r ≡ l ++ (n ↓ (3 + k)) ++ r
telescope-l-rev-+1 n k l r =
  begin
    ((((l ++ (rev ((suc (suc (suc n)) ↑ k)))) ++ suc (suc n) ∷ []) ++ suc n ∷ []) ++ n ∷ []) ++ r
  ≡⟨ ++-assoc (((l ++ rev (suc (suc (suc n)) ↑ k)) ++ suc (suc n) ∷ []) ++ suc n ∷ []) (n ∷ []) r ⟩
    _
  ≡⟨ ++-assoc ((l ++ rev (suc (suc (suc n)) ↑ k)) ++ suc (suc n) ∷ []) (suc n ∷ []) (n ∷ r) ⟩
    _
  ≡⟨ ++-assoc (l ++ rev (suc (suc (suc n)) ↑ k)) (suc (suc n) ∷ []) (suc n ∷ n ∷ r) ⟩
    _
  ≡⟨ ++-assoc (l) (rev (suc (suc (suc n)) ↑ k)) (suc (suc n) ∷ suc n ∷ n ∷ r) ⟩
    l ++ (rev (suc (suc (suc n)) ↑ k) ++ suc (suc n) ∷ suc n ∷ n ∷ r)
  ≡⟨ start+end (refl {x = l}) (≡-sym (++-assoc (rev (suc (suc (suc n)) ↑ k)) (suc (suc n) ∷ []) _)) ⟩
    l ++ ((rev (suc (suc (suc n)) ↑ k) ++ suc (suc n) ∷ []) ++ suc n ∷ n ∷ r)
  ≡⟨ start+end (refl {x = l}) (≡-sym (++-assoc (rev (suc (suc (suc n)) ↑ k) ++ suc (suc n) ∷ []) (suc n ∷ []) _)) ⟩
    l ++ (((rev (suc (suc (suc n)) ↑ k) ++ suc (suc n) ∷ []) ++ suc n ∷ []) ++ n ∷ r)
  ≡⟨ start+end (refl {x = l}) (≡-sym (++-assoc _ (n ∷ []) r)) ⟩
    l ++ ((((rev (suc (suc (suc n)) ↑ k) ++ suc (suc n) ∷ []) ++ suc n ∷ []) ++ n ∷ []) ++ r)
  ≡⟨ start+end (refl {x = l}) (start+end (telescope-rev (1 + n) k [ n ]) (refl {x = r})) ⟩
    l ++ ((((suc n) ↓ (2 + k)) ++ n ∷ []) ++ r)
  ≡⟨ start+end (refl {x = l}) (start+end (++-↓ n (suc (suc k))) (refl {x = r}))  ⟩
    _
  ∎

++-empty : (l r : List ℕ) -> (l ++ r) ≡ l -> (r ≡ [])
++-empty [] r p = p
++-empty (x ∷ l) r p = ++-empty l r (cut-head p)

[]-abs : {x : ℕ} -> {l : List ℕ} -> (x ∷ l) ≡ [] -> ⊥
[]-abs ()


_↓↓_,_ : (n : ℕ) -> (k : ℕ) -> (k ≤ n) -> List ℕ
n ↓↓ zero , z≤n = []
suc n ↓↓ suc k , s≤s p = n ∷ (n ↓↓ k , p)

↓↓-↓ : (n : ℕ) -> (k : ℕ) -> (p : k ≤ k + n) -> (((k + n) ↓↓ k , p) ≡ n ↓ k)
↓↓-↓ n zero z≤n = refl
↓↓-↓ n (suc k) (s≤s p) rewrite (↓↓-↓ n k p) = refl

↓-↓↓ : (n : ℕ) -> (k : ℕ) -> (p : k ≤ n) -> (n ↓↓ k , p) ≡ ((n ∸ k) ↓ k)
↓-↓↓ n zero z≤n = refl
↓-↓↓ (suc n) (suc k) (s≤s p) rewrite (↓-↓↓ n k p) = head+tail (≡-sym (plus-minus p)) refl

-- ↓↓-rec : {n k : ℕ} -> (k < n) -> (n ↓↓ suc k) ≡ (n ↓↓ k) ++ [ n ∸ (k + 1) ]
-- ↓↓-rec {suc zero} {zero} (s≤s z≤n) = refl
-- ↓↓-rec {suc (suc n)} {zero} (s≤s z≤n) = refl
-- ↓↓-rec {suc (suc n)} {suc k} (s≤s p) = cong (λ l -> suc n ∷ l) (↓↓-rec p)
