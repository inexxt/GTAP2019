{-# OPTIONS --without-K #-}
module ImpossibleLemmas where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties

open import Relation.Nullary
open import Data.Empty

open import Arithmetic hiding (n)
open import Lists
open import Compact hiding (n; l)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)

open ≅*-Reasoning
open Relation.Binary.PropositionalEquality.≡-Reasoning

repeat-long-lemma : (n k n1 : ℕ) -> (l r : List ℕ) -> (n ↓ k) ≡ (l ++ n1 ∷ n1 ∷ r) -> ⊥
repeat-long-lemma n zero n1 [] r ()
repeat-long-lemma n zero n1 (x ∷ l) r ()
repeat-long-lemma n (suc (suc k)) n1 [] r p =
  abs-refl (≤-trans (≤-reflexive (cut-t1 p)) (≤-reflexive (≡-sym (cut-t2 p))))
repeat-long-lemma n (suc k) n1 (x ∷ l) r p = repeat-long-lemma n k n1 l r (cut-head p)

repeat-long-lemma-rev : (n k n1 : ℕ) -> (l r : List ℕ) -> (n ↑ k) ≡ (l ++ n1 ∷ n1 ∷ r) -> ⊥
repeat-long-lemma-rev n zero n1 [] r ()
repeat-long-lemma-rev n zero n1 (x ∷ l) r ()
repeat-long-lemma-rev n (suc zero) n1 [] r ()
repeat-long-lemma-rev n (suc (suc k)) n1 [] r ()
repeat-long-lemma-rev n (suc k) n1 (x ∷ l) r p = repeat-long-lemma-rev (suc n) k n1 l r (cut-head p)


incr-long-lemma-rev : (n k n1 k1 : ℕ) -> (suc k1 < n1) -> (l r : List ℕ) -> (n ↑ k) ≡ (l ++ k1 ∷ n1 ∷ r) -> ⊥
incr-long-lemma-rev n (suc (suc k)) .(suc n) .n pkn [] .(suc (suc n) ↑ k) refl = abs-refl pkn
incr-long-lemma-rev n (suc k) n1 k1 pkn (x ∷ l) r p = incr-long-lemma-rev (suc n) k n1 k1 pkn l r (cut-head p)

incr-long-lemma : (n k n1 k1 : ℕ) -> (suc k1 < n1) -> (l r : List ℕ) -> (n ↓ k) ≡ (l ++ n1 ∷ k1 ∷ r) -> ⊥
incr-long-lemma n k n1 k1 p l r q =
  let pp =
        begin
          (n ↑ k)
        ≡⟨ ≡-sym (rev-d n k) ⟩
          rev (n ↓ k)
        ≡⟨ cong rev q ⟩
          rev (l ++ n1 ∷ k1 ∷ r)
        ≡⟨ rev-++ l (n1 ∷ k1 ∷ r) ⟩
          ((rev r ++ k1 ∷ []) ++ n1 ∷ []) ++ rev l
        ≡⟨ ++-assoc (rev r ++ k1 ∷ []) (n1 ∷ []) (rev l) ⟩
          (rev r ++ k1 ∷ []) ++ n1 ∷ rev l
        ≡⟨ ++-assoc (rev r) (k1 ∷ []) (n1 ∷ rev l) ⟩
          rev r ++ k1 ∷ n1 ∷ rev l
        ∎
  in  incr-long-lemma-rev n k n1 k1 p (rev r) (rev l) pp

dec-long-lemma-rev : (n k n1 k1 : ℕ) -> (n1 ≤ k1) -> (l r : List ℕ) -> (n ↑ k) ≡ (l ++ k1 ∷ n1 ∷ r) -> ⊥
dec-long-lemma-rev n (suc (suc k)) .(suc n) .n pkn [] .(suc (suc n) ↑ k) refl = abs-refl pkn
dec-long-lemma-rev n (suc k) n1 k1 pkn (x ∷ l) r p = dec-long-lemma-rev (suc n) k n1 k1 pkn l r (cut-head p)

-- TODO exact code duplication from iincr-long-lemma
dec-long-lemma : (n k n1 k1 : ℕ) -> (n1 ≤ k1) -> (l r : List ℕ) -> (n ↓ k) ≡ (l ++ n1 ∷ k1 ∷ r) -> ⊥
dec-long-lemma n k n1 k1 p l r q =
  let pp =
        begin
          (n ↑ k)
        ≡⟨ ≡-sym (rev-d n k) ⟩
          rev (n ↓ k)
        ≡⟨ cong rev q ⟩
          rev (l ++ n1 ∷ k1 ∷ r)
        ≡⟨ rev-++ l (n1 ∷ k1 ∷ r) ⟩
          ((rev r ++ k1 ∷ []) ++ n1 ∷ []) ++ rev l
        ≡⟨ ++-assoc (rev r ++ k1 ∷ []) (n1 ∷ []) (rev l) ⟩
          (rev r ++ k1 ∷ []) ++ n1 ∷ rev l
        ≡⟨ ++-assoc (rev r) (k1 ∷ []) (n1 ∷ rev l) ⟩
          rev r ++ k1 ∷ n1 ∷ rev l
        ∎
  in  dec-long-lemma-rev n k n1 k1 p (rev r) (rev l) pp

postulate
  repeat-spaced-long-lemma : (n k n1 : ℕ) -> (l r1 r2 : List ℕ) -> (n ↓ k) ≡ (l ++ n1 ∷ r1 ++ n1 ∷ r2) -> ⊥
-- repeat-spaced-long-lemma n k n1 l r1 r2 p = {!   !}
