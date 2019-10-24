{-# OPTIONS --allow-unsolved-metas --without-K #-}
module DiamondCompact where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; _×_; _,_)

open import Relation.Nullary
open import Data.Empty
open import Data.Sum hiding (swap)
open import Data.Bool hiding (_<_; _≤_; _≟_)
open import Data.Bool.Properties hiding (≤-reflexive; ≤-trans; _≟_)
open import Function

open import Arithmetic hiding (n)
open import Compact hiding (n; l)
open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to ≤∎) hiding (_≡⟨_⟩_; _≡⟨⟩_)


open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)


variable
    n : ℕ
    l : List ℕ

open ≅*-Reasoning
open Relation.Binary.PropositionalEquality.≡-Reasoning


abs-refl : {A : Set} -> n < n -> A
abs-refl p = ⊥-elim (1+n≰n p)


-- suc n ∷ n ∷ (n ↓ k , p) ++ suc (suc n) ∷ r ≡ suc n1 ∷ n1 ∷ (n1 ↓ k1 , p1) ++ suc (suc n1) ∷ r1) ->

long-lemma : (n n1 k k1 t t1 : ℕ) -> (suc n ≤ t) -> (suc n1 ≤ t1) -> (r r1 : List ℕ) -> ((2 + n) ↓ (2 + k)) ++ t ∷ r ≡ ((2 + n1) ↓ (2 + k1)) ++ t1 ∷ r1
             -> (n ≡ n1) × (((2 + n) ↓ (2 + k)) ≡ ((2 + n1) ↓ (2 + k1))) × (r ≡ r1)
long-lemma n n1 zero zero t t1 pt pt1 r r1 p rewrite (cut-t2 p) rewrite (cut-h3 p) = refl , (refl , refl)
long-lemma .0 zero zero (suc k1) t t1 pt pt1 r .r refl = refl , (refl , refl)
long-lemma zero .0 (suc k) zero t t1 pt pt1 r .r refl = refl , (refl , refl)
long-lemma zero zero (suc k) (suc k1) t t1 pt pt1 r .r refl = refl , (refl , refl)
long-lemma (suc n) (suc n1) (suc k) (suc k1) t t1 pt pt1 r r1 p =
  let recn , recl , recr = long-lemma n n1 k k1 t t1  (≤-down pt) (≤-down pt1) r r1 (cut-head p)
      recll = head+tail (cong (λ e -> 2 + e) recn) recl
  in  (cong suc recn) ,(recll , recr)
long-lemma n (suc n1) zero (suc k1) t t1 pt pt1 r r1 q =
  let e1 = cut-t2 q
      e2 = cut-t3 q
      eq = ≤-trans (s≤s pt) (≤-trans (s≤s (≤-reflexive e2)) (≤-reflexive (≡-sym e1)))
  in  abs-suc eq
long-lemma (suc n) (suc n1) (suc k) zero t t1 pt pt1 r r1 q =
  let e1 = cut-t2 q
      e2 = cut-t3 q
      eq = ≤-trans (s≤s pt1) (≤-trans (s≤s (≤-reflexive (≡-sym e2))) (≤-reflexive e1))
  in  abs-suc eq


-- and this should do something like: if ir1 = (ir p1) and ir2 = (ir p2) are non-overlapping, use force-non-crit-pair
-- otherwise, take the ir1 ∪ ir2 , force it into one of the critical pairs and then reduce critical pair
diamond : (m1 m2 m3 : List ℕ) -> (m1 ≅ m2) -> (m1 ≅ m3) -> ∃ (λ m -> (m2 ≅* m) × (m3 ≅* m))
-- -- crit-pair
-- diamond (x₁ ∷ .x₁ ∷ .x₁ ∷ m1) m2 m3 (cancel≅ [] .(x₁ ∷ m1) .(x₁ ∷ x₁ ∷ x₁ ∷ m1) .m2 refl defmf) (cancel≅ (.x₁ ∷ []) .m1 .(x₁ ∷ x₁ ∷ x₁ ∷ m1) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ = (x₁ ∷ m1) , (refl , refl) -- cc
-- diamond (x₂ ∷ .x₂ ∷ x₄ ∷ m1) m2 m3 (cancel≅ [] .(x₄ ∷ m1) .(x₂ ∷ x₂ ∷ x₄ ∷ m1) .m2 refl defmf) (swap≅ x (.x₂ ∷ []) .m1 .(x₂ ∷ x₂ ∷ x₄ ∷ m1) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ = (x₄ ∷ m1) , (refl , trans (swap x [] _) (cancel [ x₄ ] m1)) -- cs
-- diamond (c ∷ b ∷ a ∷ m1) m2 m3 (swap≅ b<c [] .(a ∷ m1) .(c ∷ b ∷ a ∷ m1) .m2 refl defmf) (swap≅ a<b (.c ∷ []) .m1 .(c ∷ b ∷ a ∷ m1) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ =
--   let a<c : suc a < c
--       a<c = ≤-down (≤-trans (s≤s a<b) (≤-down b<c))
--       left = trans (swap a<c [ b ] m1) (swap a<b [] _)
--       right = trans (swap a<c [] _) (swap b<c [ a ] _)
--    in a ∷ b ∷ c ∷ m1 , left , right -- ss
-- diamond (x₂ ∷ x₃ ∷ .x₃ ∷ m1) m2 m3 (cancel≅ (.x₂ ∷ []) .m1 .(x₂ ∷ x₃ ∷ x₃ ∷ m1) .m2 refl defmf) (swap≅ x [] .(x₃ ∷ m1) .(x₂ ∷ x₃ ∷ x₃ ∷ m1) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ = _ , (refl , trans (swap x [ x₃ ] _) (cancel [] _)) -- cs
--
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (long≅ k (x₁ ∷ []) r₁ .(_ ∷ _ ∷ r) .m3 defm₁ defmf₁) = {!   !}
-- diamond .(_ ∷ _ ∷ r) m2 m3 (swap≅ x [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (long≅ k (x₁ ∷ []) r₁ .(_ ∷ _ ∷ r) .m3 defm₁ defmf₁) = {!   !}
--
-- -- -- -- - disjoint
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (cancel≅ {n = n} (x ∷ x₁ ∷ l) r₁ .(_ ∷ _ ∷ r) .m3 d defmf₁)
--     rewrite (≡-trans defmf (cut-h2 d)) rewrite defmf₁ rewrite (≡-sym (cut-t1 d)) rewrite (≡-sym (cut-t2 d)) =
--     (l ++ r₁) ,  cancel l r₁ , (cancel [] (l ++ r₁)) --((cancel l r₁) ,  -- cc-dis
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (swap≅ x (x₁ ∷ x₂ ∷ l) r₁ .(_ ∷ _ ∷ r) .m3 d defmf₁)
--     rewrite (≡-trans defmf (cut-h2 d)) rewrite defmf₁ rewrite (≡-sym (cut-t1 d)) rewrite (≡-sym (cut-t2 d)) =
--      ((l ++ _ ∷ _ ∷ r₁)) , (swap x l r₁ , cancel [] _) -- cs-dis
-- diamond .(_ ∷ _ ∷ r) m2 m3 (swap≅ x [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (swap≅ x₁ (x₂ ∷ x₃ ∷ l) r₁ .(_ ∷ _ ∷ r) .m3 d defmf₁)
--     rewrite defmf rewrite defmf₁ rewrite (≡-sym (cut-t1 d)) rewrite (≡-sym (cut-t2 d)) rewrite (cut-h2 d) =
--      _ , (swap x₁ _ r₁ , swap x [] _) -- ss-dis
-- diamond .(_ ∷ _ ∷ r₁) m2 m3 (cancel≅ (x₁ ∷ x₂ ∷ l) r .(_ ∷ _ ∷ r₁) .m2 defm defmf) (swap≅ x [] r₁ .(_ ∷ _ ∷ r₁) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h2 defm) rewrite ≡-sym (cut-t1 defm) rewrite ≡-sym (cut-t2 defm) =
--   _ , (swap x [] _ , cancel _ r)
--
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (long≅ k (x ∷ x₁ ∷ l₁) r₁ .(_ ∷ _ ∷ r) .m3 d defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h2 d) rewrite ≡-sym (cut-t1 d) rewrite ≡-sym (cut-t2 d) =
--   _ , ((long k l₁ r₁) , (cancel [] _))
-- diamond .(_ ∷ _ ∷ r) m2 m3 (swap≅ x [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (long≅ k (x₁ ∷ x₂ ∷ l₁) r₁ .(_ ∷ _ ∷ r) .m3 d defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h2 d) rewrite ≡-sym (cut-t1 d) rewrite ≡-sym (cut-t2 d) =
--   _ , ((long k (_ ∷ _ ∷ l₁) r₁) , (swap x [] _))
--
-- -- --- identity
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (cancel≅ [] r₁ .(_ ∷ _ ∷ r) .m3 defm₁ defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h2 defm₁)  = r₁ , (refl , refl)
-- diamond .(_ ∷ _ ∷ r) m2 m3 (swap≅ x [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (swap≅ x₁ [] r₁ .(_ ∷ _ ∷ r) .m3 defm₁ defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h2 defm₁) rewrite (cut-t1 defm₁) rewrite (cut-t2 defm₁)  = _ , (refl , refl)
--
-- -- --- rec
-- diamond m1 m2 m3 (swap≅ x l r .m1 .m2 defm defmf) (cancel≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (long≅ k l r .m1 .m2 defm defmf) (cancel≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
-- diamond m1 m2 m3 (long≅ k l r .m1 .m2 defm defmf) (swap≅ x l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
--
-- diamond m1 m2 m3 (cancel≅ (x ∷ l) r .m1 .m2 defm defmf) (cancel≅ [] r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (swap≅ x (x₂ ∷ l) r .m1 .m2 defm defmf) (swap≅ x₁ [] r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (long≅ k (x ∷ l) r .m1 .m2 defm defmf) (long≅ k₁ [] r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
--
-- diamond m1 m2 m3 (cancel≅ (x ∷ l) r .m1 .m2 defm defmf) (cancel≅ (x₁ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (cancel≅ (x₁ ∷ l) r .m1 .m2 defm defmf) (swap≅ x (x₂ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (swap≅ x (x₂ ∷ l) r .m1 .m2 defm defmf) (swap≅ x₁ (x₃ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!!}
--
-- diamond m1 m2 m3 (cancel≅ (x ∷ l) r .m1 .m2 defm defmf) (long≅ k (x₁ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
-- diamond m1 m2 m3 (swap≅ x (x₁ ∷ l) r .m1 .m2 defm defmf) (long≅ k (x₂ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
-- diamond m1 m2 m3 (long≅ k (x ∷ l) r .m1 .m2 defm defmf) (long≅ k₁ (x₁ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
--
-- -- - abs
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (swap≅ x [] .r .(_ ∷ _ ∷ r) .m3 refl defmf₁) = abs-suc x
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (long≅ k [] r₁ .(_ ∷ _ ∷ r) .m3 () defmf₁)
-- diamond .(_ ∷ _ ∷ r) m2 m3 (swap≅ x [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (long≅ k [] r₁ .(_ ∷ _ ∷ r) .m3 defm₁ defmf₁) =
--   let nn = (cut-t1 defm₁)
--       kk = (cut-t2 defm₁)
--   in  abs-refl (≤-trans x (≤-trans (≤-reflexive nn) (≤-reflexive (≡-sym (cong suc kk)))))

-- TODO
diamond m1 m2 m3 (long≅ {n} k1 [] r m mf defm defmf) (long≅ {n₁} k2 [] r₁ m₁ mf₁ defm₁ defmf₁)
  rewrite defmf rewrite defmf₁ =
  let eq = ≡-trans (≡-sym defm) defm₁
      eqn , eql , eqr = long-lemma n n₁ k1 k2 (suc n) (suc n₁) (≤-reflexive refl) (≤-reflexive refl) r r₁ eq
  in  _ , (refl , refl≡ (head+tail (≡-sym eqn) (start+end (≡-sym eql) (≡-sym eqr))))

diamond .(1 ∷ 0 ∷ 1 ∷ 1 ∷ r) m2 m3 (cancel≅ (.1 ∷ .0 ∷ []) r .(1 ∷ 0 ∷ 1 ∷ 1 ∷ r) .m2 refl defmf) (long≅ {zero} zero [] .(1 ∷ r) .(1 ∷ 0 ∷ 1 ∷ 1 ∷ r) .m3 refl defmf₁)
  rewrite defmf rewrite defmf₁ =
  _ , (refl , trans (braid [ 0 ] _ ) (cancel [] _))
diamond .(1 ∷ 0 ∷ 1 ∷ l ++ _ ∷ _ ∷ r) m2 m3 (cancel≅ (.1 ∷ .0 ∷ .1 ∷ l) r .(1 ∷ 0 ∷ 1 ∷ l ++ _ ∷ _ ∷ r) .m2 refl defmf) (long≅ {zero} zero [] .(l ++ _ ∷ _ ∷ r) .(1 ∷ 0 ∷ 1 ∷ l ++ _ ∷ _ ∷ r) .m3 refl defmf₁)   rewrite defmf rewrite defmf₁ =
  _ , (braid [] _ , cancel _ r)
diamond .(x ∷ _ ∷ _ ∷ r) m2 m3 (cancel≅ (x ∷ []) r .(x ∷ _ ∷ _ ∷ r) .m2 refl defmf) (long≅ {zero} (suc k) [] r₁ .(x ∷ _ ∷ _ ∷ r) .m3 () defmf₁)
diamond .(1 ∷ 0 ∷ 1 ∷ 1 ∷ r) m2 m3 (cancel≅ (.1 ∷ .0 ∷ []) r .(1 ∷ 0 ∷ 1 ∷ 1 ∷ r) .m2 refl defmf) (long≅ {zero} (suc k) [] .(1 ∷ r) .(1 ∷ 0 ∷ 1 ∷ 1 ∷ r) .m3 refl defmf₁)
  rewrite defmf rewrite defmf₁ =
  _ , (refl , trans (braid [ 0 ] _ ) (cancel [] _))
diamond .(1 ∷ 0 ∷ 1 ∷ l ++ _ ∷ _ ∷ r) m2 m3 (cancel≅ (.1 ∷ .0 ∷ .1 ∷ l) r .(1 ∷ 0 ∷ 1 ∷ l ++ _ ∷ _ ∷ r) .m2 refl defmf) (long≅ {zero} (suc k) [] .(l ++ _ ∷ _ ∷ r) .(1 ∷ 0 ∷ 1 ∷ l ++ _ ∷ _ ∷ r) .m3 refl defmf₁)
  rewrite defmf rewrite defmf₁ =
  _ , (braid [] _ , cancel _ r)
diamond .(suc (suc n) ∷ suc n ∷ suc (suc n) ∷ suc (suc n) ∷ r) m2 m3 (cancel≅ (.(suc (suc n)) ∷ .(suc n) ∷ []) r .(suc (suc n) ∷ suc n ∷ suc (suc n) ∷ suc (suc n) ∷ r) .m2 refl defmf) (long≅ {suc n} zero [] .(suc (suc n) ∷ r) .(suc (suc n) ∷ suc n ∷ suc (suc n) ∷ suc (suc n) ∷ r) .m3 refl defmf₁)
  rewrite defmf rewrite defmf₁ =
  _ , refl , trans (braid [ _ ] _) (cancel [] _)
diamond .(suc (suc n) ∷ suc n ∷ suc (suc n) ∷ l ++ _ ∷ _ ∷ r) m2 m3 (cancel≅ (.(suc (suc n)) ∷ .(suc n) ∷ .(suc (suc n)) ∷ l) r .(suc (suc n) ∷ suc n ∷ suc (suc n) ∷ l ++ _ ∷ _ ∷ r) .m2 refl defmf) (long≅ {suc n} zero [] .(l ++ _ ∷ _ ∷ r) .(suc (suc n) ∷ suc n ∷ suc (suc n) ∷ l ++ _ ∷ _ ∷ r) .m3 refl defmf₁)
  rewrite defmf rewrite defmf₁ =
  _ , braid [] _ , cancel _ r
diamond (x₁ ∷ .(l ++ n₁ ∷ n₁ ∷ r)) m2 m3 (cancel≅ {n₁} (.x₁ ∷ l) r .(x₁ ∷ l ++ n₁ ∷ n₁ ∷ r) .m2 refl defmf) (long≅ {suc n} (suc k) [] r₁ .(x₁ ∷ l ++ n₁ ∷ n₁ ∷ r) .m3 defm₁ defmf₁)
  rewrite defmf rewrite defmf₁ rewrite (cut-tail defm₁) =
  let left-c = cancel-c {n₁} l r
      right-c = long-c {n} k [] r₁
      right-cc = {!subst (λ e -> e ≅ (n ∷ suc n ∷ n ∷ (n ↓ k) ++ r₁)) right-c (≡-sym (cut-head defm₁))!}
      rec = diamond (l ++ n₁ ∷ n₁ ∷ r) (l ++ r) {!!} left-c right-cc
  in  {!!} , {!!} , {!!}
-- diamond m1 m2 m3 (swap≅ x (x₁ ∷ l) r .m1 .m2 defm defmf) (long≅ k [] r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
-- diamond m1 m2 m3 (long≅ k [] r .m1 .m2 defm defmf) (long≅ k₁ (x ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!   !}


-- diamond-full : {m1 m2 m3 : List ℕ} -> (m1 ≅* m2) -> (m1 ≅* m3) -> ∃ (λ m -> (m2 ≅* m) × (m3 ≅* m))
-- diamond-full p q = {!!}
--
--
-- data _≃_ : List ℕ -> List ℕ -> Set where
--   R : {m1 m2 mf : List ℕ} -> (p1 : m1 ≅* mf) -> (p2 : m2 ≅* mf) -> m1 ≃ m2
--
-- refl≃ : (m : List ℕ) -> (m ≃ m)
-- refl≃ m = R refl refl
--
-- comm≃ : (m1 m2 : List ℕ) -> (m1 ≃ m2) -> (m2 ≃ m1)
-- comm≃ m1 m2 (R p1 p2) = R p2 p1
--
-- trans≃ : (m1 m2 m3 : List ℕ) -> (r1 : m1 ≃ m2) -> (r2 : m2 ≃ m3) -> (m1 ≃ m3)
-- trans≃ m1 m2 m3 (R p1 p2) (R p3 p4) =
--   let lemma-m , lemma1 , lemma2 = diamond-full p2 p3
--   in  R (trans p1 lemma1) (trans p4 lemma2)
