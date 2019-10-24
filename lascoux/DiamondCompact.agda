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

long-lemma : {n n1 k k1 t t1 : ℕ} -> {p : k ≤ n} -> {p1 : k1 ≤ n1} -> {r r1 : List ℕ} -> suc n ∷ n ∷ (n ↓ k , p) ++ (t + n) ∷ r ≡ suc n1 ∷ n1 ∷ (n1 ↓ k1 , p1) ++ (t1 + n1) ∷ r1 -> (n ≡ n1) × (k ≡ k1) × (r ≡ r1) × (t ≡ t1)
long-lemma {n} {n1} {.0} {.0} {t} {t1} {z≤n} {z≤n} {r} {r1} q = (cut-t2 q) , refl , (cut-h3 q) , ≡-down-r-+ (subst (λ e -> t + e ≡ t1 + n1) (cut-t2 q) (cut-t3 q))
long-lemma {suc n} {suc n1} {suc k} {suc k1} {t} {t1} {s≤s p} {s≤s p1} {r} {r1} q rewrite (cut-t3 q) =
  let qq =
        begin
          suc (suc n) ∷ suc n ∷ n ∷ (n ↓ k , p) ++ (t + 1) + n ∷ r
        ≡⟨ cong (λ e -> suc (suc n) ∷ suc n ∷ n ∷ (n ↓ k , p) ++ e ∷ r) (+-assoc t 1 n) ⟩ --
          _
        ≡⟨ q ⟩
          suc (suc n1) ∷ suc n1 ∷ n1 ∷ (n1 ↓ k1 , p1) ++ t1 + suc n1 ∷ r1
        ≡⟨ cong (λ e -> suc (suc n1) ∷ suc n1 ∷ n1 ∷ (n1 ↓ k1 , p1) ++ e ∷ r1) (≡-sym (+-assoc t1 1 n1)) ⟩
          suc (suc n1) ∷ suc n1 ∷ n1 ∷ (n1 ↓ k1 , p1) ++ (t1 + 1) + n1 ∷ r1
        ∎
      en , ek , er , et = long-lemma {p = p} {p1 = p1} {r = r} {r1 = r1} (cut-head qq)
  in  refl , (cong suc ek) , er , ≡-down-r-+ et
long-lemma {n} {suc n1} {zero} {suc k1} {suc t} {t1} {z≤n} {s≤s p1} {r} {r1} q =
  let e1 = cut-t2 q
      e2 = cut-t3 q
      aa = ≤-trans {!   !} (≤-trans (≤-reflexive (cong suc e2)) (≤-reflexive (≡-sym e1)))
  in  {!  !}
long-lemma {suc n} {n1} {suc k} {zero} {t} {suc t1} {s≤s p} {z≤n} {r} {r1} q = {!   !}

-- and this should do something like: if ir1 = (ir p1) and ir2 = (ir p2) are non-overlapping, use force-non-crit-pair
-- otherwise, take the ir1 ∪ ir2 , force it into one of the critical pairs and then reduce critical pair
diamond : (m1 m2 m3 : List ℕ) -> (m1 ≅ m2) -> (m1 ≅ m3) -> ∃ (λ m -> (m2 ≅* m) × (m3 ≅* m))
-- crit-pair
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
-- diamond .(1 ∷ 1 ∷ 0 ∷ 1 ∷ r₁) m2 m3 (cancel≅ [] .(0 ∷ 1 ∷ r₁) .(1 ∷ 1 ∷ 0 ∷ 1 ∷ r₁) .m2 refl defmf) (long≅ {zero} zero z≤n (.1 ∷ []) r₁ .(1 ∷ 1 ∷ 0 ∷ 1 ∷ r₁) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ =
--   0 ∷ 1 ∷ r₁ , refl , trans (braid [] (0 ∷ r₁)) (cancel (0 ∷ 1 ∷ []) r₁)
-- diamond .(suc (suc n) ∷ suc (suc n) ∷ suc n ∷ suc (suc n) ∷ r₁) m2 m3 (cancel≅ [] .(suc n ∷ suc (suc n) ∷ r₁) .(suc (suc n) ∷ suc (suc n) ∷ suc n ∷ suc (suc n) ∷ r₁) .m2 refl defmf) (long≅ {suc n} zero z≤n (.(suc (suc n)) ∷ []) r₁ .(suc (suc n) ∷ suc (suc n) ∷ suc n ∷ suc (suc n) ∷ r₁) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ =
--   (1 + n) ∷ (2 + n) ∷ r₁ , refl , trans (braid [] ((1 + n) ∷ r₁)) (cancel ((1 + n) ∷ (2 + n) ∷ []) r₁)
-- diamond .(suc (suc n) ∷ suc (suc n) ∷ suc n ∷ n ∷ (n ↓ k , p) ++ suc (suc n) ∷ r₁) m2 m3 (cancel≅ [] .(suc n ∷ n ∷ (n ↓ k , p) ++ suc (suc n) ∷ r₁) .(suc (suc n) ∷ suc (suc n) ∷ suc n ∷ n ∷ (n ↓ k , p) ++ suc (suc n) ∷ r₁) .m2 refl defmf) (long≅ {suc n} (suc k) (s≤s p) (.(suc (suc n)) ∷ []) r₁ .(suc (suc n) ∷ suc (suc n) ∷ suc n ∷ n ∷ (n ↓ k , p) ++ suc (suc n) ∷ r₁) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ =
--   _ , (refl , (trans (braid [] _) (trans (cancel ((1 + n) ∷ 2 + n ∷ []) _) (long-swap-lr [ suc n ] r₁ (s≤s (≤-reflexive refl)) (s≤s p)))))
-- diamond .(x₁ ∷ suc _ ∷ _ ∷ (_ ↓ k , p) ++ suc _ ∷ r₁) m2 m3 (swap≅ x [] .(_ ∷ (_ ↓ k , p) ++ suc _ ∷ r₁) .(x₁ ∷ suc _ ∷ _ ∷ (_ ↓ k , p) ++ suc _ ∷ r₁) .m2 refl defmf) (long≅ {n} k p (x₁ ∷ []) r₁ .(x₁ ∷ suc _ ∷ _ ∷ (_ ↓ k , p) ++ suc _ ∷ r₁) .m3 refl defmf₁)
--   rewrite defmf rewrite defmf₁ =
--   let left = trans (long-swap-lr {n1 = suc n} [ suc n ] (suc n ∷ r₁) (≤-down x) {k = suc k} (s≤s p)) (trans (swap x (suc n ∷ n ∷ (n ↓ k , p)) r₁) (long k p [] (x₁ ∷ r₁)))
--       right = trans (swap (≤-down x) [] _) (long-swap-lr [ n ] r₁ x (s≤s (s≤s p)))
--   in  _ , (left , right)
--
-- -- -- - disjoint
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
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (long≅ k p (x ∷ x₁ ∷ l₁) r₁ .(_ ∷ _ ∷ r) .m3 d defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h2 d) rewrite ≡-sym (cut-t1 d) rewrite ≡-sym (cut-t2 d) =
--   _ , ((long k p l₁ r₁) , (cancel [] _))
-- diamond .(_ ∷ _ ∷ r) m2 m3 (swap≅ x [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (long≅ k p (x₁ ∷ x₂ ∷ l₁) r₁ .(_ ∷ _ ∷ r) .m3 d defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h2 d) rewrite ≡-sym (cut-t1 d) rewrite ≡-sym (cut-t2 d) =
--   _ , ((long k p (_ ∷ _ ∷ l₁) r₁) , (swap x [] _))
--
-- -- --- identity
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (cancel≅ [] r₁ .(_ ∷ _ ∷ r) .m3 defm₁ defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h2 defm₁)  = r₁ , (refl , refl)
-- diamond .(_ ∷ _ ∷ r) m2 m3 (swap≅ x [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (swap≅ x₁ [] r₁ .(_ ∷ _ ∷ r) .m3 defm₁ defmf₁)
--   rewrite defmf rewrite defmf₁ rewrite (cut-h2 defm₁) rewrite (cut-t1 defm₁) rewrite (cut-t2 defm₁)  = _ , (refl , refl)
--
-- -- --- rec
-- diamond m1 m2 m3 (swap≅ x l r .m1 .m2 defm defmf) (cancel≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (long≅ k p l r .m1 .m2 defm defmf) (cancel≅ l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
-- diamond m1 m2 m3 (long≅ k p l r .m1 .m2 defm defmf) (swap≅ x l₁ r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
--
-- diamond m1 m2 m3 (cancel≅ (x ∷ l) r .m1 .m2 defm defmf) (cancel≅ [] r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (swap≅ x (x₂ ∷ l) r .m1 .m2 defm defmf) (swap≅ x₁ [] r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (long≅ k p (x ∷ l) r .m1 .m2 defm defmf) (long≅ k₁ p₁ [] r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
--
-- diamond m1 m2 m3 (cancel≅ (x ∷ l) r .m1 .m2 defm defmf) (cancel≅ (x₁ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (cancel≅ (x₁ ∷ l) r .m1 .m2 defm defmf) (swap≅ x (x₂ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!!}
-- diamond m1 m2 m3 (swap≅ x (x₂ ∷ l) r .m1 .m2 defm defmf) (swap≅ x₁ (x₃ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!!}
--
-- diamond m1 m2 m3 (cancel≅ (x ∷ l) r .m1 .m2 defm defmf) (long≅ k p (x₁ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
-- diamond m1 m2 m3 (swap≅ x (x₁ ∷ l) r .m1 .m2 defm defmf) (long≅ k p (x₂ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
-- diamond m1 m2 m3 (long≅ k p (x ∷ l) r .m1 .m2 defm defmf) (long≅ k₁ p₁ (x₁ ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
--
-- -- - abs
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (swap≅ x [] .r .(_ ∷ _ ∷ r) .m3 refl defmf₁) = abs-suc x
-- diamond .(_ ∷ _ ∷ r) m2 m3 (cancel≅ [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (long≅ k p [] r₁ .(_ ∷ _ ∷ r) .m3 () defmf₁)
-- diamond .(_ ∷ _ ∷ r) m2 m3 (swap≅ x [] r .(_ ∷ _ ∷ r) .m2 refl defmf) (long≅ k p [] r₁ .(_ ∷ _ ∷ r) .m3 defm₁ defmf₁) =
--   let nn = (cut-t1 defm₁)
--       kk = (cut-t2 defm₁)
--   in  abs-refl (≤-trans x (≤-trans (≤-reflexive nn) (≤-reflexive (≡-sym (cong suc kk)))))

-- TODO
diamond m1 m2 m3 (long≅ {n} k1 p [] r m mf defm defmf) (long≅ k2 p₁ [] r₁ m₁ mf₁ defm₁ defmf₁)
  rewrite defmf rewrite defmf₁ =
  let eq = ≡-trans (≡-sym defm) defm₁
  in  {!   !} , (refl , {! refl  !})

-- diamond m1 m2 m3 (cancel≅ (x ∷ l) r .m1 .m2 defm defmf) (long≅ k p [] r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
-- diamond m1 m2 m3 (swap≅ x (x₁ ∷ l) r .m1 .m2 defm defmf) (long≅ k p [] r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
-- diamond m1 m2 m3 (long≅ k p [] r .m1 .m2 defm defmf) (long≅ k₁ p₁ (x ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!   !}


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
