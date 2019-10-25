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
open import Data.Bool hiding (_<_; _≤_; _≟_; _<?_)
open import Data.Bool.Properties hiding (≤-reflexive; ≤-trans; _≟_; _<?_)
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


-- long-lemma : (n n1 k k1 t t1 : ℕ) -> (suc n ≤ t) -> (suc n1 ≤ t1) -> (r r1 : List ℕ) -> ((2 + n) ↓ (2 + k)) ++ t ∷ r ≡ ((2 + n1) ↓ (2 + k1)) ++ t1 ∷ r1
--              -> (n ≡ n1) × (((2 + n) ↓ (2 + k)) ≡ ((2 + n1) ↓ (2 + k1))) × (r ≡ r1)
-- long-lemma n n1 zero zero t t1 pt pt1 r r1 p rewrite (cut-t2 p) rewrite (cut-h3 p) = refl , (refl , refl)
-- long-lemma .0 zero zero (suc k1) t t1 pt pt1 r .r refl = refl , (refl , refl)
-- long-lemma zero .0 (suc k) zero t t1 pt pt1 r .r refl = refl , (refl , refl)
-- long-lemma zero zero (suc k) (suc k1) t t1 pt pt1 r .r refl = refl , (refl , refl)
-- long-lemma (suc n) (suc n1) (suc k) (suc k1) t t1 pt pt1 r r1 p =
--   let recn , recl , recr = long-lemma n n1 k k1 t t1  (≤-down pt) (≤-down pt1) r r1 (cut-head p)
--       recll = head+tail (cong (λ e -> 2 + e) recn) recl
--   in  (cong suc recn) ,(recll , recr)
-- long-lemma n (suc n1) zero (suc k1) t t1 pt pt1 r r1 q =
--   let e1 = cut-t2 q
--       e2 = cut-t3 q
--       eq = ≤-trans (s≤s pt) (≤-trans (s≤s (≤-reflexive e2)) (≤-reflexive (≡-sym e1)))
--   in  abs-suc eq
-- long-lemma (suc n) (suc n1) (suc k) zero t t1 pt pt1 r r1 q =
--   let e1 = cut-t2 q
--       e2 = cut-t3 q
--       eq = ≤-trans (s≤s pt1) (≤-trans (s≤s (≤-reflexive (≡-sym e2))) (≤-reflexive e1))
--   in  abs-suc eq

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
rev-d k p = {!!}

rev-u : (k p : ℕ) -> rev (k ↑ p) ≡ k ↓ p
rev-u k p = {!!}

rev-++ : (l r : List ℕ) -> rev (l ++ r) ≡ (rev r) ++ (rev l)
rev-++ [] r = ≡-sym ++-unit
rev-++ (x ∷ l) r =
  let rec = start+end (rev-++ l r) refl
  in  ≡-trans rec (++-assoc (rev r) (rev l) (x ∷ []))

rev-rev : l ≡ rev (rev l)
rev-rev {l} = {!!}

-- repeat-long-lemma : (n k n1 : ℕ) -> (l r : List ℕ) -> (n ↓ k) ≡ (l ++ n1 ∷ n1 ∷ r) -> ⊥
-- repeat-long-lemma n zero n1 [] r ()
-- repeat-long-lemma n zero n1 (x ∷ l) r ()
-- repeat-long-lemma n (suc (suc k)) n1 [] r p =
--   abs-refl (≤-trans (≤-reflexive (cut-t1 p)) (≤-reflexive (≡-sym (cut-t2 p))))
-- repeat-long-lemma n (suc k) n1 (x ∷ l) r p = repeat-long-lemma n k n1 l r (cut-head p)
--
-- repeat-long-lemma-rev : (n k n1 : ℕ) -> (l r : List ℕ) -> (n ↑ k) ≡ (l ++ n1 ∷ n1 ∷ r) -> ⊥
-- repeat-long-lemma-rev n zero n1 [] r ()
-- repeat-long-lemma-rev n zero n1 (x ∷ l) r ()
-- repeat-long-lemma-rev n (suc zero) n1 [] r ()
-- repeat-long-lemma-rev n (suc (suc k)) n1 [] r ()
-- repeat-long-lemma-rev n (suc k) n1 (x ∷ l) r p = repeat-long-lemma-rev (suc n) k n1 l r (cut-head p)
--
-- cancel-long-lemma-rev : (n k n1 : ℕ) -> (r l1 r1 : List ℕ) -> ((r ++ (1 + k + n) ∷ (n ↑ (2 + k))) ≡ (r1 ++ n1 ∷ n1 ∷ l1)) -> ∃ (λ mf -> ((((k + n) ∷ (n ↓ (2 + k)) ++ (rev r)) ≅* mf) × (((rev l1) ++ (rev r1))) ≅* mf))
-- cancel-long-lemma-rev n k n1 [] l1 [] p =
--   let fst = cut-t1 p
--       snd = cut-t2 p
--   in  abs-refl (≤-trans (≤-reflexive fst) (≤-trans (≤-reflexive (≡-sym snd)) (≤-up-+ (≤-reflexive refl))))
-- cancel-long-lemma-rev n zero n1 [] l1 (x ∷ x₁ ∷ []) ()
-- cancel-long-lemma-rev n (suc k) n1 [] l1 (x ∷ x₁ ∷ []) ()
-- cancel-long-lemma-rev n k n1 [] l1 (x ∷ x₁ ∷ x₂ ∷ r1) p =
--   let cut = cut-h3 p
--   in  ⊥-elim (repeat-long-lemma-rev (suc (suc n)) k n1 r1 l1 (cut-h3 p))
-- cancel-long-lemma-rev n k .(suc (k + n)) (.(suc (k + n)) ∷ []) .(n ∷ suc n ∷ (suc (suc n) ↑ k)) [] refl =
--   let left =
--         ≅*begin
--           k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k) ++ suc (k + n) ∷ []
--         ≅*⟨ long k [ k + n ] [] ⟩
--           k + n ∷ k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k) ++ []
--         ≅*⟨ cancel [] _ ⟩
--           suc (k + n) ∷ k + n ∷ (n ↓ k) ++ []
--         ≅*⟨ refl≡ (++-unit) ⟩
--           (n ↓ (2 + k))
--         ≅*∎
--       right =
--         begin
--           ((rev (suc (suc n) ↑ k) ++ suc n ∷ []) ++ n ∷ []) ++ []
--         ≡⟨ ++-unit ⟩
--           (rev (suc (suc n) ↑ k) ++ suc n ∷ []) ++ n ∷ []
--         ≡⟨ start+end (start+end (rev-u (2 + n) k) refl) refl ⟩
--           ((suc (suc n) ↓ k) ++ suc n ∷ []) ++ n ∷ []
--         ≡⟨ start+end (++-↓ (1 + n) k) refl ⟩
--           k + suc n ∷ (suc n ↓ k) ++ n ∷ []
--         ≡⟨ ++-↓ n (1 + k) ⟩
--           suc (k + n) ∷ k + n ∷ (n ↓ k)
--         ∎
--   in  _ , ( left , refl≡ right)
--
-- cancel-long-lemma-rev n k n1 (.n1 ∷ .n1 ∷ r) .(r ++ suc (k + n) ∷ n ∷ suc n ∷ (suc (suc n) ↑ k)) [] refl =
--   let left =
--         ≅*begin
--           (rev r ++ n1 ∷ []) ++ n1 ∷ []
--         ≅*⟨ refl≡ (++-assoc (rev r) [ n1 ] (n1 ∷ [])) ⟩
--           rev r ++ n1 ∷ n1 ∷ []
--         ≅*⟨ (cancel (rev r) []) ⟩
--           rev r ++ []
--         ≅*⟨ (refl≡ ++-unit) ⟩
--           rev r
--         ≅*∎
--       right =
--         begin
--           rev (r ++ suc (k + n) ∷ n ∷ suc n ∷ (suc (suc n) ↑ k)) ++ []
--         ≡⟨ ++-unit ⟩
--           rev (r ++ suc (k + n) ∷ n ∷ suc n ∷ (suc (suc n) ↑ k))
--         ≡⟨ rev-++ r (suc (k + n) ∷ n ∷ suc n ∷ (suc (suc n) ↑ k)) ⟩
--           (((rev (suc (suc n) ↑ k) ++ suc n ∷ []) ++ n ∷ []) ++ suc (k + n) ∷ []) ++ rev r
--         ≡⟨ start+end (start+end (start+end (start+end (rev-u (2 + n) k) refl) refl) refl) refl ⟩
--           ((((suc (suc n) ↓ k) ++ suc n ∷ []) ++ n ∷ []) ++ suc (k + n) ∷ []) ++ rev r
--         ≡⟨ start+end (start+end (start+end (++-↓ (1 + n) k) refl) refl) refl ⟩
--           k + suc n ∷ (((suc n ↓ k) ++ n ∷ []) ++ suc (k + n) ∷ []) ++ rev r
--         ≡⟨ start+end (start+end (++-↓ n (1 + k)) refl) refl ⟩
--           suc (k + n) ∷ k + n ∷ ((n ↓ k) ++ suc (k + n) ∷ []) ++ rev r
--         ∎
--       right* =
--         ≅*begin
--           rev (r ++ suc (k + n) ∷ n ∷ suc n ∷ (suc (suc n) ↑ k)) ++ []
--         ≅*⟨ refl≡ right ⟩
--           suc (k + n) ∷ k + n ∷ ((n ↓ k) ++ suc (k + n) ∷ []) ++ rev r
--         ≅*⟨ ++r (rev r) (long k [] []) ⟩
--           k + n ∷ suc (k + n) ∷ k + n ∷ ((n ↓ k) ++ []) ++ rev r
--         ≅*⟨ ++r (rev r) (l++ (k + n ∷ suc (k + n) ∷ k + n ∷ []) (refl≡ ++-unit)) ⟩
--           k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k) ++ rev r
--         ≅*∎
--   in  _ , ( l++ (k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k)) left , right* )
-- cancel-long-lemma-rev n k n1 (x ∷ r) l1 (x₁ ∷ r1) p rewrite (≡-sym (cut-tail p)) =
--   let rec-m , rec-l , rec-r = cancel-long-lemma-rev n k n1 r l1 r1 (cut-head p)
--       ll = trans (refl≡ (≡-sym (++-assoc (k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k)) (rev r) [ x ]))) (++r [ x ] rec-l)
--       rr = trans (refl≡ (≡-sym (++-assoc (rev l1) (rev r1) [ x ]))) (++r [ x ] rec-r)
--   in  _ , (ll , rr)
--
-- cancel-long-lemma : (n k n1 : ℕ) -> (r l1 r1 : List ℕ) -> (((n ↑ (2 + k)) ++ (1 + k + n) ∷ r) ≡ (l1 ++ n1 ∷ n1 ∷ r1)) -> ∃ (λ mf -> ((((k + n) ∷ (n ↓ (2 + k)) ++ (rev r)) ≅* mf) × (((rev l1) ++ (rev r1))) ≅* mf))
-- cancel-long-lemma n k n1 r l1 r1 p =
--   let pp =
--         begin
--           r ++ suc (k + n) ∷ n ∷ suc n ∷ (suc (suc n) ↑ k)
--         ≡⟨ {!!} ⟩
--           (rev ((suc (suc n) ↑ k) ++ suc (k + n) ∷ r) ++ suc n ∷ []) ++ n ∷ []
--         ≡⟨ cong rev p ⟩
--           rev (l1 ++ n1 ∷ n1 ∷ r1)
--         ≡⟨ {!!} ⟩
--           r1 ++ n1 ∷ n1 ∷ l1
--         ∎
--   in  cancel-long-lemma-rev n k n1 r l1 r1 pp

-- incr-long-lemma : (n k n1 k1 : ℕ) -> (l r : List ℕ) -> (n ↓ k) ≡ (l ++ n1 ∷ n1 ∷ r) -> ⊥
-- incr-long-lemma

incr-long-lemma-rev : (n k n1 k1 : ℕ) -> (suc k1 < n1) -> (l r : List ℕ) -> (n ↑ k) ≡ (l ++ k1 ∷ n1 ∷ r) -> ⊥
incr-long-lemma-rev n k n1 k1 pkn l r p = {!   !}

swap-long-lemma-rev : (n k n1 k1 : ℕ) -> (pkn : suc k1 < n1)-> (r l1 r1 : List ℕ) -> ((r ++ (1 + k + n) ∷ (n ↑ (2 + k))) ≡ (r1 ++ k1 ∷ n1 ∷ l1)) -> ∃ (λ mf -> ((((k + n) ∷ (n ↓ (2 + k)) ++ (rev r)) ≅* mf) × (((rev l1) ++ (k1 ∷ n1 ∷ rev r1))) ≅* mf))
swap-long-lemma-rev n k n1 k1 pkn [] l1 [] p =
  let fst = cut-t1 p
      snd = cut-t2 p
  in  abs-refl (≤-trans (≤-trans (≤-trans (s≤s (≤-up (≤-up (≤-up-+ (≤-reflexive refl))))) (≤-reflexive (cong (λ e -> 2 + e ) fst))) pkn) (≤-reflexive (≡-sym snd)))
swap-long-lemma-rev n k .(suc n) .n pkn [] .(suc (suc n) ↑ k) (.(suc (k + n)) ∷ []) refl = abs-refl pkn
swap-long-lemma-rev n (suc k) .(suc (suc n)) .(suc n) pkn [] .(suc (suc (suc n)) ↑ k) (.(suc (suc (k + n))) ∷ .n ∷ []) refl = abs-refl pkn
swap-long-lemma-rev n k n1 k1 pkn [] l1 (x ∷ x₁ ∷ x₂ ∷ r1) p = ⊥-elim (incr-long-lemma-rev (suc (suc n)) k n1 k1 pkn r1 l1 (cut-h3 p))
swap-long-lemma-rev n k .(suc (k + n)) k1 pkn (.k1 ∷ []) .(n ∷ suc n ∷ (suc (suc n) ↑ k)) [] refl with suc k1 <? n
... | yes p =
  let left =
        ≅*begin
          k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k) ++ k1 ∷ []
        ≅*⟨ long-swap<-lr k1 n (2 + k) [ k + n ] [] p ⟩
          k + n ∷ k1 ∷ suc (k + n) ∷ k + n ∷ (n ↓ k) ++ []
        ≅*⟨ refl≡ (++-unit) ⟩
          k + n ∷ k1 ∷ suc (k + n) ∷ k + n ∷ (n ↓ k)
        ≅*⟨ swap (≤-trans p (≤-up-+ (≤-reflexive refl))) [] _ ⟩
          k1 ∷ k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k)
        ≅*∎
      right =
        begin
          ((rev (suc (suc n) ↑ k) ++ suc n ∷ []) ++ n ∷ []) ++ k1 ∷ suc (k + n) ∷ []
        ≡⟨ start+end (start+end (start+end (rev-u (2 + n) k) refl) refl) refl ⟩
          (((suc (suc n) ↓ k) ++ suc n ∷ []) ++ n ∷ []) ++ k1 ∷ suc (k + n) ∷ []
        ≡⟨ start+end (start+end (++-↓ (1 + n) k) refl) refl ⟩
          (((suc n) ↓ (1 + k)) ++ n ∷ []) ++ k1 ∷ suc (k + n) ∷ []
        ≡⟨ start+end (++-↓ n (1 + k)) refl ⟩
          (n ↓ (2 + k)) ++ k1 ∷ suc (k + n) ∷ []
        ∎
      right* =
        ≅*begin
          ((rev (suc (suc n) ↑ k) ++ suc n ∷ []) ++ n ∷ []) ++ k1 ∷ suc (k + n) ∷ []
        ≅*⟨ refl≡ right ⟩
          suc (k + n) ∷ k + n ∷ (n ↓ k) ++ k1 ∷ suc (k + n) ∷ []
        ≅*⟨ long-swap<-lr k1 n (suc (suc k)) [] (suc (k + n) ∷ []) p ⟩
          k1 ∷ suc (k + n) ∷ k + n ∷ (n ↓ k) ++ suc (k + n) ∷ []
        ≅*⟨ long k [ k1 ] [] ⟩
          k1 ∷ k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k) ++ []
        ≅*⟨ refl≡ (++-unit) ⟩
          k1 ∷ k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k)
        ≅*∎
  in  _ , ( left , right*)
... | no q = {!!}
swap-long-lemma-rev n k n1 k1 pkn (.k1 ∷ .n1 ∷ r) .(r ++ suc (k + n) ∷ n ∷ suc n ∷ (suc (suc n) ↑ k)) [] refl =
  let left =
        ≅*begin
          (rev r ++ n1 ∷ []) ++ k1 ∷ []
        ≅*⟨ refl≡ (++-assoc (rev r) [ n1 ] [ k1 ]) ⟩
          rev r ++ n1 ∷ [] ++ k1 ∷ []
        ≅*⟨ swap pkn (rev r) [] ⟩
          rev r ++ k1 ∷ [] ++ n1 ∷ []
        ≅*∎
      right =
        ≅*begin
          rev (r ++ suc (k + n) ∷ n ∷ suc n ∷ (suc (suc n) ↑ k))
        ≅*⟨ refl≡ (rev-++ r _) ⟩
          (((rev (suc (suc n) ↑ k) ++ suc n ∷ []) ++ n ∷ []) ++ suc (k + n) ∷ []) ++ rev r
        ≅*⟨ ++r (rev r) (refl≡ (start+end (start+end (start+end (rev-u (2 + n) k) refl) refl) refl)) ⟩
          ((((suc (suc n) ↓ k) ++ suc n ∷ []) ++ n ∷ []) ++ suc (k + n) ∷ []) ++ rev r
        ≅*⟨ ++r (rev r) (refl≡ (start+end (start+end (++-↓ (1 + n) k) refl) refl)) ⟩
          k + suc n ∷ (((suc n ↓ k) ++ n ∷ []) ++ suc (k + n) ∷ []) ++ rev r
        ≅*⟨ ++r (rev r) (refl≡ (start+end (++-↓ n (1 + k)) refl)) ⟩
          suc (k + n) ∷ k + n ∷ ((n ↓ k) ++ suc (k + n) ∷ []) ++ rev r
        ≅*⟨ ++r (rev r) (long k [] []) ⟩
          k + n ∷ suc (k + n) ∷ k + n ∷ ((n ↓ k) ++ []) ++ rev r
        ≅*⟨ ++r (rev r) (l++ (k + n ∷ suc (k + n) ∷ k + n ∷ []) (refl≡ (++-unit))) ⟩
          k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k) ++ rev r
        ≅*∎
      right* =
        ≅*begin
          rev (r ++ suc (k + n) ∷ n ∷ suc n ∷ (suc (suc n) ↑ k)) ++ k1 ∷ n1 ∷ []
        ≅*⟨ ++r (k1 ∷ n1 ∷ []) right ⟩
          k + n ∷ suc (k + n) ∷ k + n ∷ ((n ↓ k) ++ rev r) ++ k1 ∷ n1 ∷ []
        ≅*⟨ refl≡ (++-assoc (k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k)) (rev r) (k1 ∷ n1 ∷ [])) ⟩
          k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k) ++ rev r ++ k1 ∷ n1 ∷ []
        ≅*∎
  in  _ , ( (l++ (k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k)) left) , right*)
swap-long-lemma-rev n k n1 k1 pkn (x ∷ r) l1 (x₁ ∷ r1) p rewrite (≡-sym (cut-tail p)) =
  let rec-m , rec-l , rec-r = swap-long-lemma-rev n k n1 k1 pkn r l1 r1 (cut-head p)
      ll = trans (refl≡ (≡-sym (++-assoc (k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k)) (rev r) [ x ]))) (++r [ x ] rec-l)
      rr = trans (refl≡ (≡-sym (++-assoc (rev l1) ( _ ∷ _ ∷ rev r1) [ x ]))) (++r [ x ] rec-r)
  in  _ , (ll , rr)


swap-long-lemma : (n k n1 k1 : ℕ) -> (pkn : suc k1 < n1) -> (r l1 r1 : List ℕ) -> (((n ↓ (2 + k)) ++ (1 + k + n) ∷ r) ≡ (l1 ++ n1 ∷ k1 ∷ r1)) -> ∃ (λ mf -> ((((k + n) ∷ (n ↓ (2 + k)) ++ r) ≅* mf) × ((l1 ++ (k1 ∷ n1 ∷ r1))) ≅* mf))
swap-long-lemma n k n1 k1 pkn r l1 r1 p =
  let pp =
        begin
          rev r ++ suc (k + n) ∷ n ∷ suc n ∷ (suc (suc n) ↑ k)
        ≡⟨ start+end refl (start+end (refl {x = [ suc (k + n) ]}) (≡-sym (++-↑ n (suc k)))) ⟩
          rev r ++ suc (k + n) ∷ n ∷ (suc n ↑ k) ++ suc (k + n) ∷ []
        ≡⟨ start+end refl (start+end (refl {x = [ suc (k + n) ]}) (≡-sym (start+end (++-↑ n k) refl))) ⟩
          rev r ++ suc (k + n) ∷ [] ++ ((n ↑ k) ++ [ k + n ] ) ++ suc (k + n) ∷ []
        ≡⟨ start+end (refl {x = rev r}) (start+end (refl {x = [ suc (k + n) ]}) (++-assoc (n ↑ k) (k + n ∷ []) (suc (k + n) ∷ []))) ⟩
          rev r ++ suc (k + n) ∷ [] ++ (n ↑ k) ++ k + n ∷ suc (k + n) ∷ []
        ≡⟨ start+end refl (start+end (refl {x = [ suc (k + n) ]}) (start+end (≡-sym (rev-d n k)) refl)) ⟩
          rev r ++ suc (k + n) ∷ [] ++ rev (n ↓ k) ++ k + n ∷ suc (k + n) ∷ []
        ≡⟨ ≡-sym (++-assoc (rev r) (suc (k + n) ∷ []) (rev (n ↓ k) ++ k + n ∷ suc (k + n) ∷ [])) ⟩
          (rev r ++ suc (k + n) ∷ []) ++ rev (n ↓ k) ++ k + n ∷ suc (k + n) ∷ []
        ≡⟨ ≡-sym (++-assoc _ (rev (n ↓ k)) (k + n ∷ suc (k + n) ∷ [])) ⟩
          ((rev r ++ suc (k + n) ∷ []) ++ rev (n ↓ k)) ++ k + n ∷ suc (k + n) ∷ []
        ≡⟨ ≡-sym (start+end (rev-++ (n ↓ k) (suc (k + n) ∷ r)) refl) ⟩
          rev ((n ↓ k) ++ suc (k + n) ∷ r) ++ k + n ∷ suc (k + n) ∷ []
        ≡⟨ ≡-sym (++-assoc (rev ((n ↓ k) ++ suc (k + n) ∷ r)) (k + n ∷ []) (suc (k + n) ∷ []))  ⟩
          (rev ((n ↓ k) ++ suc (k + n) ∷ r) ++ k + n ∷ []) ++ suc (k + n) ∷ []
        ≡⟨ cong rev p ⟩
          rev (l1 ++ n1 ∷ k1 ∷ r1)
        ≡⟨ rev-++ l1 (n1 ∷ k1 ∷ r1) ⟩
          ((rev r1 ++ k1 ∷ []) ++ n1 ∷ []) ++ rev l1
        ≡⟨ ++-assoc (rev r1 ++ k1 ∷ []) (n1 ∷ []) (rev l1) ⟩
          (rev r1 ++ k1 ∷ []) ++ n1 ∷ rev l1
        ≡⟨ ++-assoc _ [ k1 ] _ ⟩
          rev r1 ++ k1 ∷ n1 ∷ rev l1
        ∎
      call-m , call-l , call-r = swap-long-lemma-rev n k n1 k1 pkn (rev r) (rev l1) (rev r1) pp
      ll = trans (refl≡ (start+end refl (rev-rev {r}))) call-l
      rr = trans (refl≡ (start+end (rev-rev {l1}) (start+end refl (rev-rev {r1})))) call-r
  in  call-m , ll , rr

--
-- long-long-lemma : (n k t n1 k1 t1 : ℕ) -> (suc n ≤ t) -> (suc n1 ≤ t1) -> (l r l1 r1 : List ℕ) -> (((n ↓ k) ++ t ∷ r) ≡ ((n1 ↓ k1) ++ t1 ∷ r1)) -> ∃ (λ mf -> (((n ↓ k) ++ t ∷ r) ≅* mf) × ((n1 ↓ k1) ++ t1 ∷ r1) ≅* mf)
-- long-long-lemma zero zero t zero zero .t pt pt1 l r l1 .r refl = _ , (refl , refl)
-- long-long-lemma zero zero t zero (suc k1) .t pt pt1 l r l1 .r refl = _ , (refl , refl)
-- long-long-lemma zero zero t (suc n1) zero .t pt pt1 l r l1 .r refl = _ , (refl , refl)
-- long-long-lemma zero zero t (suc .t) (suc k1) t1 pt pt1 l .((t ↓ k1) ++ t1 ∷ r1) l1 r1 refl = _ , (refl , refl)
-- long-long-lemma zero (suc k) t zero zero .t pt pt1 l r l1 .r refl = _ , (refl , refl)
-- long-long-lemma zero (suc k) t zero (suc k1) .t pt pt1 l r l1 .r refl = _ , (refl , refl)
-- long-long-lemma zero (suc k) t (suc n1) zero .t pt pt1 l r l1 .r refl = _ , (refl , refl)
-- long-long-lemma zero (suc k) t (suc .t) (suc k1) t1 pt pt1 l .((t ↓ k1) ++ t1 ∷ r1) l1 r1 refl = _ , (refl , refl)
-- long-long-lemma (suc n) zero t zero zero .t pt pt1 l r l1 .r refl = _ , (refl , refl)
-- long-long-lemma (suc n) zero t zero (suc k1) .t pt pt1 l r l1 .r refl = _ , (refl , refl)
-- long-long-lemma (suc n) zero t (suc n1) zero .t pt pt1 l r l1 .r refl = _ , (refl , refl)
-- long-long-lemma (suc n) zero t (suc .t) (suc k1) t1 pt pt1 l .((t ↓ k1) ++ t1 ∷ r1) l1 r1 refl = _ , (refl , refl)
-- long-long-lemma (suc n) (suc k) t zero zero .n pt pt1 l r l1 .((n ↓ k) ++ t ∷ r) refl = _ , (refl , refl)
-- long-long-lemma (suc n) (suc k) t zero (suc k1) .n pt pt1 l r l1 .((n ↓ k) ++ t ∷ r) refl = _ , (refl , refl)
-- long-long-lemma (suc n) (suc k) t (suc n1) zero .n pt pt1 l r l1 .((n ↓ k) ++ t ∷ r) refl = _ , (refl , refl)
-- long-long-lemma (suc n) (suc k) t (suc n1) (suc k1) t1 pt pt1 l r l1 r1 p =
--   let rec-m , rec-l , rec-r = long-long-lemma n k t n1 k1 t1 (≤-down pt) (≤-down pt1) l r l1 r1 (cut-head p)
--       ll = l++ [ n1 ] rec-l
--       rr = l++ [ n1 ] rec-r
--   in  _ , (trans (refl≡ (cong (λ e -> e ∷ _) (cut-tail p))) ll , rr)

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
--
-- -- TODO
-- diamond m1 m2 m3 (long≅ {n} k1 [] r m mf defm defmf) (long≅ {n₁} k2 [] r₁ m₁ mf₁ defm₁ defmf₁)
--   rewrite defmf rewrite defmf₁ =
--   let eq = ≡-trans (≡-sym defm) defm₁
--       eqn , eql , eqr = long-lemma n n₁ k1 k2 (suc n) (suc n₁) (≤-reflexive refl) (≤-reflexive refl) r r₁ eq
--   in  _ , (refl , refl≡ (head+tail (≡-sym eqn) (start+end (≡-sym eql) (≡-sym eqr))))

-- diamond m1 m2 m3 (cancel≅ {n₁} (x₁ ∷ l) r .m1 .m2 defm defmf) (long≅ {n} k [] r₁ .m1 .m3 defm₁ defmf₁)
--   rewrite defmf rewrite defmf₁ =
--   let eq = ≡-trans (≡-sym defm₁) defm
--       eqx = cut-tail eq
--       rec-m , rec-l , rec-r = cancel-long-lemma (2 + n) (2 + k) (suc n) n₁ {!   !} [] r₁ (x₁ ∷ l) r eq
--       rr = rec-r
--       ll = {!!}
--   in  rec-m , (rr , ll) -- TODO remove this stuff above
-- diamond m1 m2 m3 (swap≅ x (x₁ ∷ l) r .m1 .m2 defm defmf) (long≅ k [] r₁ .m1 .m3 defm₁ defmf₁) = {!   !}
-- diamond m1 m2 m3 (long≅ k [] r .m1 .m2 defm defmf) (long≅ k₁ (x ∷ l₁) r₁ .m1 .m3 defm₁ defmf₁) = {!   !}

-- diamond-full : {m1 m2 m3 : List ℕ} -> (m1 ≅* m2) -> (m1 ≅* m3) -> ∃ (λ m -> (m2 ≅* m) × (m3 ≅* m))
-- diamond-full refl q = _ , (q , refl)
-- diamond-full (trans≅ x p) refl = _ , refl , trans≅ x p
-- diamond-full (trans≅ x refl) (trans≅ y refl) = diamond _ _ _ x y
-- diamond-full {m1} {m2} {m3} (trans≅ x (trans≅ y p)) (trans≅ z refl) =
--   let one-m , one-l , one-r = diamond _ _ _ x z
--       rec-m , rec-l , rec-r = diamond-full {_} {m2} {one-m} (trans≅ y p) one-l
--   in  rec-m , rec-l , trans one-r rec-r
-- diamond-full {m1} {m2} {m3} (trans≅ x p) (trans≅ y (trans≅ {m4} z q)) =
--   let rec-m , rec-l , rec-r = diamond-full (trans≅ x p) (ext y)
--       rec-mm , rec-ll , rec-rr = diamond-full {m4} {rec-m} {_} rec-r (trans≅ z q)
--   in  rec-mm , trans rec-l rec-ll , rec-rr

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
