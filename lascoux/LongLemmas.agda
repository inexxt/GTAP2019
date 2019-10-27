{-# OPTIONS --allow-unsolved-metas --without-K #-}
module LongLemmas where

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
open import Lists
open import Compact hiding (n; l)
open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to ≤∎) hiding (_≡⟨_⟩_; _≡⟨⟩_)


open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)


variable
    n : ℕ
    l : List ℕ

open ≅*-Reasoning
open Relation.Binary.PropositionalEquality.≡-Reasoning

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

-- repeat-long-lemma : (n k n1 : ℕ) -> (l r : List ℕ) -> (n ↓ k) ≡ (l ++ n1 ∷ n1 ∷ r) -> ⊥
-- repeat-long-lemma n zero n1 [] r ()
-- repeat-long-lemma n zero n1 (x ∷ l) r ()
-- repeat-long-lemma n (suc (suc k)) n1 [] r p =
--   abs-refl (≤-trans (≤-reflexive (cut-t1 p)) (≤-reflexive (≡-sym (cut-t2 p))))
-- repeat-long-lemma n (suc k) n1 (x ∷ l) r p = repeat-long-lemma n k n1 l r (cut-head p)

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
incr-long-lemma-rev n (suc (suc k)) .(suc n) .n pkn [] .(suc (suc n) ↑ k) refl = abs-refl pkn
incr-long-lemma-rev n (suc k) n1 k1 pkn (x ∷ l) r p = incr-long-lemma-rev (suc n) k n1 k1 pkn l r (cut-head p)

swap-long-lemma-base : (n k k1 : ℕ) -> (pkn : suc k1 < suc (k + n))
                       -> (q1 : k1 ≤ n) -> (q2 : n ≤ 1 + k1)
                       -> ((k1 ∷ (1 + k + n) ∷ (n ↑ (2 + k))) ≡ (k1 ∷ suc (k + n) ∷ (n ↑ (2 + k))))
                       -> ∃ (λ mf -> (((k + n) ∷ (n ↓ (2 + k)) ++ [ k1 ]) ≅* mf) × (((rev (n ↑ (2 + k))) ++ (k1 ∷ suc (k + n) ∷ [])) ≅* mf))
swap-long-lemma-base n k k1 pkn q1 q2 p with (≤-∃ _ _ q1)
swap-long-lemma-base n zero k1 pkn q1 q2 p | zero , snd rewrite (≡-sym snd) = abs-refl pkn
swap-long-lemma-base n (suc k) k1 pkn q1 q2 p | zero , snd rewrite (≡-sym snd) =
  let left = refl≡ (head+tail (≡-sym (+-three-assoc {k} {1} {k1}))
                   (head+tail (≡-sym (+-three-assoc {1 + k} {1} {k1}))
                   (head+tail (≡-sym (+-three-assoc {k} {1} {k1})) refl)))
      left* =
        ≅*begin
          _
        ≅*⟨ left ⟩
          k + suc k1 ∷ suc (k + suc k1) ∷ k + suc k1 ∷ (k1 ↓ (1 + k)) ++ k1 ∷ []
        ≅*⟨ refl≡ (start+end (refl {x = k + suc k1 ∷ suc (k + suc k1) ∷ k + suc k1 ∷ []}) (start+end (≡-sym (++-↓ k1 k)) refl)) ⟩
          k + suc k1 ∷ suc (k + suc k1) ∷ k + suc k1 ∷ ((suc k1 ↓ k) ++ k1 ∷ []) ++ k1 ∷ []
        ≅*⟨ refl≡ (++-assoc (k + suc k1 ∷  suc (k + suc k1) ∷ k + suc k1 ∷ (suc k1 ↓ k)) [ k1 ] [ k1 ]) ⟩
          k + suc k1 ∷  suc (k + suc k1) ∷ k + suc k1 ∷ (suc k1 ↓ k) ++ k1 ∷ k1 ∷ []
        ≅*⟨ cancel _ [] ⟩
          k + suc k1 ∷ suc (k + suc k1) ∷ k + suc k1 ∷ (suc k1 ↓ k) ++ []
        ≅*⟨ refl≡ ++-unit ⟩
          k + suc k1 ∷ suc (k + suc k1) ∷ k + suc k1 ∷ (suc k1 ↓ k)
        ≅*∎
      right =
        ≅*begin
          _
        ≅*⟨ refl≡ (++-assoc _ (k1 ∷ []) (k1 ∷ suc (suc (k + k1)) ∷ [])) ⟩
          _
        ≅*⟨ refl≡ (telescope-rev (suc k1) k (k1 ∷ k1 ∷ suc (suc (k + k1)) ∷ [])) ⟩
          _
        ≅*⟨ cancel ((1 + k1) ↓ (2 + k)) (suc (suc (k + k1)) ∷ []) ⟩
          _
        ≅*⟨ l++ (suc k1 ↓ (2 + k)) (refl≡ (head+tail (≡-sym (+-three-assoc {1 + k} {1} {k1})) refl)) ⟩
          (suc k1 ↓ (2 + k)) ++ suc (k + suc k1) ∷ []
        ≅*⟨ long {1 + k1} k [] [] ⟩
          k + suc k1 ∷ (suc k1 ↓ (2 + k)) ++ []
        ≅*⟨ refl≡ ++-unit ⟩
          k + suc k1 ∷ (suc k1 ↓ (2 + k))
        ≅*∎
  in  _  , (left* , right)
swap-long-lemma-base n k k1 pkn q1 q2 p | suc zero , snd rewrite (≡-sym snd) =
  let left = l++ (k + suc k1 ∷ suc (k + suc k1) ∷ []) (refl≡ (++-↓ k1 (1 + k) ))
      right =
        ≅*begin
          _
        ≅*⟨ refl≡ (telescope-rev (suc k1) k (k1 ∷ (suc (k + suc k1)) ∷ [])) ⟩
          (suc k1 ↓ (2 + k)) ++ k1 ∷ suc (k + suc k1) ∷ []
        ≅*⟨ refl≡ (≡-sym (++-assoc (suc k1 ↓ (2 + k)) _ (suc (k + suc k1) ∷ []))) ⟩
          ((suc k1 ↓ (2 + k)) ++ k1 ∷ []) ++ suc (k + suc k1) ∷ []
        ≅*⟨ ++r (suc (k + suc k1) ∷ []) (refl≡ (++-↓ k1 ( 2 + k )))   ⟩
          (k1 ↓ (3 + k)) ++ suc (k + suc k1) ∷ []
        ≅*⟨ short-swap-l {k1} {suc k} {k + suc k1} [] (≤-trans (≤-up (≤-reflexive refl)) (≤-up-+ (≤-reflexive refl))) (s≤s (≤-reflexive (+-three-assoc {k} {1} {k1}))) ⟩
          k + suc k1 ∷ suc (suc (k + k1)) ∷ suc (k + k1) ∷ k + k1 ∷ (k1 ↓ k)
        ≅*⟨ refl≡ (head+tail refl (head+tail (≡-sym (+-three-assoc {1 + k} {1} {k1})) refl)) ⟩
          k + suc k1 ∷ suc (k + suc k1) ∷ (k1 ↓ (2 + k))
        ≅*∎
  in  _ , (left , right)
swap-long-lemma-base n k k1 pkn q1 q2 p | suc (suc fst) , snd rewrite (≡-sym snd) = abs-refl (≤-trans q2 (s≤s (≤-up-+ (≤-reflexive refl))))

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
      right = telescope-rev n k (k1 ∷ suc (k + n) ∷ [])
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
swap-long-lemma-rev n k .(suc (k + n)) k1 pkn (.k1 ∷ []) .(n ∷ (suc n ↑ suc k)) [] refl | no q with n <? k1
... | no q2 =
  let qq = ≰⇒> q
      qq2 = ≰⇒> q2

  in  {!   !}
... | yes q2 =
  let sk1 , sk1p = ≤-∃ {!   !} {!   !} {!   !}
      qq : n < 2 + k1
      qq = ≰⇒> q
      left =
        ≅*begin
          {!   !}
        ≅*⟨ {!   !} ⟩
          k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k) ++ (suc sk1) ∷ []
        ≅*⟨ short-swap-l [ k + n ] {!   !} {!   !} ⟩
          k + n ∷ sk1 ∷ suc (k + n) ∷ k + n ∷ (n ↓ k)
        ≅*⟨ {!!} ⟩
          {!!}
        ≅*⟨ {!!} ⟩
          {!!}
        ≅*∎
      right = telescope-rev n k ((suc sk1) ∷ suc (k + n) ∷ [])
      right* =
        ≅*begin
          {!   !}
        ≅*⟨ {!   !} ⟩
          ((rev (suc (suc n) ↑ k) ++ suc n ∷ []) ++ n ∷ []) ++ (suc sk1) ∷ suc (k + n) ∷ []
        ≅*⟨ refl≡ right ⟩
          suc (k + n) ∷ k + n ∷ (n ↓ k) ++ (suc sk1) ∷ suc (k + n) ∷ []
        ≅*⟨ {!!} ⟩
          {!!}
        ≅*⟨ {!!} ⟩
          {!!}
        ≅*⟨ {!!} ⟩
          {!!}
        ≅*∎
  in  _ , (left , right*)
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
