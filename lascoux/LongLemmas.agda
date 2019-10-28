{-# OPTIONS --allow-unsolved-metas --without-K #-}
module LongLemmas where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (Σ; ∃; _×_; _,_)

open import Relation.Nullary
open import Data.Empty
open import Data.Sum hiding (swap)
open import Data.Bool hiding (_<_; _≤_; _≟_; _<?_; _≤?_)
open import Data.Bool.Properties hiding (≤-reflexive; ≤-trans; _≟_; _<?_; _≤?_)
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

long-lemma : (n n1 k k1 t t1 : ℕ) -> (suc n ≤ t) -> (suc n1 ≤ t1) -> (r r1 : List ℕ) -> (n ↓ (2 + k)) ++ t ∷ r ≡ (n1 ↓ (2 + k1)) ++ t1 ∷ r1
             -> (n ≡ n1) × ((n ↓ (2 + k)) ≡ (n1 ↓ (2 + k1))) × (r ≡ r1)
long-lemma n n1 zero zero t t1 pnt pnt1 r r1 p rewrite (cut-t1 p) rewrite (cut-t2 p) rewrite (cut-t3 p) rewrite (cut-h3 p) = refl , (refl , refl)
long-lemma n n1 zero (suc k1) t t1 pnt pnt1 r r1 p rewrite (cut-t1 p) rewrite (cut-t2 p) rewrite (cut-t3 p) rewrite (cut-h3 p) = abs-suc pnt
long-lemma n n1 (suc k) zero t t1 pnt pnt1 r r1 p rewrite ≡-sym (cut-t1 p) rewrite ≡-sym (cut-t2 p) rewrite ≡-sym (cut-t3 p) rewrite (cut-h3 p) = abs-suc pnt1
long-lemma n n1 (suc k) (suc k1) t t1 pnt pnt1 r r1 p =
  let rec-m , rec-l , rec-r = long-lemma n n1 k k1 t t1 pnt pnt1 r r1 (cut-head p)
  in  rec-m , ((head+tail (cong suc (cut-t2 p) ) rec-l) , rec-r)


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

-- cancel-long-lemma : (n k n1 : ℕ) -> (r l1 r1 : List ℕ) -> (((n ↓ (2 + k)) ++ (1 + k + n) ∷ r) ≡ (l1 ++ n1 ∷ n1 ∷ r1)) -> ∃ (λ mf -> ((((k + n) ∷ (n ↓ (2 + k)) ++ r) ≅* mf) × ((l1 ++ r1)) ≅* mf))
-- cancel-long-lemma n k n1 r l1 r1 p =
--   let pp =
--         begin
--           {!   !}
--         ≡⟨ {!!} ⟩
--           {!   !}
--         ≡⟨ p ⟩
--           l1 ++ n1 ∷ n1 ∷ r1
--         ≡⟨ {!!} ⟩
--           {!   !}
--         ∎
--       rec-m , rec-l , rec-r = cancel-long-lemma-rev n k n1 (rev r) (rev l1) (rev r1) pp
--   in {!   !}

-- incr-long-lemma-rev : (n k n1 k1 : ℕ) -> (suc k1 < n1) -> (l r : List ℕ) -> (n ↑ k) ≡ (l ++ k1 ∷ n1 ∷ r) -> ⊥
-- incr-long-lemma-rev n (suc (suc k)) .(suc n) .n pkn [] .(suc (suc n) ↑ k) refl = abs-refl pkn
-- incr-long-lemma-rev n (suc k) n1 k1 pkn (x ∷ l) r p = incr-long-lemma-rev (suc n) k n1 k1 pkn l r (cut-head p)

-- swap-long-lemma-base : (n k k1 : ℕ) -> (pkn : suc k1 < suc (k + n))
--                        -> (q1 : k1 ≤ n) -> (q2 : n ≤ 1 + k1)
--                        -> ((k1 ∷ (1 + k + n) ∷ (n ↑ (2 + k))) ≡ (k1 ∷ suc (k + n) ∷ (n ↑ (2 + k))))
--                        -> ∃ (λ mf -> (((k + n) ∷ (n ↓ (2 + k)) ++ [ k1 ]) ≅* mf) × (((rev (n ↑ (2 + k))) ++ (k1 ∷ suc (k + n) ∷ [])) ≅* mf))
-- swap-long-lemma-base n k k1 pkn q1 q2 p with (≤-∃ _ _ q1)
-- swap-long-lemma-base n zero k1 pkn q1 q2 p | zero , snd rewrite (≡-sym snd) = abs-refl pkn
-- swap-long-lemma-base n (suc k) k1 pkn q1 q2 p | zero , snd rewrite (≡-sym snd) =
--   let left = refl≡ (head+tail (≡-sym (+-three-assoc {k} {1} {k1}))
--                    (head+tail (≡-sym (+-three-assoc {1 + k} {1} {k1}))
--                    (head+tail (≡-sym (+-three-assoc {k} {1} {k1})) refl)))
--       left* =
--         ≅*begin
--           _
--         ≅*⟨ left ⟩
--           k + suc k1 ∷ suc (k + suc k1) ∷ k + suc k1 ∷ (k1 ↓ (1 + k)) ++ k1 ∷ []
--         ≅*⟨ refl≡ (start+end (refl {x = k + suc k1 ∷ suc (k + suc k1) ∷ k + suc k1 ∷ []}) (start+end (≡-sym (++-↓ k1 k)) refl)) ⟩
--           k + suc k1 ∷ suc (k + suc k1) ∷ k + suc k1 ∷ ((suc k1 ↓ k) ++ k1 ∷ []) ++ k1 ∷ []
--         ≅*⟨ refl≡ (++-assoc (k + suc k1 ∷  suc (k + suc k1) ∷ k + suc k1 ∷ (suc k1 ↓ k)) [ k1 ] [ k1 ]) ⟩
--           k + suc k1 ∷  suc (k + suc k1) ∷ k + suc k1 ∷ (suc k1 ↓ k) ++ k1 ∷ k1 ∷ []
--         ≅*⟨ cancel _ [] ⟩
--           k + suc k1 ∷ suc (k + suc k1) ∷ k + suc k1 ∷ (suc k1 ↓ k) ++ []
--         ≅*⟨ refl≡ ++-unit ⟩
--           k + suc k1 ∷ suc (k + suc k1) ∷ k + suc k1 ∷ (suc k1 ↓ k)
--         ≅*∎
--       right =
--         ≅*begin
--           _
--         ≅*⟨ refl≡ (++-assoc _ (k1 ∷ []) (k1 ∷ suc (suc (k + k1)) ∷ [])) ⟩
--           _
--         ≅*⟨ refl≡ (telescope-rev (suc k1) k (k1 ∷ k1 ∷ suc (suc (k + k1)) ∷ [])) ⟩
--           _
--         ≅*⟨ cancel ((1 + k1) ↓ (2 + k)) (suc (suc (k + k1)) ∷ []) ⟩
--           _
--         ≅*⟨ l++ (suc k1 ↓ (2 + k)) (refl≡ (head+tail (≡-sym (+-three-assoc {1 + k} {1} {k1})) refl)) ⟩
--           (suc k1 ↓ (2 + k)) ++ suc (k + suc k1) ∷ []
--         ≅*⟨ long {1 + k1} k [] [] ⟩
--           k + suc k1 ∷ (suc k1 ↓ (2 + k)) ++ []
--         ≅*⟨ refl≡ ++-unit ⟩
--           k + suc k1 ∷ (suc k1 ↓ (2 + k))
--         ≅*∎
--   in  _  , (left* , right)
-- swap-long-lemma-base n k k1 pkn q1 q2 p | suc zero , snd rewrite (≡-sym snd) =
--   let left = l++ (k + suc k1 ∷ suc (k + suc k1) ∷ []) (refl≡ (++-↓ k1 (1 + k) ))
--       right =
--         ≅*begin
--           _
--         ≅*⟨ refl≡ (telescope-rev (suc k1) k (k1 ∷ (suc (k + suc k1)) ∷ [])) ⟩
--           (suc k1 ↓ (2 + k)) ++ k1 ∷ suc (k + suc k1) ∷ []
--         ≅*⟨ refl≡ (≡-sym (++-assoc (suc k1 ↓ (2 + k)) _ (suc (k + suc k1) ∷ []))) ⟩
--           ((suc k1 ↓ (2 + k)) ++ k1 ∷ []) ++ suc (k + suc k1) ∷ []
--         ≅*⟨ ++r (suc (k + suc k1) ∷ []) (refl≡ (++-↓ k1 ( 2 + k )))   ⟩
--           (k1 ↓ (3 + k)) ++ suc (k + suc k1) ∷ []
--         ≅*⟨ short-swap-l {k1} {suc k} {k + suc k1} [] (≤-trans (≤-up (≤-reflexive refl)) (≤-up-+ (≤-reflexive refl))) (s≤s (≤-reflexive (+-three-assoc {k} {1} {k1}))) ⟩
--           k + suc k1 ∷ suc (suc (k + k1)) ∷ suc (k + k1) ∷ k + k1 ∷ (k1 ↓ k)
--         ≅*⟨ refl≡ (head+tail refl (head+tail (≡-sym (+-three-assoc {1 + k} {1} {k1})) refl)) ⟩
--           k + suc k1 ∷ suc (k + suc k1) ∷ (k1 ↓ (2 + k))
--         ≅*∎
--   in  _ , (left , right)
-- swap-long-lemma-base n k k1 pkn q1 q2 p | suc (suc fst) , snd rewrite (≡-sym snd) = abs-refl (≤-trans q2 (s≤s (≤-up-+ (≤-reflexive refl))))

-- swap-long-lemma-rev : (n k n1 k1 : ℕ) -> (pkn : suc k1 < n1)-> (r l1 r1 : List ℕ) -> ((r ++ (1 + k + n) ∷ (n ↑ (2 + k))) ≡ (r1 ++ k1 ∷ n1 ∷ l1)) -> ∃ (λ mf -> ((((k + n) ∷ (n ↓ (2 + k)) ++ (rev r)) ≅* mf) × (((rev l1) ++ (k1 ∷ n1 ∷ rev r1))) ≅* mf))
-- swap-long-lemma-rev n k n1 k1 pkn [] l1 [] p =
--   let fst = cut-t1 p
--       snd = cut-t2 p
--   in  abs-refl (≤-trans (≤-trans (≤-trans (s≤s (≤-up (≤-up (≤-up-+ (≤-reflexive refl))))) (≤-reflexive (cong (λ e -> 2 + e ) fst))) pkn) (≤-reflexive (≡-sym snd)))
-- swap-long-lemma-rev n k .(suc n) .n pkn [] .(suc (suc n) ↑ k) (.(suc (k + n)) ∷ []) refl = abs-refl pkn
-- swap-long-lemma-rev n (suc k) .(suc (suc n)) .(suc n) pkn [] .(suc (suc (suc n)) ↑ k) (.(suc (suc (k + n))) ∷ .n ∷ []) refl = abs-refl pkn
-- swap-long-lemma-rev n k n1 k1 pkn [] l1 (x ∷ x₁ ∷ x₂ ∷ r1) p = ⊥-elim (incr-long-lemma-rev (suc (suc n)) k n1 k1 pkn r1 l1 (cut-h3 p))

-- swap-long-lemma-rev n k .(suc (k + n)) k1 pkn (.k1 ∷ []) .(n ∷ suc n ∷ (suc (suc n) ↑ k)) [] refl with suc k1 <? n
-- ... | yes p =
--   let left =
--         ≅*begin
--           k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k) ++ k1 ∷ []
--         ≅*⟨ long-swap<-lr k1 n (2 + k) [ k + n ] [] p ⟩
--           k + n ∷ k1 ∷ suc (k + n) ∷ k + n ∷ (n ↓ k) ++ []
--         ≅*⟨ refl≡ (++-unit) ⟩
--           k + n ∷ k1 ∷ suc (k + n) ∷ k + n ∷ (n ↓ k)
--         ≅*⟨ swap (≤-trans p (≤-up-+ (≤-reflexive refl))) [] _ ⟩
--           k1 ∷ k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k)
--         ≅*∎
--       right = telescope-rev n k (k1 ∷ suc (k + n) ∷ [])
--       right* =
--         ≅*begin
--           ((rev (suc (suc n) ↑ k) ++ suc n ∷ []) ++ n ∷ []) ++ k1 ∷ suc (k + n) ∷ []
--         ≅*⟨ refl≡ right ⟩
--           suc (k + n) ∷ k + n ∷ (n ↓ k) ++ k1 ∷ suc (k + n) ∷ []
--         ≅*⟨ long-swap<-lr k1 n (suc (suc k)) [] (suc (k + n) ∷ []) p ⟩
--           k1 ∷ suc (k + n) ∷ k + n ∷ (n ↓ k) ++ suc (k + n) ∷ []
--         ≅*⟨ long k [ k1 ] [] ⟩
--           k1 ∷ k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k) ++ []
--         ≅*⟨ refl≡ (++-unit) ⟩
--           k1 ∷ k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k)
--         ≅*∎
--   in  _ , ( left , right*)
-- swap-long-lemma-rev n k .(suc (k + n)) k1 pkn (.k1 ∷ []) .(n ∷ (suc n ↑ suc k)) [] refl | no q with n <? k1
-- ... | no q2 =
--   let qq = ≰⇒> q
--       qq2 = ≰⇒> q2
--   in  swap-long-lemma-base n k k1 pkn (≤-down2 qq2) (≤-down2 qq) refl
-- ... | yes q2 =
--   let sk1 , sk1p = ≤-∃ 1 k1 (≤-down-+ q2)
--       qq : n < 2 + k1
--       qq = ≰⇒> q

--       k1=1+sk1 : k1 ≡ suc sk1
--       k1=1+sk1 = ≡-trans (≡-sym sk1p) (+-comm _ 1)

--       n≤sk1 : n ≤ sk1
--       n≤sk1 = (≤-down2 (≤-trans q2 (≤-reflexive k1=1+sk1)))
--       sk1≤k+n : suc sk1 ≤ suc (k + n)
--       sk1≤k+n = (≤-trans (s≤s (≤-up (≤-down (≤-reflexive (≡-sym k1=1+sk1))))) pkn)
--       left =
--         ≅*begin
--           k + n ∷ (n ↓ (2 + k)) ++ k1 ∷ []
--         ≅*⟨ refl≡ (cong (λ e -> (k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k)) ++ [ e ]) k1=1+sk1) ⟩
--           k + n ∷ (n ↓ (2 + k)) ++ (suc sk1) ∷ []
--         ≅*⟨ short-swap-l [ k + n ] n≤sk1 sk1≤k+n ⟩
--           k + n ∷ sk1 ∷ (n ↓ (2 + k))
--         ≅*⟨ swap (≤-down2 (≤-trans (s≤s (s≤s (≤-reflexive (≡-sym k1=1+sk1)))) pkn)) [] _ ⟩
--           sk1 ∷ k + n ∷ (n ↓ (2 + k))
--         ≅*∎
--       right = telescope-rev n k ((suc sk1) ∷ suc (k + n) ∷ [])
--       right* =
--         ≅*begin
--           _
--         ≅*⟨ refl≡ (cong (λ e -> ((rev (suc (suc n) ↑ k) ++ suc n ∷ []) ++ n ∷ []) ++ e ∷ suc (k + n) ∷ [] ) k1=1+sk1) ⟩
--           ((rev (suc (suc n) ↑ k) ++ suc n ∷ []) ++ n ∷ []) ++ (suc sk1) ∷ suc (k + n) ∷ []
--         ≅*⟨ refl≡ right ⟩
--            (n ↓ (2 + k)) ++ (suc sk1) ∷ suc (k + n) ∷ []
--         ≅*⟨ refl≡ (≡-sym (++-assoc (n ↓ (2 + k)) [ suc sk1 ] [ suc (k + n) ])) ⟩
--           ((n ↓ (2 + k)) ++ [ suc sk1 ]) ++ suc (k + n) ∷ []
--         ≅*⟨ ++r [ suc (k + n) ] (short-swap-l [] n≤sk1 sk1≤k+n) ⟩
--           sk1 ∷ (n ↓ (2 + k)) ++ suc (k + n) ∷ []
--         ≅*⟨ short-swap-l [ sk1 ] (≤-up-+ (≤-reflexive refl)) (≤-reflexive refl) ⟩
--           _
--         ≅*∎
--   in  _ , (left , right*)
-- swap-long-lemma-rev n k n1 k1 pkn (.k1 ∷ .n1 ∷ r) .(r ++ suc (k + n) ∷ n ∷ suc n ∷ (suc (suc n) ↑ k)) [] refl =
--   let left =
--         ≅*begin
--           (rev r ++ n1 ∷ []) ++ k1 ∷ []
--         ≅*⟨ refl≡ (++-assoc (rev r) [ n1 ] [ k1 ]) ⟩
--           rev r ++ n1 ∷ [] ++ k1 ∷ []
--         ≅*⟨ swap pkn (rev r) [] ⟩
--           rev r ++ k1 ∷ [] ++ n1 ∷ []
--         ≅*∎
--       right =
--         ≅*begin
--           rev (r ++ suc (k + n) ∷ n ∷ suc n ∷ (suc (suc n) ↑ k))
--         ≅*⟨ refl≡ (rev-++ r _) ⟩
--           (((rev (suc (suc n) ↑ k) ++ suc n ∷ []) ++ n ∷ []) ++ suc (k + n) ∷ []) ++ rev r
--         ≅*⟨ ++r (rev r) (refl≡ (start+end (start+end (start+end (rev-u (2 + n) k) refl) refl) refl)) ⟩
--           ((((suc (suc n) ↓ k) ++ suc n ∷ []) ++ n ∷ []) ++ suc (k + n) ∷ []) ++ rev r
--         ≅*⟨ ++r (rev r) (refl≡ (start+end (start+end (++-↓ (1 + n) k) refl) refl)) ⟩
--           k + suc n ∷ (((suc n ↓ k) ++ n ∷ []) ++ suc (k + n) ∷ []) ++ rev r
--         ≅*⟨ ++r (rev r) (refl≡ (start+end (++-↓ n (1 + k)) refl)) ⟩
--           suc (k + n) ∷ k + n ∷ ((n ↓ k) ++ suc (k + n) ∷ []) ++ rev r
--         ≅*⟨ ++r (rev r) (long k [] []) ⟩
--           k + n ∷ suc (k + n) ∷ k + n ∷ ((n ↓ k) ++ []) ++ rev r
--         ≅*⟨ ++r (rev r) (l++ (k + n ∷ suc (k + n) ∷ k + n ∷ []) (refl≡ (++-unit))) ⟩
--           k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k) ++ rev r
--         ≅*∎
--       right* =
--         ≅*begin
--           rev (r ++ suc (k + n) ∷ n ∷ suc n ∷ (suc (suc n) ↑ k)) ++ k1 ∷ n1 ∷ []
--         ≅*⟨ ++r (k1 ∷ n1 ∷ []) right ⟩
--           k + n ∷ suc (k + n) ∷ k + n ∷ ((n ↓ k) ++ rev r) ++ k1 ∷ n1 ∷ []
--         ≅*⟨ refl≡ (++-assoc (k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k)) (rev r) (k1 ∷ n1 ∷ [])) ⟩
--           k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k) ++ rev r ++ k1 ∷ n1 ∷ []
--         ≅*∎
--   in  _ , ( (l++ (k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k)) left) , right*)
-- swap-long-lemma-rev n k n1 k1 pkn (x ∷ r) l1 (x₁ ∷ r1) p rewrite (≡-sym (cut-tail p)) =
--   let rec-m , rec-l , rec-r = swap-long-lemma-rev n k n1 k1 pkn r l1 r1 (cut-head p)
--       ll = trans (refl≡ (≡-sym (++-assoc (k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k)) (rev r) [ x ]))) (++r [ x ] rec-l)
--       rr = trans (refl≡ (≡-sym (++-assoc (rev l1) ( _ ∷ _ ∷ rev r1) [ x ]))) (++r [ x ] rec-r)
--   in  _ , (ll , rr)


-- swap-long-lemma : (n k n1 k1 : ℕ) -> (pkn : suc k1 < n1) -> (r l1 r1 : List ℕ) -> (((n ↓ (2 + k)) ++ (1 + k + n) ∷ r) ≡ (l1 ++ n1 ∷ k1 ∷ r1)) -> ∃ (λ mf -> ((((k + n) ∷ (n ↓ (2 + k)) ++ r) ≅* mf) × ((l1 ++ (k1 ∷ n1 ∷ r1))) ≅* mf))
-- swap-long-lemma n k n1 k1 pkn r l1 r1 p =
--   let pp =
--         begin
--           rev r ++ suc (k + n) ∷ n ∷ suc n ∷ (suc (suc n) ↑ k)
--         ≡⟨ start+end refl (start+end (refl {x = [ suc (k + n) ]}) (≡-sym (++-↑ n (suc k)))) ⟩
--           rev r ++ suc (k + n) ∷ n ∷ (suc n ↑ k) ++ suc (k + n) ∷ []
--         ≡⟨ start+end refl (start+end (refl {x = [ suc (k + n) ]}) (≡-sym (start+end (++-↑ n k) refl))) ⟩
--           rev r ++ suc (k + n) ∷ [] ++ ((n ↑ k) ++ [ k + n ] ) ++ suc (k + n) ∷ []
--         ≡⟨ start+end (refl {x = rev r}) (start+end (refl {x = [ suc (k + n) ]}) (++-assoc (n ↑ k) (k + n ∷ []) (suc (k + n) ∷ []))) ⟩
--           rev r ++ suc (k + n) ∷ [] ++ (n ↑ k) ++ k + n ∷ suc (k + n) ∷ []
--         ≡⟨ start+end refl (start+end (refl {x = [ suc (k + n) ]}) (start+end (≡-sym (rev-d n k)) refl)) ⟩
--           rev r ++ suc (k + n) ∷ [] ++ rev (n ↓ k) ++ k + n ∷ suc (k + n) ∷ []
--         ≡⟨ ≡-sym (++-assoc (rev r) (suc (k + n) ∷ []) (rev (n ↓ k) ++ k + n ∷ suc (k + n) ∷ [])) ⟩
--           (rev r ++ suc (k + n) ∷ []) ++ rev (n ↓ k) ++ k + n ∷ suc (k + n) ∷ []
--         ≡⟨ ≡-sym (++-assoc _ (rev (n ↓ k)) (k + n ∷ suc (k + n) ∷ [])) ⟩
--           ((rev r ++ suc (k + n) ∷ []) ++ rev (n ↓ k)) ++ k + n ∷ suc (k + n) ∷ []
--         ≡⟨ ≡-sym (start+end (rev-++ (n ↓ k) (suc (k + n) ∷ r)) refl) ⟩
--           rev ((n ↓ k) ++ suc (k + n) ∷ r) ++ k + n ∷ suc (k + n) ∷ []
--         ≡⟨ ≡-sym (++-assoc (rev ((n ↓ k) ++ suc (k + n) ∷ r)) (k + n ∷ []) (suc (k + n) ∷ []))  ⟩
--           (rev ((n ↓ k) ++ suc (k + n) ∷ r) ++ k + n ∷ []) ++ suc (k + n) ∷ []
--         ≡⟨ cong rev p ⟩
--           rev (l1 ++ n1 ∷ k1 ∷ r1)
--         ≡⟨ rev-++ l1 (n1 ∷ k1 ∷ r1) ⟩
--           ((rev r1 ++ k1 ∷ []) ++ n1 ∷ []) ++ rev l1
--         ≡⟨ ++-assoc (rev r1 ++ k1 ∷ []) (n1 ∷ []) (rev l1) ⟩
--           (rev r1 ++ k1 ∷ []) ++ n1 ∷ rev l1
--         ≡⟨ ++-assoc _ [ k1 ] _ ⟩
--           rev r1 ++ k1 ∷ n1 ∷ rev l1
--         ∎
--       call-m , call-l , call-r = swap-long-lemma-rev n k n1 k1 pkn (rev r) (rev l1) (rev r1) pp
--       ll = trans (refl≡ (start+end refl (rev-rev {r}))) call-l
--       rr = trans (refl≡ (start+end (rev-rev {l1}) (start+end refl (rev-rev {r1})))) call-r
--   in  call-m , ll , rr


ar-lemma : (k1 k2 : ℕ) -> {n1 n2 : ℕ} -> (n1 ≡ n2) -> suc (k1 + n1) ≡ suc (k2 + n2) -> k1 ≡ k2
ar-lemma k1 k2 pn p rewrite pn = ≡-down-r-+ (≡-down2 p)

dec-long-lemma-rev : (n k n1 k1 : ℕ) -> (n1 ≤ k1) -> (l r : List ℕ) -> (n ↑ k) ≡ (l ++ k1 ∷ n1 ∷ r) -> ⊥
dec-long-lemma-rev n (suc (suc k)) .(suc n) .n pkn [] .(suc (suc n) ↑ k) refl = abs-refl pkn
dec-long-lemma-rev n (suc k) n1 k1 pkn (x ∷ l) r p = dec-long-lemma-rev (suc n) k n1 k1 pkn l r (cut-head p)

dec-long-lemma-disjoint-rev : (n k n1 k1 x : ℕ) -> (n < x) -> (l r : List ℕ) -> l ++ x ∷ (n ↑ (1 + k)) ≡ (n1 ↑ (1 + k1)) ++ r
                              -> (Σ (List ℕ × List ℕ) (λ (l1 , r1) -> (l ≡ (n1 ↑ k1)) × (x ≡ n1 + k1) × (r ≡ (n ↑ (1 + k)))) ⊎
                                  Σ (List ℕ) (λ m -> (l ≡ (n1 ↑ (1 + k1)) ++ m) × (r ≡ m ++ x ∷ (n ↑ (1 + k)))))
dec-long-lemma-disjoint-rev n k n1 k1 pnx l r p = {!!}

long-long-not-disjoint : (n k n1 k1 : ℕ) -> (k + n ≡ suc (n1 + k1))
                         -> ∃ (λ mf -> ((k + n ∷ (n ↓ (2 + k)) ++ (n1 ↓ (2 + k1)) ++ (2 + (k1 + n1)) ∷ []) ≅* mf) ×
                                        (((n ↓ (2 + k)) ++ (suc (k1 + n1) ∷ (n1 ↓ (3 + k1)))) ≅* mf))
long-long-not-disjoint n zero n1 k1 p rewrite p rewrite (cong suc (+-comm n1 k1)) =
 let left = trans (cancel (_ ∷ _ ∷ []) _) (trans (long-swap-lr n1 (2 + (k1 + n1))(1 + k1) [ suc (k1 + n1) ] [ 2 + k1 + n1 ] (≤-reflexive refl)) (trans (cancel _ []) (refl≡ ++-unit)))
     right = trans (cancel [ _ ] _) (cancel [] _)
 in  _ , (left , right)
long-long-not-disjoint n (suc k) n1 k1 p with k ≤? k1 with k ≟ k1
... | yes q | yes qq rewrite qq = {!!}
  -- let left =
  --       ≅*begin
  --         suc (k + n) ∷ (2 + k + n) ∷ (n ↓ (2 + k)) ++ (n1 ↓ (2 + k1)) ++ suc (suc (k1 + n1)) ∷ []
  --       ≅*⟨ {!!} ⟩
  --         {!!}
  --       ≅*⟨ {!!} ⟩
  --         {!!}
  --       ≅*∎
  --     right =
  --       ≅*begin
  --         (n ↓ (3 + k)) ++ suc (k1 + n1) ∷ (n1 ↓ (3 + k1))
  --       ≅*⟨ short-swap-lr {n} {1 + k} [] (n1 ↓ (3 + k1)) (≤-down-+ {r = k} (≤-reflexive (≡-trans (+-comm n k) (≡-trans (≡-down2 p) (+-comm n1 k1))))) (≤-up (≤-reflexive (≡-trans (cong suc (+-comm k1 n1)) (≡-sym p)))) ⟩
  --         (k1 + n1) ∷ (n ↓ (3 + k)) ++ (n1 ↓ (3 + k1))
  --       ≅*∎
  -- in  {!!} , left , right
... | no q | yes qq = ⊥-elim (q (≤-reflexive qq))
... | no q | no qq = {!!}
... | yes q | no qq = {!!}

-- long-long-lemma-rev : (n k n1 k1 : ℕ) -> (r l1 r1 : List ℕ) -> ((r ++ (1 + k + n) ∷ (n ↑ (2 + k))) ≡ (r1 ++ (1 + k1 + n1) ∷ (n1 ↑ (2 + k1)) ++ l1))
--                       -> ∃ (λ mf -> ((((k + n) ∷ (n ↓ (2 + k)) ++ (rev r)) ≅* mf) × ((rev l1) ++ (k1 + n1) ∷ (n1 ↓ (2 + k1)) ++ (rev r1)) ≅* mf))
-- long-long-lemma-rev n k n1 k1 [] [] [] p
--   rewrite (cut-t2 p)
--   rewrite (ar-lemma k k1 (cut-t2 p) (cut-t1 p)) = _ , refl , refl
-- long-long-lemma-rev n k n1 k1 [] (x ∷ l) [] p =
--   let nn1 = (cut-t2 p)
--       kk1 = ar-lemma k k1 nn1 (cut-t1 p)
--   in ⊥-elim ([]-abs (++-empty (suc (k1 + n1) ∷ n1 ∷ suc n1 ∷ (suc (suc n1) ↑ k1)) ((x ∷ l)) (≡-trans (≡-sym p)
--     (head+tail (cut-tail p)
--     (head+tail nn1
--     (head+tail (cut-t3 p)
--     (≡-trans (cong (λ e -> (2 + e) ↑ k) nn1) (cong (λ e -> (2 + n1) ↑ e) kk1))))))))

-- long-long-lemma-rev n zero n1 k1 [] l1 (x ∷ x₁ ∷ x₂ ∷ []) ()
-- long-long-lemma-rev n zero n1 k1 [] l1 (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ r1) ()
-- long-long-lemma-rev n (suc k) n1 k1 [] l1 (x ∷ r1) p =
--   let q = cut-head p
--   in  ⊥-elim (dec-long-lemma-rev n (suc (suc (suc k))) n1 (suc (k1 + n1)) (≤-up (≤-up-+ (≤-reflexive refl))) r1 (suc n1 ∷ (suc (suc n1) ↑ k1) ++ l1) q)
-- long-long-lemma-rev n k n1 zero (x ∷ []) l1 [] p =
--   let a1 = cut-t2 p
--       a2 = cut-t3 p
--   in  abs-refl (≤-trans (≤-reflexive (≡-sym a2)) (≤-trans (≤-up (≤-up-+ (≤-reflexive refl))) (≤-reflexive a1)))
-- long-long-lemma-rev n zero .n zero (.(suc n) ∷ .n ∷ []) .(n ∷ suc n ∷ []) [] refl = _ , ((trans (cancel (n ∷ suc n ∷ []) [ suc n ]) (cancel _ [])) , (trans (cancel [ suc n ] _) (cancel [] _)))
-- long-long-lemma-rev n (suc k) .(suc (k + n)) zero (.(suc (suc (k + n))) ∷ .(suc (k + n)) ∷ []) .(n ∷ suc n ∷ suc (suc n) ∷ (suc (suc (suc n)) ↑ k)) [] refl =
--   let left =
--         ≅*begin
--           suc (k + n) ∷ (n ↓ (3 + k)) ++ suc (k + n) ∷ (2 + (k + n)) ∷ []
--         ≅*⟨ short-swap-lr {n = n} {k = 1 + k} [ suc (k + n) ] [ 2 + (k + n) ] (≤-up-+ (≤-reflexive refl)) (≤-up (≤-reflexive refl)) ⟩
--           suc (k + n) ∷ k + n ∷ (n ↓ (3 + k)) ++ suc (suc (k + n)) ∷ []
--         ≅*⟨ short-swap-l {n = n} {k = 1 + k} (suc (k + n) ∷ k + n ∷ []) (≤-up (≤-up-+ (≤-reflexive refl))) (≤-reflexive refl) ⟩
--           suc (k + n) ∷ k + n ∷ suc (k + n) ∷ (n ↓ (3 + k))
--         ≅*⟨ braid [] _ ⟩
--           k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ (3 + k))
--         ≅*∎
--       right =
--         ≅*begin
--           (((rev (suc (suc (suc n)) ↑ k) ++ suc (suc n) ∷ []) ++ suc n ∷ []) ++ n ∷ []) ++ suc (k + n) ∷ suc (suc (k + n)) ∷ suc (k + n) ∷ []
--         ≅*⟨ ++r (suc (k + n) ∷ suc (suc (k + n)) ∷ suc (k + n) ∷ []) (refl≡ (telescope-rev (suc n) k (n ∷ []))) ⟩
--           _
--         ≅*⟨ ++r (suc (k + n) ∷ suc (suc (k + n)) ∷ suc (k + n) ∷ []) (refl≡ (++-↓ n (suc (suc k)))) ⟩
--           (n ↓ (3 + k)) ++ suc (k + n) ∷ suc (suc (k + n)) ∷ suc (k + n) ∷ []
--         ≅*⟨ short-swap-lr {n} {1 + k} [] (_ ∷ _ ∷ []) (≤-up-+ (≤-reflexive refl)) (≤-up (≤-reflexive refl))  ⟩
--           k + n ∷ (n ↓ (3 + k)) ++ suc (suc (k + n)) ∷ suc (k + n) ∷ []
--         ≅*⟨ short-swap-lr {n} {1 + k} [ _ ] [ _ ] ((≤-up-+ (≤-reflexive refl))) (≤-reflexive refl) ⟩
--           _
--         ≅*⟨ short-swap-l (_ ∷ _ ∷ []) (≤-up-+ (≤-reflexive refl)) (≤-up (≤-reflexive refl)) ⟩
--           k + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ (3 + k))
--         ≅*∎
--   in  _ , (left , right)
-- long-long-lemma-rev n k n1 zero (.(suc n1) ∷ .n1 ∷ .(suc n1) ∷ r) .(r ++ suc (k + n) ∷ n ∷ suc n ∷ (suc (suc n) ↑ k)) [] refl =
--   let left =
--         ≅*begin
--           k + n ∷ (n ↓ (2 + k)) ++ ((rev r ++ suc n1 ∷ []) ++ n1 ∷ []) ++ suc n1 ∷ []
--         ≅*⟨ l++ (k + n ∷ (n ↓ (2 + k))) (refl≡ (≡-trans (++-assoc _ [ n1 ] [ suc n1 ]) (++-assoc _ [ suc n1 ] (n1 ∷ [ suc n1 ])))) ⟩
--           k + n ∷ (n ↓ (2 + k)) ++ rev r ++ suc n1 ∷ n1 ∷ suc n1 ∷ []
--         ≅*⟨ l++ (k + n ∷ (n ↓ (2 + k))) (braid (rev r) []) ⟩
--           k + n ∷ (n ↓ (2 + k)) ++ rev r ++ n1 ∷ suc n1 ∷ n1 ∷ []
--         ≅*∎
--       right =
--         ≅*begin
--           rev (r ++ suc (k + n) ∷ (n ↑ (2 + k)))
--         ≅*⟨ refl≡ (rev-++ r _) ⟩
--           rev (suc (k + n) ∷ (n ↑ (2 + k))) ++ (rev r)
--         ≅*⟨ ++r (rev r) (refl≡ (start+end (rev-u n (suc (suc k))) (refl {x = [ suc (k + n) ]}))) ⟩
--           ((n ↓ (2 + k)) ++ [ suc (k + n) ]) ++ (rev r)
--         ≅*⟨ ++r (rev r) (short-swap-l [] (≤-up-+ (≤-reflexive refl)) (≤-reflexive refl)) ⟩
--           k + n ∷ (n ↓ (2 + k)) ++ rev r
--         ≅*∎
--   in  _ , (left , trans (++r (n1 ∷ suc n1 ∷ n1 ∷ []) right) (refl≡ (++-assoc (k + n ∷ (n ↓ (2 + k))) (rev r) _)))
-- long-long-lemma-rev n k n1 (suc k1) (x ∷ r) l1 [] p with (dec-long-lemma-disjoint-rev n (1 + k) n1 (2 + k1) (suc (k + n)) (s≤s (≤-up-+ (≤-reflexive refl))) r l1 (cut-head p))
-- long-long-lemma-rev n k n1 (suc k1) (x ∷ r) l [] p | inj₁ ((l1 , r1) , l1p , xp , r1p) rewrite (cut-t1 p) rewrite l1p rewrite r1p =
--   let xpp = ≡-down2 (≡-trans xp (+-three-assoc {n1} {1} {1 + k1}))
--       left =
--         ≅*begin
--           _
--         ≅*⟨ l++ (k + n ∷ (n ↓ (2 + k))) (refl≡ (telescope-rev n1 k1 [ 2 + (k1 + n1) ])) ⟩
--           k + n ∷ (n ↓ (2 + k)) ++ (n1 ↓ (2 + k1)) ++ (2 + (k1 + n1)) ∷ []
--         ≅*∎
--       right =
--         ≅*begin
--           ((rev (suc (suc n) ↑ k) ++ suc n ∷ []) ++ n ∷ []) ++ (suc (k1 + n1) ∷ (n1 ↓ (3 + k1)) ++ [])
--         ≅*⟨ refl≡ (telescope-rev n k ((suc (k1 + n1) ∷ (n1 ↓ (3 + k1)) ++ []))) ⟩
--           (n ↓ (2 + k)) ++ (suc (k1 + n1) ∷ (n1 ↓ (3 + k1)) ++ [])
--         ≅*⟨ l++ (n ↓ (2 + k)) (refl≡ (++-unit)) ⟩
--           (n ↓ (2 + k)) ++ (suc (k1 + n1) ∷ (n1 ↓ (3 + k1)))
--         ≅*∎
--       rec-m , rec-l , rec-r  = long-long-not-disjoint n k n1 k1 (≡-trans xpp (+-three-assoc {n1} {1} {k1}))
--   in rec-m , (trans left rec-l , trans right rec-r)
-- long-long-lemma-rev n k n1 (suc k1) (x ∷ r) l [] p | inj₂ (m , lmp , mrp) rewrite (cut-t1 p) rewrite lmp rewrite mrp rewrite (rev-++ ((suc (suc (suc n1)) ↑ k1)) m) =  -- disjoint
--   let left =
--         ≅*begin
--           (((((rev m) ++ (rev ((suc (suc (suc n1)) ↑ k1)))) ++ suc (suc n1) ∷ []) ++ suc n1 ∷ []) ++ n1 ∷ []) ++ suc (suc (k1 + n1)) ∷ []
--         ≅*⟨ refl≡ (telescope-l-rev-+1 n1 k1 (rev m) [ 2 + k1 + n1 ]) ⟩
--           rev m ++ (n1 ↓ (3 + k1)) ++ (2 + k1 + n1) ∷ []
--         ≅*⟨ long (1 + k1) (rev m) [] ⟩
--           _
--         ≅*⟨ l++ (rev m) (refl≡ ++-unit) ⟩
--           rev m ++ (1 + k1 + n1) ∷ (n1 ↓ (3 + k1))
--         ≅*∎
--       right =
--         ≅*begin
--           rev (m ++ suc (k + n) ∷ n ∷ suc n ∷ (suc (suc n) ↑ k)) ++ suc (k1 + n1) ∷ suc (suc (k1 + n1)) ∷ suc (k1 + n1) ∷ k1 + n1 ∷ (n1 ↓ k1) ++ []
--         ≅*⟨ ++r _ (refl≡ (rev-++ m _)) ⟩
--           ((((rev (suc (suc n) ↑ k) ++ suc n ∷ []) ++ n ∷ []) ++ suc (k + n) ∷ []) ++ rev m) ++ suc (k1 + n1) ∷ (n1 ↓ (3 + k1)) ++ []
--         ≅*⟨ refl≡ (++-assoc _ (rev m) (suc (k1 + n1) ∷ (n1 ↓ (3 + k1)) ++ [])) ⟩
--           _
--         ≅*⟨ refl≡ (start+end (telescope-rev n k [ suc (k + n) ]) refl) ⟩
--           _
--         ≅*⟨ l++ (((n ↓ (2 + k)) ++ suc (k + n) ∷ [])) (l++ (rev m) (refl≡ ++-unit)) ⟩
--           _
--         ≅*⟨ ++r ((rev m) ++ suc (k1 + n1) ∷ (n1 ↓ (3 + k1))) (short-swap-l {n} {k} [] (≤-up-+ {r = k} (≤-reflexive refl)) (≤-reflexive refl))  ⟩
--           _
--         ≅*∎
--   in   _ , (l++ (k + n ∷ (n ↓ (2 + k))) left , right)
-- long-long-lemma-rev n k n1 k1 (x₁ ∷ r) l1 (x ∷ r1) p rewrite cut-tail p =
--   let rec-m , rec-l , rec-r = long-long-lemma-rev n k n1 k1 r l1 r1 (cut-head p)
--   in  rec-m ++ [ x ] , (trans (refl≡ (≡-sym (++-assoc _ (rev r) [ x ]))) (++r [ x ] rec-l) ,
--                        (trans (refl≡ (≡-sym
--                            (≡-trans (++-assoc (rev l1)  _   (x ∷ []))
--                            (≡-trans (cong (λ e -> rev l1 ++ k1 + n1 ∷ suc (k1 + n1) ∷ k1 + n1 ∷ [] ++ e)
--                                      (++-assoc (n1 ↓ k1) (rev r1) (x ∷ []))) refl)))) (++r [ x ] rec-r)))

-- long-long-lemma : (n k n1 k1 : ℕ) -> (r l1 r1 : List ℕ) -> (((n ↓ (2 + k)) ++ (1 + k + n) ∷ r) ≡ (l1 ++ (n1 ↓ (2 + k1)) ++ (1 + k1 + n1) ∷ r1)) -> ∃ (λ mf -> ((((k + n) ∷ (n ↓ (2 + k)) ++ r) ≅* mf) × (l1 ++ (k1 + n1) ∷ (n1 ↓ (2 + k1)) ++ r1) ≅* mf))
-- long-long-lemma n k n1 k1 r l1 r1 p = {!   !}
