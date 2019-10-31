{-# OPTIONS --without-K #-}
module SwapLemmas where

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
open import Lists
open import Compact
open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to ≤∎) hiding (_≡⟨_⟩_; _≡⟨⟩_)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)

open ≅*-Reasoning

long-swap : (n1 n2 : ℕ) -> (k : ℕ) -> (k + n1 < n2) -> (n2 ∷ (n1 ↓ k)) ≅* ((n1 ↓ k) ++ [ n2 ])
long-swap n1 n2 zero p = refl
long-swap n1 n2 (suc k) p =
  let rec = long-swap n1 n2 k (≤-down p)
  in  trans (swap p [] _) (l++ [ k + n1 ] rec)

long-swap< : (n1 n2 : ℕ) -> (k : ℕ) -> (suc n1 < n2) -> ((n2 ↓ k) ++ [ n1 ]) ≅* (n1 ∷ (n2 ↓ k))
long-swap< n1 n2 zero p = refl
long-swap< n1 n2 (suc k) p =
  let rec = long-swap< n1 n2 k p
  in  trans (l++ (k + n2 ∷ []) rec) (swap (≤-up-+ p) [] _)

long-swap-lr : (n1 n2 k : ℕ) -> (l r : List ℕ) -> (k + n1 < n2) -> (l ++ (n2 ∷ (n1 ↓ k)) ++ r) ≅* (l ++ (n1 ↓ k) ++ n2 ∷ r)
long-swap-lr n1 n2 k l r p =
  let lemma = (++r r (long-swap n1 n2 k p))
  in  l++ l (trans lemma (refl≡ (++-assoc _ [ _ ] r)))

long-swap<-lr : (n1 n2 k : ℕ) -> (l r : List ℕ) -> (suc n1 < n2) -> (l ++ (n2 ↓ k) ++ n1 ∷ r) ≅* (l ++ n1 ∷ (n2 ↓ k) ++ r)
long-swap<-lr n1 n2 k l r p =
  let lemma = (++r r (long-swap< n1 n2 k p))
  in  l++ l (trans (refl≡ (≡-sym (++-assoc (n2 ↓ k) (n1 ∷ []) r))) lemma)

short-swap : {n k t tl tr : ℕ} -> (tr + n ≡ t) -> ((tl + suc t) ≡ suc (k + n)) -> (n ↓ (2 + k) ++ [ suc t ]) ≅* (t ∷ (n ↓ (2 + k)))
short-swap {n} {k} {t} {tl} {tr} ptn ptkn rewrite (≡-sym ptn) =
  let pp = ≡-down-r-+ {r = n} (≡-trans (+-assoc tl (1 + tr) n) (≡-trans ptkn (≡-sym (+-assoc 1 k n))))
      k=tl+tr : 2 + k ≡ tl + (2 + tr)
      k=tl+tr = ≡-trans (≡-sym (cong suc pp)) (≡-sym (+-three-assoc {tl} {1} {1 + tr}))

      lemma : n ↓ (2 + k) ≡ (n + (2 + tr)) ↓ tl ++ (n ↓ (2 + tr))
      lemma = ≡-trans (cong (λ e -> n ↓ e) k=tl+tr) (↓-+ n tl (2 + tr))

      red =
        ≅*begin
          suc (k + n) ∷ k + n ∷ (n ↓ k) ++ suc (tr + n) ∷ []
        ≅*⟨ refl≡ (start+end lemma refl) ⟩
          (((n + (2 + tr)) ↓ tl) ++ (n ↓ (2 + tr))) ++ suc (tr + n) ∷ []
        ≅*⟨ refl≡ (++-assoc ((n + suc (suc tr)) ↓ tl) _ (suc (tr + n) ∷ []) ) ⟩
          ((n + (2 + tr)) ↓ tl) ++ (n ↓ (2 + tr)) ++ suc (tr + n) ∷ []
        ≅*⟨ long _ (((n + (2 + tr)) ↓ tl)) [] ⟩
          ((n + (2 + tr)) ↓ tl) ++ (tr + n) ∷ (n ↓ (2 + tr)) ++ []
        ≅*⟨ long-swap<-lr (tr + n) (n + (2 + tr)) tl [] (suc (tr + n) ∷ tr + n ∷ (n ↓ tr) ++ []) (≤-reflexive (≡-trans (≡-sym (+-assoc 2 tr n)) (+-comm (suc (suc tr)) n))) ⟩
          (tr + n) ∷ ((n + (2 + tr)) ↓ tl) ++ (n ↓ (2 + tr)) ++ []
        ≅*⟨ refl≡ (start+end (refl {x = (tr + n) ∷ ((n + (2 + tr)) ↓ tl)}) (++-unit {(n ↓ (2 + tr))})) ⟩
          (tr + n) ∷ ((n + (2 + tr)) ↓ tl) ++ (n ↓ (2 + tr))
        ≅*⟨ refl≡ (head+tail refl (≡-sym (↓-+ n tl (2 + tr)))) ⟩
          tr + n ∷ (n ↓ (tl + suc (suc tr)))
        ≅*⟨ refl≡ (head+tail refl (cong (λ e -> n ↓ e) (≡-sym k=tl+tr))) ⟩
          tr + n ∷ suc (k + n) ∷ k + n ∷ (n ↓ k)
        ≅*∎
  in  red

short-swap-l : {n k t : ℕ} -> (l : List ℕ) -> (n ≤ t) -> (suc t ≤ suc (k + n)) -> (l ++ n ↓ (2 + k) ++ [ suc t ]) ≅* (l ++ t ∷ (n ↓ (2 + k)))
short-swap-l {n} {k} {t} l pnt ptkn =
  let tr , tr-p = ≤-∃ n t pnt
      tl , tl-p = ≤-∃ (suc t) (suc k + n) ptkn
      lemma = (short-swap {n} {k} {t} {tl} {tr} tr-p tl-p)
  in  l++ l lemma

short-swap-lr : {n k t : ℕ} -> (l r : List ℕ) -> (n ≤ t) -> (suc t ≤ suc (k + n)) -> ((l ++ n ↓ (2 + k)) ++ suc t ∷ r) ≅* ((l ++ t ∷ (n ↓ (2 + k))) ++ r)
short-swap-lr {n} {k} {t} l r pnt ptkn =
  let tr , tr-p = ≤-∃ n t pnt
      tl , tl-p = ≤-∃ (suc t) (suc k + n) ptkn
      lemma = ++r r (l++ l (short-swap {n} {k} {t} {tl} {tr} tr-p tl-p))
  in  trans (refl≡ (≡-sym (≡-trans (start+end (≡-sym (++-assoc l _ [ _ ])) (refl {x = r})) (++-assoc _ [ _ ] r)))) lemma

long->-long : (n k n1 k1 : ℕ) -> (k + n ≡ suc (k1 + n1)) -> (k1 < k) -> ((n ↓ (2 + k)) ++ ((1 + n1) ↓ (2 + k1))) ≅* ((n1 ↓ (2 + k1)) ++ (n ↓ (2 + k)))
long->-long n zero n1 k1 pp ()
long->-long n (suc k) n1 zero pp pk rewrite (≡-sym pp)  =
  ≅*begin
    (n ↓ (3 + k)) ++ (2 + (k + n)) ∷ (1 + (k + n)) ∷ []
  ≅*⟨ long (1 + k) [] [ _ ] ⟩
    (1 + (k + n)) ∷ (n ↓ (3 + k)) ++ (1 + (k + n)) ∷ []
  ≅*⟨ short-swap-lr {n = n} {k = (1 + k)} [ _ ] [] (≤-up-+ (≤-reflexive refl)) (≤-up (≤-reflexive refl)) ⟩
    _
  ≅*⟨ refl≡ ++-unit ⟩
    _
  ≅*⟨ refl≡ (head+tail refl (head+tail (≡-down2 pp) refl)) ⟩
    _
  ≅*∎
long->-long n (suc k) n1 (suc k1) pp pk =
  let rec = long->-long n k n1 k1 (≡-down2 pp) (≤-down2 pk)
  in
    ≅*begin
      (n ↓ (3 + k)) ++ ((1 + n1) ↓ (3 + k1))
    ≅*⟨ short-swap-lr {n = n} {k = (1 + k)} [] (((1 + n1) ↓ (2 + k1))) (≤-trans (≤-trans (≤-up (≤-up-+ rrr)) (≤-reflexive pp)) (≤-reflexive (≡-sym (+-three-assoc {1 + k1} {1} {_})))) (≤-reflexive (cong suc (≡-trans (+-three-assoc {1 + k1} {1} {_}) (≡-sym pp)))) ⟩
      _ ∷ _ ∷ (n ↓ (2 + k)) ++ ((1 + n1) ↓ (2 + k1))
    ≅*⟨ l++ (_ ∷ _ ∷ []) rec ⟩
      _ ∷ _ ∷ (n1 ↓ (2 + k1)) ++ (n ↓ (2 + k))
    ≅*⟨ long-swap-lr n1 (suc (suc (k + n))) (suc (suc k1)) [ _ ] ((n ↓ (2 + k))) (≤-reflexive (cong suc (≡-sym pp))) ⟩
      _ ∷ (n1 ↓ (2 + k1)) ++ _ ∷ (n ↓ (2 + k))
    ≅*⟨ refl≡ (head+tail (+-three-assoc {1 + k1} {1} {n1}) refl) ⟩
      (n1 ↓ (3 + k1)) ++ (n ↓ (3 + k))
    ≅*∎

long-≤-long : (n k n1 k1 : ℕ) -> (k + n ≡ k1 + n1) -> (k ≤ k1) -> ((n ↓ (2 + k)) ++ (n1 ↓ (2 + k1))) ≅* ((n1 ↓ (1 + k1)) ++ ((1 + n) ↓ (1 + k)))
long-≤-long n zero n1 k1 pp pk rewrite pp rewrite (+-three-assoc {k1} {1} {n1}) =
  ≅*begin
    _
  ≅*⟨ braid [] _ ⟩
    _
  ≅*⟨ cancel (_ ∷ _ ∷ [])  _ ⟩
    _
  ≅*⟨ refl≡ (≡-sym (++-unit)) ⟩
    _
  ≅*⟨ long-swap-lr n1 (1 + k1 + n1) k1 [ _ ] [] (≤-reflexive refl) ⟩
    _
  ≅*∎
long-≤-long n (suc k) n1 zero pp ()
long-≤-long n (suc k) n1 (suc k1) pp pk =
  let rec = long-≤-long n k n1 k1 (≡-down2 pp) (≤-down2 pk)
      lemma = (≡-sym (cong (λ e -> 2 + e) (≡-trans (+-three-assoc {k} {1} {n}) (≡-trans pp (≡-sym (+-three-assoc {k1} {1} {n1}))))))
  in
    ≅*begin
      (n ↓ (3 + k)) ++ 2 + k1 + n1 ∷ (n1 ↓ (2 + k1))
    ≅*⟨ short-swap-lr {n = n} [] ((n1 ↓ (2 + k1))) (≤-trans (≤-up (≤-up-+ (≤-reflexive refl))) (≤-reflexive pp)) (s≤s (≤-reflexive (≡-sym pp))) ⟩
       1 + k1 + n1 ∷ (2 + k + n) ∷ (n ↓ (2 + k)) ++ (n1 ↓ (2 + k1))
    ≅*⟨ refl≡ (++-assoc (_ ∷ _ ∷ []) ((n ↓ (2 + k))) _) ⟩
      1 + k1 + n1 ∷ (2 + k + n) ∷ [] ++ (((n ↓ (2 + k)) ++ (n1 ↓ (2 + k1))))
    ≅*⟨ l++ (_ ∷ _ ∷ []) rec ⟩
      1 + k1 + n1 ∷ (2 + k + n) ∷ [] ++ (((n1 ↓ (1 + k1)) ++ ((1 + n) ↓ (1 + k))))
    ≅*⟨ refl≡ (≡-sym (++-assoc (_ ∷ _ ∷ []) (n1 ↓ (1 + k1)) _)) ⟩
      _
    ≅*⟨ long-swap-lr n1 (suc (suc (k + n))) (suc k1) [ _ ] ((1 + n) ↓ (1 + k)) (≤-reflexive (cong suc (≡-sym pp))) ⟩
      1 + k1 + n1 ∷ (n1 ↓ (1 + k1)) ++ (2 + k + n) ∷ ((1 + n) ↓ (1 + k))
    ≅*⟨ refl≡ (start+end (refl {x = 1 + k1 + n1 ∷ (n1 ↓ (1 + k1))})  (head+tail (≡-sym (+-three-assoc {1 + k} {1} {n})) refl)) ⟩
      _
    ≅*∎
