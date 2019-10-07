{-# OPTIONS --allow-unsolved-metas #-}

module Canonization where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; Σ; _×_; _,_; _,′_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)

open import General
open import Relation.Nullary
open import Data.Empty
open Relation.Binary.PropositionalEquality.≡-Reasoning

variable
    n : ℕ
    l : List ℕ

data _≃_ : List ℕ -> List ℕ -> Set where
    cancel : (n ∷ n ∷ []) ≃ []
    swap : {k : ℕ} -> (suc k < n) -> (n ∷ k ∷ []) ≃ (k ∷ n ∷ [])
    braid : (n ∷ (suc n) ∷ n ∷ []) ≃ ((suc n) ∷ n ∷ (suc n) ∷ [])
    prepend : (k : ℕ) -> {l l' : List ℕ} -> (l ≃ l') -> (k ∷ l) ≃ (k ∷ l')
    ++-respects : {l l' m m' : List ℕ} -> (l ≃ l') -> (m ≃ m') -> (l ++ m) ≃ (l' ++ m')
    refl : {l : List ℕ} -> l ≃ l
    comm : {l l' : List ℕ} -> (l ≃ l') -> l' ≃ l
    trans : {l l' l'' : List ℕ} -> (l ≃ l') -> (l' ≃ l'') -> l ≃ l''

module ≃-Reasoning where
    infix  1 ≃begin_
    infixr 2 _≃⟨⟩_ _≃⟨_⟩_
    infix  3 _≃∎

    ≃begin_ : ∀ {x y : List ℕ}
             → x ≃ y
               -----
             → x ≃ y
    ≃begin x≃y  =  x≃y

    _≃⟨⟩_ : ∀ (x : List ℕ) {y : List ℕ}
            → x ≃ y
              -----
            → x ≃ y
    x ≃⟨⟩ x≃y  =  x≃y

    _≃⟨_⟩_ : ∀ (x : List ℕ) {y z : List ℕ}
             → x ≃ y
             → y ≃ z
               -----
             → x ≃ z
    x ≃⟨ x≃y ⟩ y≃z  =  trans x≃y y≃z

    _≃∎ : ∀ (x : List ℕ)
           -----
          → x ≃ x
    x ≃∎  =  refl

open ≃-Reasoning


refl≡ : {l l' : List ℕ} -> (l ≡ l') -> l ≃ l'
refl≡ refl = refl

_↓_ : (n : ℕ) -> (r : ℕ) -> List ℕ
zero ↓ r = []
suc n ↓ zero = []
suc n ↓ suc r = n ∷ n ↓ r

↓-rec : {n k : ℕ} -> (k < n) -> (n ↓ suc k) ≡ (n ↓ k) ++ [ n ∸ (k + 1) ]
↓-rec {suc zero} {zero} (s≤s z≤n) = refl
↓-rec {suc (suc n)} {zero} (s≤s z≤n) = refl
↓-rec {suc (suc n)} {suc k} (s≤s p) = cong (λ l -> suc n ∷ l) (↓-rec p)

≤-up : {n m : ℕ} -> m ≤ n -> m ≤ suc n
≤-up {n} {.0} z≤n = z≤n
≤-up {.(suc _)} {.(suc _)} (s≤s q) = s≤s (≤-up q)

≤-down : {n m : ℕ} -> suc m ≤ n -> m ≤ n
≤-down {.(suc _)} {zero} (s≤s p) = z≤n
≤-down {.(suc _)} {suc n} (s≤s p) = s≤s (≤-down p)

≤-down2 : {n m : ℕ} -> suc m ≤ suc n -> m ≤ n
≤-down2 {m} {n} (s≤s p) = p

≤-abs : {A : Set} -> {n : ℕ} -> (suc n ≤ 0) -> A
≤-abs ()

open Σ

postulate
    ∸-implies-≤ : {p q r : ℕ} -> (p ≡ q ∸ r) -> (p ≤ q)
    ≤-remove-+ : {p q r : ℕ} -> (p + q ≤ r) -> (q ≤ r)
    ≡-down2 : (p q : ℕ) -> suc p ≡ suc q -> p ≡ q

nnl=l : {l : List ℕ} -> {n : ℕ} -> (n ∷ n ∷ l) ≃ l
nnl=l = ++-respects cancel refl
l++nn=l : {l : List ℕ} -> {n : ℕ} -> (l ++ (n ∷ n ∷ [])) ≃ l
l++nn=l = trans (++-respects refl cancel) {!!}

canonize-p< : (n r1 r2 : ℕ)
              -> {i : ℕ}
              -> ((suc zero) ≤ r2)
              -> ((r1 + r2) < n)
              -> {i ≡ n ∸ (2 + r1 + r2)}
              -> ((n ↓ r1) ++ [ i ]) ≃ (i ∷ (n ↓ r1))

canonize-p< (suc n) zero r2 {i} pr2 pinr = refl
canonize-p< (suc zero) (suc zero) r2 {zero} pr2 pinr = refl
canonize-p< (suc zero) (suc (suc r1)) r2 {zero} pr2 pinr = refl
canonize-p< (suc (suc zero)) (suc zero) (suc r2) {i} pr2 (s≤s (s≤s ())) {pinr}
canonize-p< (suc (suc zero)) (suc (suc r1)) (suc r2) {i} pr2 (s≤s (s≤s prn)) {pinr} = ≤-abs prn
canonize-p< (suc (suc (suc zero))) (suc (suc r1)) (suc r2) {i} pr2 (s≤s (s≤s (s≤s prn))) {pinr} = ≤-abs (≤-remove-+ prn)

canonize-p< (suc (suc (suc zero))) (suc zero) (suc r2) {i} pr2 prn {pinr} rewrite pinr = swap (s≤s (s≤s z≤n)) -- base case
canonize-p< (suc (suc (suc (suc n)))) (suc zero) (suc r2) {i} pr2 prn {pinr} rewrite pinr =
  let tt = ∸-implies-≤ {r = r2} (_≡_.refl {x = n ∸ r2})
  in swap (s≤s (s≤s (≤-trans tt (≤-up (≤-reflexive refl)))))
canonize-p< (suc (suc (suc (suc n)))) (suc (suc r1)) (suc r2) {i} pr2 (s≤s prn) {pinr} =
  let rec = prepend (3 + n) (canonize-p< (suc (suc (suc n))) (suc r1) (suc r2) {i} pr2 prn {pinr})

      i≤1+n : i ≤ (suc n)
      i≤1+n = ≤-trans (∸-implies-≤ {_} {_} {r = r1 + suc r2} pinr) ((≤-up (≤-reflexive refl)))

      lemma =
        ≃begin
          (3 + n) ∷ (2 + n) ∷ ((2 + n) ↓ r1) ++ i ∷ []
        ≃⟨ rec ⟩
          (3 + n) ∷ (i ∷ (2 + n) ∷ ((2 + n) ↓ r1))
        ≃⟨ ++-respects (swap (s≤s (s≤s i≤1+n))) refl ⟩
          i ∷ (3 + n) ∷ (2 + n) ∷ ((2 + n) ↓ r1)
        ≃∎
  in lemma

-- REMEMBER - i is (suc i)
canonize-p> : (n r1 r2 : ℕ)
              -> {i : ℕ}
              -> ((suc (suc zero)) ≤ r2)
              -> (r1 + r2 < n)
              -> {i ≡ n ∸ (2 + r1)}
--              -> ((n ↓ (r2 + r1)) ++ [ suc i ]) ≃ (i ∷ n ↓ (r1 + r2))
              -> (((n ↓ r1) ++ [ 1 + i ] ++ (1 + i) ↓ r2) ++ [ 1 + i ]) ≃ (i ∷ (n ↓ (1 + r1 + r2)))
canonize-p> (suc zero) r1 (suc r2) {i} pr2 prn = ≤-abs (≤-remove-+ {r1} (≤-down2 prn))
canonize-p> (suc (suc zero)) r1 (suc zero) {i} (s≤s ()) prn
canonize-p> (suc (suc zero)) zero (suc (suc zero)) {i} pr2 prn {pinr} rewrite pinr = comm braid -- base case
canonize-p> (suc (suc zero)) (suc r1) (suc (suc zero)) {i} pr2 (s≤s (s≤s prn)) = ≤-abs (≤-remove-+ {r1} prn)
canonize-p> (suc (suc zero)) r1 (suc (suc (suc r2))) {i} pr2 (s≤s prn) = ≤-abs (≤-down2 (≤-remove-+ {r1} prn))

canonize-p> (suc (suc (suc n))) zero (suc zero) {i} (s≤s ()) prn {pinr}
canonize-p> (suc (suc (suc n))) zero (suc (suc zero)) {i} pr2 prn {pinr} = {!!}

canonize-p> (suc (suc (suc n))) zero (suc (suc (suc r2))) {suc i} pr2 (s≤s prn) {pinr} rewrite (≡-down2 i n pinr) =
  let reci = canonize-p> (suc (suc n)) zero (suc (suc r2)) {i} (s≤s (s≤s z≤n)) prn {≡-down2 i n pinr}
      recn = subst (λ k -> (suc k ∷ k ∷ (k ↓ suc r2) ++ [ suc k ]) ≃ (k ∷ suc n ∷ n ∷ (n ↓ suc r2))) ((≡-down2 i n pinr)) reci
  in  {!!}
canonize-p> (suc (suc (suc n))) (suc r1) (suc zero) {i} (s≤s ()) prn --
canonize-p> (suc (suc (suc n))) (suc r1) (suc (suc r2)) {i} pr2 prn = {!!}

-- -- canonize-p> (suc (suc n)) (suc zero) (suc (suc zero)) {i} pr1 pr2 prrn {pinr} rewrite pinr =
-- --   trans (nnl=l {0 ∷ 1 ∷ []}) (comm {!!})
-- canonize-p> (suc (suc (suc n))) (suc zero) (suc (suc zero)) {i} pr1 pr2 prrn {pinr} rewrite pinr =
--   let x : ((2 +  n) ∷ 1 + n ∷ n ∷ 1 + n ∷ []) ≃ ((2 + n) ∷ n ∷ 1 + n ∷ n ∷ [])
--       x = prepend (2 + n) (comm (braid {n}))
--       y : {l : List ℕ} -> ((2 + n) ∷ n ∷ l) ≃ (n ∷ (2 + n) ∷ l)
--       y = ++-respects (swap n<1+n) refl
--   in trans {!!} {!!}
-- canonize-p> (suc (suc (suc n))) (suc (suc r1)) (suc (suc zero)) {i} pr1 pr2 (s≤s prrn) {pinr} =
--   let x = prepend (suc (suc n)) (canonize-p> (suc (suc n)) (suc r1) (suc zero) {i} ({!!}) pr2 (prrn) {pinr})
--       y : (suc (suc n) ∷ [ i ]) ≃ (i ∷ [ suc (suc n) ])
--       y = swap (s≤s (s≤s (∸-implies-≤ {i} {n} {suc r1} {!!})))
--       z = ++-respects y (refl { (suc n) ∷ ((suc n) ↓ suc (r1 + 1))})
--   in trans x z

-- canonize-p> (suc (suc zero)) (suc r1) (suc (suc r2)) {i} pr1 pr2 (s≤s prrn) {pirn} =
--   let t = ≤-down2 (≤-remove-+ {r1} {suc (suc r2)} {1} (≤-down {!!}))
--   in  ≤-abs t
-- canonize-p> (suc (suc (suc n))) (suc r1) (suc (suc r2)) {i} pr1 pr2 prrn {pirn} =
--   let r1<n : r1 < n
--       r1<n = {!!}
--       r2<i : r2 < i
--       r2<i = {!!}
--       tt = ↓-rec r2<i
-- --      tt2 = cong (λ l -> (suc (suc n) ∷ ((suc (suc n) ↓ r1) ++ suc i ∷ i ∷ l) ++ [ suc i ])) tt
--       goal :  (((i ↓ suc r2)) ++ [ suc i ]) ≃ (suc n ↓ (r1 + suc (suc r2)))
--       goal = {!!}
--       x = canonize-p> (3 + n) (1 + r1) (1 + r2) {i} pr1 (s≤s {!!}) (s≤s {!!}) {pirn}
--   in  {!!}

postulate
  F-canonize-p> : (n r i : ℕ)
                -> (r ≤ n)
                -> ((suc i) ≤ n)
                -> ((suc i) + r > n)
                -> ((n ↓ r) ++ [ suc i ]) ≃ (i ∷ n ↓ r)
  F-canonize-p≡ : (n r i : ℕ)
                  -> (r ≤ n)
                  -> ((suc i) < n)
                  -> (((suc i) + 1 + r) ≡ n)
                  -> ((n ↓ r) ++ [ suc i ]) ≃ (n ↓ (1 + r))
  F-canonize-p< : (n r i : ℕ)
                  -> (r ≤ n)
                  -> ((suc i) < n)
                  -> ((suc i) + (1 + r) < n)
                  -> ((n ↓ r) ++ [ suc i ]) ≃ ((suc i) ∷ n ↓ r)
