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

open ≤-Reasoning renaming (_∎ to _≤∎; begin_ to begin-≤_) hiding (_≡⟨_⟩_)


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
    +-three-assoc : {k i r : ℕ} -> k + i + r ≡ i + k + r
    ++-unit : l ++ [] ≡ l
    ∸-with-≡ : {p q r : ℕ} -> (r ≤ q) -> (p + r ≡ q) -> (p ≡ q ∸ r)

∸-up : {n r : ℕ} -> (r < n) -> (n ∸ r) ≡ suc (n ∸ (suc r))
∸-up {suc zero} {zero} p = refl
∸-up {suc zero} {suc r} (s≤s p) = ≤-abs p
∸-up {suc (suc n)} {zero} p = refl
∸-up {suc (suc n)} {suc r} (s≤s p) = ∸-up {suc n} {r} p

nnl=l : {l : List ℕ} -> {n : ℕ} -> (n ∷ n ∷ l) ≃ l
nnl=l = ++-respects cancel refl
l++nn=l : {l : List ℕ} -> {n : ℕ} -> (l ++ (n ∷ n ∷ [])) ≃ l
l++nn=l = trans (++-respects refl cancel) (refl≡ ++-unit)

canonize-p< : (n r1 r2 : ℕ)
              -> {i : ℕ}
              -> ((suc zero) ≤ r2)
              -> ((r1 + r2) < n)
              -> {i ≡ n ∸ (2 + r1 + r2)}
              -> ((n ↓ r1) ++ [ i ]) ≃ (i ∷ (n ↓ r1))
-- unfortunately, we have to weed out some impossible cases
canonize-p< (suc n) zero r2 {i} pr2 pinr = refl
canonize-p< (suc zero) (suc zero) r2 {zero} pr2 pinr = refl
canonize-p< (suc zero) (suc (suc r1)) r2 {zero} pr2 pinr = refl
canonize-p< (suc (suc zero)) (suc zero) (suc r2) {i} pr2 (s≤s (s≤s ())) {pinr}
canonize-p< (suc (suc zero)) (suc (suc r1)) (suc r2) {i} pr2 (s≤s (s≤s prn)) {pinr} = ≤-abs prn
canonize-p< (suc (suc (suc zero))) (suc (suc r1)) (suc r2) {i} pr2 (s≤s (s≤s (s≤s prn))) {pinr} = ≤-abs (≤-remove-+ prn)
-- and now the induction
canonize-p< (suc (suc (suc zero))) (suc zero) (suc r2) {i} pr2 prn {pinr} rewrite pinr = swap (s≤s (s≤s z≤n)) -- base case
canonize-p< (suc (suc (suc (suc n)))) (suc r1) (suc r2) {i} pr2 (s≤s prn) {pinr} = -- inductive case
  let rec = prepend (3 + n) (canonize-p< (suc (suc (suc n))) r1 (suc r2) {i} pr2 prn {pinr})

      i≤1+n : i ≤ (suc n)
      i≤1+n = ∸-implies-≤ {_} {_} {r1 + suc r2} pinr

      lemma =
        ≃begin
          ((3 + n) ∷ ((3 + n) ↓ r1) ++ [ i ])
        ≃⟨ rec ⟩
          (3 + n) ∷ i ∷ ((3 + n) ↓ r1)
        ≃⟨ ++-respects (swap (s≤s (s≤s i≤1+n))) refl ⟩
          (i ∷ 3 + n ∷ (3 + n) ↓ r1)
        ≃∎
  in lemma

canonize-swap : (n r i : ℕ)
                -> (r ≤ n)
                -> ((suc n) < i)
                -> ((n ↓ r) ++ [ i ]) ≃ (i ∷ (n ↓ r))
canonize-swap zero zero i prn pni = refl
canonize-swap (suc n) zero i prn pni = refl
canonize-swap (suc n) (suc r) i prn pni =
  let rec = canonize-swap n r i (≤-down2 prn) (≤-down pni)
  in  ≃begin
         n ∷ (n ↓ r) ++ i ∷ []
       ≃⟨ prepend n rec ⟩
         n ∷ i ∷ (n ↓ r)
       ≃⟨ ++-respects (comm (swap (≤-down pni))) refl ⟩
         i ∷ n ∷ (n ↓ r)
       ≃∎

-- REMEMBER - i is (suc i)
canonize-p> : (n r1 r2 : ℕ)
              -> {i : ℕ}
              -> ((suc (suc zero)) ≤ r2)
              -> (r1 + r2 < n)
              -> {i ≡ n ∸ (2 + r1)}
              -> (((n ↓ r1) ++ [ 1 + i ] ++ (1 + i) ↓ r2) ++ [ 1 + i ]) ≃ (i ∷ (n ↓ (1 + r1 + r2)))
-- again, weeding out small, impossible cases
canonize-p> (suc zero) r1 (suc r2) {i} pr2 prn = ≤-abs (≤-remove-+ {r1} (≤-down2 prn))
canonize-p> (suc (suc zero)) r1 (suc zero) {i} (s≤s ()) prn
canonize-p> (suc (suc zero)) (suc r1) (suc (suc zero)) {i} pr2 (s≤s (s≤s prn)) = ≤-abs (≤-remove-+ {r1} prn)
canonize-p> (suc (suc zero)) r1 (suc (suc (suc r2))) {i} pr2 (s≤s prn) = ≤-abs (≤-down2 (≤-remove-+ {r1} prn))
canonize-p> (suc (suc (suc n))) zero (suc zero) {i} (s≤s ()) prn {pinr}
canonize-p> (suc (suc (suc n))) (suc r1) (suc zero) {i} (s≤s ()) prn
-- now, induction
canonize-p> (suc (suc zero)) zero (suc (suc zero)) {i} pr2 prn {pinr} rewrite pinr = comm braid -- base case on r1 and r2
canonize-p> (suc (suc (suc n))) zero (suc (suc r2)) {suc i} pr2 (s≤s (s≤s (s≤s prn))) {pinr} rewrite (≡-down2 i n pinr) = -- induction on r2
  let rec = canonize-swap n r2 (2 + n) (prn) (s≤s (s≤s (≤-reflexive refl)))
  in  ≃begin
         (2 + n) ∷ (1 + n) ∷ n ∷ (n ↓ r2) ++ (2 + n) ∷ []
       ≃⟨ prepend (2 + n) (prepend (1 + n) (prepend n rec)) ⟩
         (2 + n) ∷ (1 + n) ∷ n ∷ (2 + n) ∷ (n ↓ r2)
       ≃⟨ prepend (2 + n) (prepend (1 + n) (++-respects (comm (swap (s≤s (≤-reflexive refl)))) refl)) ⟩
         (2 + n) ∷ 1 + n ∷ (2 + n) ∷ n ∷ (n ↓ r2)
       ≃⟨ ++-respects (comm braid) refl ⟩
         (1 + n) ∷ (2 + n) ∷ (1 + n) ∷ n ∷ (n ↓ r2)
       ≃∎
canonize-p> (suc (suc (suc n))) (suc r1) (suc (suc r2)) {i} pr2 prn {pinr} = -- induction on r1
  let rec = canonize-p> (suc (suc n)) r1 (suc (suc r2)) {i} pr2 (≤-down2 prn) {pinr}
  in ≃begin
         (2 + n) ∷ (((2 + n) ↓ r1) ++ (1 + i) ∷ i ∷ (i ↓ (1 + r2))) ++ (1 + i) ∷ []
       ≃⟨ prepend (2 + n) rec ⟩
         (2 + n) ∷ i ∷ (1 + n) ∷ ((1 + n) ↓ (r1 + (2 + r2)))
       ≃⟨ ++-respects (swap (s≤s (s≤s (∸-implies-≤ {r = r1} pinr)))) (refl {(1 + n) ∷ ((1 + n) ↓ (r1 + (2 + r2)))} ) ⟩
         i ∷ (2 + n) ∷ (1 + n) ∷ ((1 + n) ↓ (r1 + (2 + r2)))
       ≃∎

add-lemma : {i r : ℕ} -> suc (i + 1 + r) ≡ suc (suc (i + r))
add-lemma {i} {r} =
  begin
    suc (i + 1 + r)
  ≡⟨ cong (λ x -> suc x) (+-three-assoc {i} {1} {r}) ⟩
    suc (suc (i + r))
  ∎

canonize-p≡ : (n r i : ℕ)
              -> (0 < n)
              -> (r < n)
              -> (i ≡ n ∸ (1 + r))
              -> ((n ↓ r) ++ [ i ]) ≃ (n ↓ (1 + r))
canonize-p≡ (suc n) r i pn prn pirn =
  let tt = ≡-sym (↓-rec {suc n} {r} prn)
      i=n-r-1 : (suc n) ∸ (r + 1) ≡ i
      i=n-r-1 = begin
                    suc n ∸ (r + 1)
                  ≡⟨ cong (λ x -> (suc n) ∸ x) (+-comm r 1) ⟩
                    suc n ∸ (1 + r)
                  ≡⟨ refl ⟩
                    n ∸ r
                  ≡⟨ ≡-sym pirn ⟩
                    i
                  ∎
  in refl≡ (subst (λ k -> ((suc n) ↓ r) ++ [ k ] ≡ ((suc n) ↓ suc r))  i=n-r-1 tt)


F-canonize-p> : (n r i : ℕ)
                -> (0 < n)
                -> (r ≤ n)
                -> ((suc i) < n)
                -> (n < (suc i) + r)
                -> ((n ↓ r) ++ [ suc i ]) ≃ (i ∷ n ↓ r)
F-canonize-p> (suc n) zero i pn prn (s≤s pin) (s≤s pirn) =
  let tt = begin-≤
             suc (suc n)
           ≤⟨ s≤s pirn ⟩
             suc (i + zero)
           ≤⟨ s≤s (≤-reflexive (+-comm i zero)) ⟩
             suc i
           ≤⟨ pin ⟩
             n
           ≤⟨ ≤-up (≤-reflexive refl) ⟩
             suc n
           ≤∎
  in  ⊥-elim (1+n≰n tt)

F-canonize-p> (suc n) (suc zero) i pn prn (s≤s pin) (s≤s pirn) =
  let tt = begin-≤
             suc (suc n)
           ≤⟨ s≤s pirn ⟩
             suc (i + 1)
           ≤⟨ s≤s (≤-reflexive (+-comm i 1)) ⟩
             suc (suc i)
           ≤⟨ s≤s pin ⟩
             suc n
           ≤∎
  in  ⊥-elim (1+n≰n tt)

F-canonize-p> (suc n) (suc (suc r)) i pn prn (s≤s pin) pirn =
  let tt = begin-≤
             suc i
           ≤⟨ pin ⟩
             n
           <⟨ <⇒≤ pirn ⟩
              suc (i + (2 + r))
           ≤∎
      tt = canonize-p> (suc n) ((suc n) ∸ (2 + i) ) ( ((suc i) + (2 + r)) ∸ (suc n) ) {i} {!   !} {!   !} {{!!}}
  in {!   !}

F-canonize-p≡ : (n r i : ℕ)
                -> (0 < n)
                -> (r < n)
                -> ((suc i) < n)
                -> (((suc i) + 1 + r) ≡ n)
                -> ((n ↓ r) ++ [ suc i ]) ≃ (n ↓ (1 + r))
F-canonize-p≡ n r i pn prn pin pirn =
  let tx = begin
             (suc i) + suc r
           ≡⟨ cong suc (≡-sym (+-assoc i 1 r)) ⟩
             suc ((i + 1) + r)
           ≡⟨ pirn ⟩
             n
           ∎
  in  canonize-p≡ n r (suc i) pn prn (∸-with-≡ prn tx)

F-canonize-p< : (n r i : ℕ)
                -> (0 < n)
                -> (r ≤ n)
                -> ((suc i) < n)
                -> ((suc i) + (1 + r) < n)
                -> ((n ↓ r) ++ [ suc i ]) ≃ ((suc i) ∷ n ↓ r)
F-canonize-p< (suc n) r i pn prn (s≤s pin) pirn = {!!} --
--  let xx = {!!}
--  in  canonize-p< n r ( n ∸ (2 + i + r)) {suc i} {!!} {!!} {{!!}}
