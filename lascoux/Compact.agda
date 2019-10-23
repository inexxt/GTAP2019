{-# OPTIONS --allow-unsolved-metas --without-K #-}
module Compact where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; _×_; _,_)

open import Relation.Nullary
open import Data.Empty
open import Data.Sum hiding (swap)
open import Data.Bool hiding (_<_; _≤_)
open import Data.Bool.Properties hiding (≤-reflexive)
open import Function

open import Arithmetic hiding (n)
open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to ≤∎) hiding (_≡⟨_⟩_; _≡⟨⟩_)


open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)


variable
    n : ℕ
    l : List ℕ

data nonempty : List ℕ -> Set where
  nonempty-l : (x : ℕ) -> (l : List ℕ) -> nonempty (x ∷ l)

data _≅_ : List ℕ -> List ℕ -> Set where
    cancel≅ : (l r m mf : List ℕ) -> (defm : m ≡ l ++ n ∷ n ∷ r) -> (defmf : mf ≡ l ++ r) -> (m ≅ mf)
    swap≅ : {k : ℕ} -> (suc k < n) ->  (l r m mf : List ℕ) -> (defm : m ≡ l ++ n ∷ k ∷ r) -> (defmf : mf ≡ l ++ k ∷ n ∷ r) -> (m ≅ mf)
    braid≅ :  (l r m mf : List ℕ) -> (defm : m ≡ l ++ (suc n) ∷ n ∷ (suc n) ∷ r) -> (defmf : mf ≡ l ++ n ∷ (suc n) ∷ n ∷ r) -> (m ≅ mf)
    bs≅ : (l r m mf : List ℕ) -> (defm : m ≡ l ++ (2 + n) ∷ (1 + n) ∷ n ∷ (2 + n) ∷ r) -> (defmf : mf ≡ l ++ (1 + n) ∷ (2 + n) ∷ (1 + n) ∷ n ∷ r) -> (m ≅ mf)

data _≅*_ : List ℕ -> List ℕ -> Set where
    refl : {m : List ℕ} -> m ≅* m
    trans≅ : {m1 m2 m3 : List ℕ} -> (m1 ≅ m2) -> (m2 ≅* m3) -> m1 ≅* m3

cancel-c : (l r : List ℕ) -> (l ++ n ∷ n ∷ r) ≅ (l ++ r)
cancel-c = {!!}

swap-c : {k : ℕ} -> (pk : suc k < n) ->  (l r : List ℕ) -> (l ++ n ∷ k ∷ r) ≅ (l ++ k ∷ n ∷ r)
swap-c {k} pk l r = {!!}

braid-c : (l r : List ℕ) -> (l ++ (suc n) ∷ n ∷ (suc n) ∷ r) ≅ (l ++ n ∷ (suc n) ∷ n ∷ r)
braid-c = {!!}


ext : {l l' : List ℕ} -> l ≅ l' -> l ≅* l'
ext p = trans≅ p refl

cancel : (l r : List ℕ) -> (l ++ n ∷ n ∷ r) ≅* (l ++ r)
cancel = {!!}

swap : {k : ℕ} -> (pk : suc k < n) ->  (l r : List ℕ) -> (l ++ n ∷ k ∷ r) ≅* (l ++ k ∷ n ∷ r)
swap {k} pk l r = {!!}

braid : (l r : List ℕ) -> (l ++ (suc n) ∷ n ∷ (suc n) ∷ r) ≅* (l ++ n ∷ (suc n) ∷ n ∷ r)
braid = {!!}

bs : (l r : List ℕ) -> (l ++ (2 + n) ∷ (1 + n) ∷ n ∷ (2 + n) ∷ r) ≅* (l ++ (1 + n) ∷ (2 + n) ∷ (1 + n) ∷ n ∷ r)
bs = {!!}

trans : {m1 m2 m3 : List ℕ} -> (m1 ≅* m2) -> (m2 ≅* m3) -> m1 ≅* m3
trans refl p  = p
trans (trans≅ x q) p = trans≅ x (trans q p)

---

abs-suc : {A : Set} -> suc n < n -> A
abs-suc {n} p = ⊥-elim (1+n≰n (≤-down p))

module ≅*-Reasoning where
    infix  1 ≅*begin_
    infixr 2 _≅*⟨⟩_ _≅*⟨_⟩_
    infix  3 _≅*∎

    ≅*begin_ : ∀ {x y : List ℕ}
             → x ≅* y
               -----
             → x ≅* y
    ≅*begin x≅*y  =  x≅*y

    _≅*⟨⟩_ : ∀ (x : List ℕ) {y : List ℕ}
            → x ≅* y
              -----
            → x ≅* y
    x ≅*⟨⟩ x≅*y  =  x≅*y

    _≅*⟨_⟩_ : ∀ (x : List ℕ) {y z : List ℕ}
             → x ≅* y
             → y ≅* z
               -----
             → x ≅* z
    x ≅*⟨ x≅*y ⟩ y≅*z  = trans x≅*y y≅*z

    _≅*∎ : ∀ (x : List ℕ)
           -----
          → x ≅* x
    x ≅*∎  =  refl

open ≅*-Reasoning

postulate
    ++-unit : l ++ [] ≡ l

refl≡ : {l l' : List ℕ} -> (l ≡ l') -> l ≅* l'
refl≡ refl = refl

≅-abs-l : {x : ℕ} -> (x ∷ []) ≅ [] -> ⊥
≅-abs-l (cancel≅ [] r .(_ ∷ []) .[] () defmf)
≅-abs-l (cancel≅ (x ∷ []) r .(_ ∷ []) .[] () defmf)
≅-abs-l (cancel≅ (x ∷ x₁ ∷ l) r .(_ ∷ []) .[] () defmf)
≅-abs-l (swap≅ x [] r .(_ ∷ []) .[] () defmf)
≅-abs-l (swap≅ x (x₁ ∷ []) r .(_ ∷ []) .[] () defmf)
≅-abs-l (swap≅ x (x₁ ∷ x₂ ∷ l) r .(_ ∷ []) .[] () defmf)
≅-abs-l (braid≅ [] r .(_ ∷ []) .[] () defmf)
≅-abs-l (braid≅ (x ∷ []) r .(_ ∷ []) .[] () defmf)
≅-abs-l (braid≅ (x ∷ x₁ ∷ l) r .(_ ∷ []) .[] () defmf)
≅-abs-l (bs≅ [] r .(_ ∷ []) .[] () defmf)
≅-abs-l (bs≅ (x ∷ []) r .(_ ∷ []) .[] () defmf)
≅-abs-l (bs≅ (x ∷ x₁ ∷ l) r .(_ ∷ []) .[] () defmf)

≅-abs-r : {x : ℕ} -> [] ≅ (x ∷ []) -> ⊥
≅-abs-r (cancel≅ [] r .[] .(_ ∷ []) () defmf)
≅-abs-r (cancel≅ (x ∷ l) r .[] .(_ ∷ []) () defmf)
≅-abs-r (swap≅ x [] r .[] .(_ ∷ []) () defmf)
≅-abs-r (swap≅ x (x₁ ∷ l) r .[] .(_ ∷ []) () defmf)
≅-abs-r (braid≅ [] r .[] .(_ ∷ []) () defmf)
≅-abs-r (braid≅ (x ∷ l) r .[] .(_ ∷ []) () defmf)
≅-abs-r (bs≅ [] r .[] .(_ ∷ []) () defmf)
≅-abs-r (bs≅ (x ∷ l) r .[] .(_ ∷ []) () defmf)

empty-reduction : {m : List ℕ} -> ([] ≅ m) -> ⊥
empty-reduction (cancel≅ [] r .[] _ () defmf)
empty-reduction (cancel≅ (x ∷ l) r .[] _ () defmf)
empty-reduction (swap≅ x [] r .[] _ () defmf)
empty-reduction (swap≅ x (x₁ ∷ l) r .[] _ () defmf)
empty-reduction (braid≅ [] r .[] _ () defmf)
empty-reduction (braid≅ (x ∷ l) r .[] _ () defmf)
empty-reduction (bs≅ [] r .[] mf () defmf)
empty-reduction (bs≅ (x ∷ l) r .[] mf () defmf)

mod2 : ℕ -> Bool
mod2 0 = true
mod2 (suc n) with mod2 n
... | true = false
... | false = true

abs-bool : (true ≡ false) -> ⊥
abs-bool ()

postulate
  -- these are proved for the previous representation, it's possible to transport them to here
  mod2-+ : (n1 n2 : ℕ) -> mod2 (n1 + n2) ≡ not ((mod2 n1) xor (mod2 n2))
  len-mod2≅ : (m1 m2 : List ℕ) -> (m1 ≅ m2) -> (mod2 (length m1) ≡ mod2 (length m2))
  len-nonincreasing≅ : (m1 m2 : List ℕ) -> (m1 ≅ m2) -> (length m2 ≤ length m1)
  diamond-separate : {l r l' r' ml mr : List ℕ} -> (ml ≡ l' ++ r) -> (mr ≡ l ++ r') -> (l ≅ l') -> (r ≅ r') -> (ml ≅ (l' ++ r')) × (mr ≅ (l' ++ r'))

  -- this ones are a little different (just because the new ≅ doesnt have reflexivity)
  one-one-reduction : (n1 n2 : ℕ) -> ((n1 ∷ []) ≅* (n2 ∷ [])) -> n1 ≡ n2
  two-two-reduction : (a b1 b2 : ℕ) -> ((a ∷ a ∷ []) ≅* (b1 ∷ b2 ∷ [])) -> (b1 ≡ b2) × (a ≡ b1)
  cancel-reduction : (m : List ℕ) -> ((n ∷ n ∷ []) ≅* m) -> (m ≡ []) ⊎ (m ≡ (n ∷ n ∷ []))
  -- one-reduction : (m : List ℕ) -> ((n ∷ []) ≅* m) -> m ≡ (n ∷ [])

  -- these ones are extension to ≅*
  len-mod2 : (m1 m2 : List ℕ) -> (m1 ≅* m2) -> (mod2 (length m1) ≡ mod2 (length m2))
  len-nonincreasing : (m1 m2 : List ℕ) -> (m1 ≅* m2) -> (length m2 ≤ length m1)


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
head+tail p1 p2 = {!!}
