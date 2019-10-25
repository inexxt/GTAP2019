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
open import Data.Bool hiding (_<_; _≤_; ≤-trans)
open import Data.Bool.Properties hiding (≤-reflexive; ≤-trans)
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

_↓_ : (n : ℕ) -> (k : ℕ) -> List ℕ
n ↓ 0 = []
n ↓ (suc k) = (k + n) ∷ (n ↓ k)

-- ↓-rec : {n k : ℕ} -> (k < n) -> (n ↓ suc k) ≡ (n ↓ k) ++ [ n ∸ (k + 1) ]
-- ↓-rec {suc zero} {zero} (s≤s z≤n) = refl
-- ↓-rec {suc (suc n)} {zero} (s≤s z≤n) = refl
-- ↓-rec {suc (suc n)} {suc k} (s≤s p) = cong (λ l -> suc n ∷ l) (↓-rec p)

data _≅_ : List ℕ -> List ℕ -> Set where
    cancel≅ : (l r m mf : List ℕ) -> (defm : m ≡ l ++ n ∷ n ∷ r) -> (defmf : mf ≡ l ++ r) -> (m ≅ mf)
    swap≅ : {k : ℕ} -> (suc k < n) ->  (l r m mf : List ℕ) -> (defm : m ≡ l ++ n ∷ k ∷ r) -> (defmf : mf ≡ l ++ k ∷ n ∷ r) -> (m ≅ mf)
    long≅ : (k : ℕ) -> (l r m mf : List ℕ) -> (defm : m ≡ l ++ (n ↓ (2 + k)) ++ (1 + k + n) ∷ r) -> (defmf : mf ≡ l ++ (k + n) ∷ (n ↓ (2 + k)) ++ r) -> (m ≅ mf)

data _≅*_ : List ℕ -> List ℕ -> Set where
    refl : {m : List ℕ} -> m ≅* m
    trans≅ : {m1 m2 m3 : List ℕ} -> (m1 ≅ m2) -> (m2 ≅* m3) -> m1 ≅* m3

cancel-c : (l r : List ℕ) -> (l ++ n ∷ n ∷ r) ≅ (l ++ r)
cancel-c = {!!}

swap-c : {k : ℕ} -> (pk : suc k < n) ->  (l r : List ℕ) -> (l ++ n ∷ k ∷ r) ≅ (l ++ k ∷ n ∷ r)
swap-c {k} pk l r = {!!}

long-c : (k : ℕ) -> (l r : List ℕ) -> (l ++ (n ↓ (2 + k)) ++ (1 + k + n) ∷ r) ≅ (l ++ (k + n) ∷ (n ↓ (2 + k)) ++ r)
long-c k l r = long≅ k l r _ _ refl refl

ext : {l l' : List ℕ} -> l ≅ l' -> l ≅* l'
ext p = trans≅ p refl

cancel : (l r : List ℕ) -> (l ++ n ∷ n ∷ r) ≅* (l ++ r)
cancel = {!!}

swap : {k : ℕ} -> (pk : suc k < n) ->  (l r : List ℕ) -> (l ++ n ∷ k ∷ r) ≅* (l ++ k ∷ n ∷ r)
swap {k} pk l r = {!!}

long : (k : ℕ) -> (l r : List ℕ) -> (l ++ (n ↓ (2 + k)) ++ (1 + k + n) ∷ r) ≅* (l ++ (k + n) ∷ (n ↓ (2 + k)) ++ r)
long k l r = ext (long≅ k l r _ _ refl refl)

braid : (l r : List ℕ) -> (l ++ suc n ∷ n ∷ suc n ∷ r) ≅* (l ++ n ∷ suc n ∷ n ∷ r)
braid {n} l r = long {n} 0 l r

trans : {m1 m2 m3 : List ℕ} -> (m1 ≅* m2) -> (m2 ≅* m3) -> m1 ≅* m3
trans refl p  = p
trans (trans≅ x q) p = trans≅ x (trans q p)

l++≅ : (m1 m2 l : List ℕ) -> (m1 ≅ m2) -> ((l ++ m1) ≅ (l ++ m2))
l++≅ m1 m2 l (cancel≅ l₁ r .m1 .m2 defm defmf) = {!   !}
l++≅ m1 m2 l (swap≅ x l₁ r .m1 .m2 defm defmf) = {!   !}
l++≅ m1 m2 l (long≅ k l₁ r .m1 .m2 defm defmf) = {!   !}

l++ : (l : List ℕ) -> {m1 m2 : List ℕ} -> (m1 ≅* m2) -> ((l ++ m1) ≅* (l ++ m2))
l++ l p = {!   !}

++r≅ : (m1 m2 r : List ℕ) -> (m1 ≅ m2) -> ((m1 ++ r) ≅ (m2 ++ r))
++r≅ m1 m2 l (cancel≅ l₁ r .m1 .m2 defm defmf) = {!   !}
++r≅ m1 m2 l (swap≅ x l₁ r .m1 .m2 defm defmf) = {!   !}
++r≅ m1 m2 l (long≅ k l₁ r .m1 .m2 defm defmf) = {!   !}

++r : {m1 m2 : List ℕ} -> (r : List ℕ) -> (m1 ≅* m2) -> ((m1 ++ r) ≅* (m2 ++ r))
++r r p = {!   !}

refl≡ : {l l' : List ℕ} -> (l ≡ l') -> l ≅* l'
refl≡ refl = refl

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
short-swap {n} {k} {.n} {tl} {zero} refl ptkn = {!   !}
short-swap {n} {k} {.(suc (tr + n))} {tl} {suc tr} refl ptkn = {!   !}

-- short-swap {zero} {zero} {zero} pnt (s≤s ptkn) = braid [] []
-- short-swap {suc n} {zero} {zero} (s≤s ()) (s≤s ptkn)
-- short-swap {zero} {suc k} {zero} pnt (s≤s ptkn) rewrite (+-unit {k}) = {!   !}
-- short-swap {suc n} {suc k} {zero} pnt (s≤s ptkn) = {!   !}
-- short-swap {n} {zero} {suc t} (s≤s pnt) (s≤s ptkn) rewrite (≤-≡ ptkn pnt) = braid [] []
-- short-swap {n} {suc k} {suc t} pnt (s≤s ptkn) = ?

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

≅-abs-l : {x : ℕ} -> (x ∷ []) ≅ [] -> ⊥
≅-abs-l (cancel≅ [] r .(_ ∷ []) .[] () defmf)
≅-abs-l (cancel≅ (x ∷ []) r .(_ ∷ []) .[] () defmf)
≅-abs-l (cancel≅ (x ∷ x₁ ∷ l) r .(_ ∷ []) .[] () defmf)
≅-abs-l (swap≅ x [] r .(_ ∷ []) .[] () defmf)
≅-abs-l (swap≅ x (x₁ ∷ []) r .(_ ∷ []) .[] () defmf)
≅-abs-l (swap≅ x (x₁ ∷ x₂ ∷ l) r .(_ ∷ []) .[] () defmf)
≅-abs-l (long≅ k [] r .(_ ∷ []) .[] defm ())
≅-abs-l (long≅ k (x ∷ l) r .(_ ∷ []) .[] defm ())

≅-abs-r : {x : ℕ} -> [] ≅ (x ∷ []) -> ⊥
≅-abs-r (cancel≅ [] r .[] .(_ ∷ []) () defmf)
≅-abs-r (cancel≅ (x ∷ l) r .[] .(_ ∷ []) () defmf)
≅-abs-r (swap≅ x [] r .[] .(_ ∷ []) () defmf)
≅-abs-r (swap≅ x (x₁ ∷ l) r .[] .(_ ∷ []) () defmf)
≅-abs-r (long≅ k [] r .[] .(_ ∷ []) () defmf)
≅-abs-r (long≅ k (x ∷ l) r .[] .(_ ∷ []) () defmf)
--
empty-reduction : {m : List ℕ} -> ([] ≅ m) -> ⊥
empty-reduction (cancel≅ [] r .[] _ () defmf)
empty-reduction (cancel≅ (x ∷ l) r .[] _ () defmf)
empty-reduction (swap≅ x [] r .[] _ () defmf)
empty-reduction (swap≅ x (x₁ ∷ l) r .[] _ () defmf)
empty-reduction (long≅ k [] r .[] mf () defmf)
empty-reduction (long≅ k (x ∷ l) r .[] mf () defmf)

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

start+end : {h1 h2 : List ℕ} -> {t1 t2 : List ℕ} -> (h1 ≡ h2) -> (t1 ≡ t2) -> (h1 ++ t1) ≡ (h2 ++ t2)
start+end p1 p2 = {!!}
