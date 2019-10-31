{-# OPTIONS --without-K #-}
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
open import Data.Bool.Properties hiding (≤-reflexive; ≤-trans)
open import Function

open import Arithmetic hiding (n)
open import Lists
open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to ≤∎) hiding (_≡⟨_⟩_; _≡⟨⟩_)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)


variable
  n : ℕ
  l : List ℕ

data _≅_ : List ℕ -> List ℕ -> Set where
    cancel≅ : (l r m mf : List ℕ) -> (defm : m ≡ l ++ n ∷ n ∷ r) -> (defmf : mf ≡ l ++ r) -> (m ≅ mf)
    swap≅ : {k : ℕ} -> (suc k < n) ->  (l r m mf : List ℕ) -> (defm : m ≡ l ++ n ∷ k ∷ r) -> (defmf : mf ≡ l ++ k ∷ n ∷ r) -> (m ≅ mf)
    long≅ : (k : ℕ) -> (l r m mf : List ℕ) -> (defm : m ≡ l ++ (n ↓ (2 + k)) ++ (1 + k + n) ∷ r) -> (defmf : mf ≡ l ++ (k + n) ∷ (n ↓ (2 + k)) ++ r) -> (m ≅ mf)

data _≅*_ : List ℕ -> List ℕ -> Set where
    refl : {m : List ℕ} -> m ≅* m
    trans≅ : {m1 m2 m3 : List ℕ} -> (m1 ≅ m2) -> (m2 ≅* m3) -> m1 ≅* m3

cancel-c : (l r : List ℕ) -> (l ++ n ∷ n ∷ r) ≅ (l ++ r)
cancel-c {n} = λ l r → cancel≅ l r (l ++ n ∷ n ∷ r) (l ++ r) refl refl

swap-c : {k : ℕ} -> (pk : suc k < n) ->  (l r : List ℕ) -> (l ++ n ∷ k ∷ r) ≅ (l ++ k ∷ n ∷ r)
swap-c {k} pk l r = swap≅ pk l r (l ++ k ∷ _ ∷ r) (l ++ _ ∷ k ∷ r) refl refl

long-c : (k : ℕ) -> (l r : List ℕ) -> (l ++ (n ↓ (2 + k)) ++ (1 + k + n) ∷ r) ≅ (l ++ (k + n) ∷ (n ↓ (2 + k)) ++ r)
long-c k l r = long≅ k l r _ _ refl refl

ext : {l l' : List ℕ} -> l ≅ l' -> l ≅* l'
ext p = trans≅ p refl

cancel : (l r : List ℕ) -> (l ++ n ∷ n ∷ r) ≅* (l ++ r)
cancel {n} = λ l r →
             trans≅ (cancel≅ l r (l ++ n ∷ n ∷ r) (l ++ r) refl refl) refl

swap : {k : ℕ} -> (pk : suc k < n) ->  (l r : List ℕ) -> (l ++ n ∷ k ∷ r) ≅* (l ++ k ∷ n ∷ r)
swap {k} pk l r = trans≅ (swap≅ pk l r (l ++ k ∷ _ ∷ r) (l ++ _ ∷ k ∷ r) refl refl)
                    refl

long : (k : ℕ) -> (l r : List ℕ) -> (l ++ (n ↓ (2 + k)) ++ (1 + k + n) ∷ r) ≅* (l ++ (k + n) ∷ (n ↓ (2 + k)) ++ r)
long k l r = ext (long≅ k l r _ _ refl refl)

braid : (l r : List ℕ) -> (l ++ suc n ∷ n ∷ suc n ∷ r) ≅* (l ++ n ∷ suc n ∷ n ∷ r)
braid {n} l r = long {n} 0 l r

trans : {m1 m2 m3 : List ℕ} -> (m1 ≅* m2) -> (m2 ≅* m3) -> m1 ≅* m3
trans refl p  = p
trans (trans≅ x q) p = trans≅ x (trans q p)

l++≅ : (m1 m2 l : List ℕ) -> (m1 ≅ m2) -> ((l ++ m1) ≅ (l ++ m2))
l++≅ m1 m2 l (cancel≅ l₁ r .m1 .m2 defm defmf) =  cancel≅ (l ++ l₁) r _ _ (≡-trans (start+end refl defm) (≡-sym (++-assoc l l₁ _))) ((≡-trans (start+end refl defmf) (≡-sym (++-assoc l l₁ _))))
l++≅ m1 m2 l (swap≅ x l₁ r .m1 .m2 defm defmf) =  swap≅ x (l ++ l₁) r _ _ (≡-trans (start+end refl defm) (≡-sym (++-assoc l l₁ _))) ((≡-trans (start+end refl defmf) (≡-sym (++-assoc l l₁ _))))
l++≅ m1 m2 l (long≅ k l₁ r .m1 .m2 defm defmf) =  long≅ k (l ++ l₁) r _ _ (≡-trans (start+end refl defm) (≡-sym (++-assoc l l₁ _))) ((≡-trans (start+end refl defmf) (≡-sym (++-assoc l l₁ _))))

l++ : (l : List ℕ) -> {m1 m2 : List ℕ} -> (m1 ≅* m2) -> ((l ++ m1) ≅* (l ++ m2))
l++ l refl = refl
l++ l (trans≅ x p) = trans≅ (l++≅ _ _ l x) ((l++ l p))

++r≅ : (m1 m2 r : List ℕ) -> (m1 ≅ m2) -> ((m1 ++ r) ≅ (m2 ++ r))
++r≅ m1 m2 r (cancel≅ l r₁ .m1 .m2 defm defmf) = cancel≅ l (r₁ ++ r)  _ _  (≡-trans (start+end defm refl) (++-assoc l _ r)) ((≡-trans (start+end defmf refl) (++-assoc l _ r)))
++r≅ m1 m2 r (swap≅ x l r₁ .m1 .m2 defm defmf) = swap≅ x l (r₁ ++ r)  _ _  (≡-trans (start+end defm refl) (++-assoc l _ r)) ((≡-trans (start+end defmf refl) (++-assoc l _ r)))
++r≅ m1 m2 r (long≅ k l r₁ .m1 .m2 defm defmf) = long≅ k l (r₁ ++ r)  _ _
  (≡-trans (start+end defm refl) (≡-trans (++-assoc l _ r) (start+end (refl {x = l}) (head+tail refl (head+tail refl (++-assoc (_ ↓ k) _ r))))))
  ((≡-trans (start+end defmf refl) (≡-trans (++-assoc l _ r) (start+end (refl {x = l}) (head+tail refl (head+tail refl (head+tail refl (++-assoc _ r₁ r))))))))

++r : {m1 m2 : List ℕ} -> (r : List ℕ) -> (m1 ≅* m2) -> ((m1 ++ r) ≅* (m2 ++ r))
++r r refl = refl
++r r (trans≅ x p) = trans≅ (++r≅ _ _ r x) (++r r p)

refl≡ : {l l' : List ℕ} -> (l ≡ l') -> l ≅* l'
refl≡ refl = refl

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

one-reduction : {x : ℕ} -> {m : List ℕ} -> ([ x ] ≅ m) -> ⊥
one-reduction {x} (cancel≅ (x₁ ∷ []) r .(x ∷ []) mf () defmf)
one-reduction {x} (cancel≅ (x₁ ∷ x₂ ∷ l) r .(x ∷ []) mf () defmf)
one-reduction {x} (swap≅ x₁ (x₂ ∷ []) r .(x ∷ []) mf () defmf)
one-reduction {x} (swap≅ x₁ (x₂ ∷ x₃ ∷ l) r .(x ∷ []) mf () defmf)
one-reduction {x} (long≅ k (x₁ ∷ []) r .(x ∷ []) mf () defmf)
one-reduction {x} (long≅ k (x₁ ∷ x₂ ∷ l) r .(x ∷ []) mf () defmf)
