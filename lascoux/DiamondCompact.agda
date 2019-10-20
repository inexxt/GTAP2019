{-# OPTIONS --allow-unsolved-metas #-}
module DiamondCompact where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; _×_; _,_)
-- open import General
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
    r : List ℕ
    m : List ℕ
    mf : List ℕ

data nonempty : List ℕ -> Set where
  nonempty-l : (x : ℕ) -> (l : List ℕ) -> nonempty (x ∷ l)

data _≅_ : List ℕ -> List ℕ -> Set where
    cancel≅ : (l r m mf : List ℕ) -> (defm : m ≡ l ++ n ∷ n ∷ r) -> (defmf : mf ≡ l ++ r) -> (m ≅ mf)
    swap≅ : {k : ℕ} -> (suc k < n) ->  (l r m mf : List ℕ) -> (defm : m ≡ l ++ n ∷ k ∷ r) -> (defmf : mf ≡ l ++ k ∷ n ∷ r) -> (m ≅ mf)
    braid≅ :  (l r m mf : List ℕ) -> (defm : m ≡ l ++ (suc n) ∷ n ∷ (suc n) ∷ r) -> (defmf : mf ≡ l ++ n ∷ (suc n) ∷ n ∷ r) -> (m ≅ mf)

data _≃_ : List ℕ -> List ℕ -> Set where
    refl : {m : List ℕ} -> m ≃ m
    trans≅ : {m1 m2 m3 : List ℕ} -> (m1 ≅ m2) -> (m2 ≃ m3) -> m1 ≃ m3

cancel-c : (l r : List ℕ) -> (l ++ n ∷ n ∷ r) ≅ (l ++ r)
cancel-c = {!!}

swap-c : {k : ℕ} -> (pk : suc k < n) ->  (l r : List ℕ) -> (l ++ n ∷ k ∷ r) ≅ (l ++ k ∷ n ∷ r)
swap-c {k} pk l r = {!!}

braid-c : (l r : List ℕ) -> (l ++ (suc n) ∷ n ∷ (suc n) ∷ r) ≅ (l ++ n ∷ (suc n) ∷ n ∷ r)
braid-c = {!!}


ext : {l l' : List ℕ} -> l ≅ l' -> l ≃ l'
ext p = trans≅ p refl

cancel : (l r : List ℕ) -> (l ++ n ∷ n ∷ r) ≃ (l ++ r)
cancel = {!!}

swap : {k : ℕ} -> (pk : suc k < n) ->  (l r : List ℕ) -> (l ++ n ∷ k ∷ r) ≃ (l ++ k ∷ n ∷ r)
swap {k} pk l r = {!!}

braid : (l r m mf : List ℕ) -> (l ++ (suc n) ∷ n ∷ (suc n) ∷ r) ≃ (l ++ n ∷ (suc n) ∷ n ∷ r)
braid = {!!}

trans : {m1 m2 m3 : List ℕ} -> (m1 ≃ m2) -> (m2 ≃ m3) -> m1 ≃ m3
trans refl p  = p
trans (trans≅ x q) p = trans≅ x (trans q p)

---
abs-suc : {A : Set} -> suc n < n -> A
abs-suc {n} p = ⊥-elim (1+n≰n (≤-down p))


--- critical pairs

cc : (a : ℕ) -> (m m1 m2 : List ℕ) -> (defm : m ≡ a ∷ a ∷ a ∷ []) -> (p1 : m ≅ m1) -> (p2 : m ≅ m2) -> ∃ (λ mm -> (m1 ≃ mm) × (m2 ≃ mm))
-- trivial, solved with two-two-reduction
-- cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ .(a ∷ []) [] .(a ∷ a ∷ a ∷ []) .m1 refl defmf) (cancel≅ .(a ∷ []) [] .(a ∷ a ∷ a ∷ []) .m2 refl defmf₁) rewrite defmf rewrite defmf₁ = [ a ] , refl , refl
-- cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ .[] (.a ∷ []) .(a ∷ a ∷ a ∷ []) .m1 refl defmf) (cancel≅ .(a ∷ []) [] .(a ∷ a ∷ a ∷ []) .m2 refl defmf₁) rewrite defmf rewrite defmf₁ = [ a ] , refl , refl
-- cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ l (x ∷ x₁ ∷ x₂ ∷ []) .(a ∷ a ∷ a ∷ []) .m1 () defmf) (cancel≅ .(a ∷ []) [] .(a ∷ a ∷ a ∷ []) .m2 refl defmf₁)
-- cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ l (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ r) .(a ∷ a ∷ a ∷ []) .m1 () defmf) (cancel≅ .(a ∷ []) [] .(a ∷ a ∷ a ∷ []) .m2 refl defmf₁)

-- cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ .(a ∷ []) [] .(a ∷ a ∷ a ∷ []) .m1 refl defmf) (cancel≅ .[] (.a ∷ []) .(a ∷ a ∷ a ∷ []) .m2 refl defmf₁) rewrite defmf rewrite defmf₁ = [ a ] , (refl , refl)
-- cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ .[] (.a ∷ []) .(a ∷ a ∷ a ∷ []) .m1 refl defmf) (cancel≅ .[] (.a ∷ []) .(a ∷ a ∷ a ∷ []) .m2 refl defmf₁) rewrite defmf rewrite defmf₁ = [ a ] , (refl , refl)
-- cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ l (x ∷ x₁ ∷ x₂ ∷ []) .(a ∷ a ∷ a ∷ []) .m1 () defmf) (cancel≅ .[] (.a ∷ []) .(a ∷ a ∷ a ∷ []) .m2 refl defmf₁)
-- cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ l (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ r) .(a ∷ a ∷ a ∷ []) .m1 () defmf) (cancel≅ .[] (.a ∷ []) .(a ∷ a ∷ a ∷ []) .m2 refl defmf₁)
-- cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ l r .(a ∷ a ∷ a ∷ []) .m1 defm defmf) (cancel≅ l₁ (x ∷ x₁ ∷ x₂ ∷ []) .(a ∷ a ∷ a ∷ []) .m2 () defmf₁)
-- cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ l r .(a ∷ a ∷ a ∷ []) .m1 defm defmf) (cancel≅ l₁ (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ r₁) .(a ∷ a ∷ a ∷ []) .m2 () defmf₁)

-- -- impossible
-- cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ l r .(a ∷ a ∷ a ∷ []) .m1 defm defmf) (swap≅ x l₁ r₁ .(a ∷ a ∷ a ∷ []) .m2 defm₁ defmf₁) = {!!}
-- cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ l r .(a ∷ a ∷ a ∷ []) .m1 defm defmf) (braid≅ l₁ r₁ .(a ∷ a ∷ a ∷ []) .m2 defm₁ defmf₁) = {!!}
-- cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (swap≅ x l r .(a ∷ a ∷ a ∷ []) .m1 defm defmf) p2 = {!!}
-- cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (braid≅ l r .(a ∷ a ∷ a ∷ []) .m1 defm defmf) p2 = {!!}

----------
--- CS ---
----------

cs : (a b : ℕ) -> (pab : suc b < a) -> (m m1 m2 : List ℕ) -> (defm : m ≡ a ∷ a ∷ b ∷ []) -> (p1 : m ≅ m1) -> (p2 : m ≅ m2) -> ∃ (λ mm -> (m1 ≃ mm) × (m2 ≃ mm))
-- cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (cancel≅ .(b ∷ []) [] .(a ∷ a ∷ b ∷ []) .m1 refl defmf) (swap≅ x (.a ∷ []) .[] .(a ∷ a ∷ b ∷ []) .m2 refl defmf₁) rewrite defmf rewrite defmf₁
--   = [ b ] , (refl , (trans≅ (swap-c x [] (a ∷ [])) (cancel [ b ] [])))
-- -- absurds
-- cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (cancel≅ l r .(a ∷ a ∷ b ∷ []) .m1 defm defmf) (swap≅ x [] .(b ∷ []) .(a ∷ a ∷ b ∷ []) .m2 refl defmf₁) = abs-suc x
-- cs a .a pab .(a ∷ a ∷ a ∷ []) m1 m2 refl (cancel≅ .[] (.a ∷ []) .(a ∷ a ∷ a ∷ []) .m1 refl defmf) (swap≅ x (.a ∷ []) .[] .(a ∷ a ∷ a ∷ []) .m2 refl defmf₁) = abs-suc x
-- cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (cancel≅ l (x₁ ∷ x₂ ∷ x₃ ∷ []) .(a ∷ a ∷ b ∷ []) .m1 () defmf) (swap≅ x (.a ∷ []) .[] .(a ∷ a ∷ b ∷ []) .m2 refl defmf₁)
-- cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (cancel≅ l (x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ r) .(a ∷ a ∷ b ∷ []) .m1 () defmf) (swap≅ x (.a ∷ []) .[] .(a ∷ a ∷ b ∷ []) .m2 refl defmf₁)
-- cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (cancel≅ l r .(a ∷ a ∷ b ∷ []) .m1 defm defmf) (swap≅ x (x₁ ∷ x₂ ∷ x₃ ∷ []) r₁ .(a ∷ a ∷ b ∷ []) .m2 () defmf₁)
-- cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (cancel≅ l r .(a ∷ a ∷ b ∷ []) .m1 defm defmf) (swap≅ x (x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ l₁) r₁ .(a ∷ a ∷ b ∷ []) .m2 () defmf₁)

-- -- impossible
-- cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (cancel≅ l r .(a ∷ a ∷ b ∷ []) .m1 defm defmf) (cancel≅ l₁ r₁ .(a ∷ a ∷ b ∷ []) .m2 defm₁ defmf₁) = {!!}
-- cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (cancel≅ l r .(a ∷ a ∷ b ∷ []) .m1 defm defmf) (braid≅ l₁ r₁ .(a ∷ a ∷ b ∷ []) .m2 defm₁ defmf₁) = {!!}
-- cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (swap≅ x l r .(a ∷ a ∷ b ∷ []) .m1 defm defmf) p2 = {!!}
-- cs a b pab .(a ∷ a ∷ b ∷ []) m1 m2 refl (braid≅ l r .(a ∷ a ∷ b ∷ []) .m1 defm defmf) p2 = {!!}

----------
--- CB ---
----------

bc : (a : ℕ) -> (m m1 m2 : List ℕ) -> (defm : m ≡ suc a ∷ a ∷ suc a ∷ suc a ∷ []) -> (p1 : m ≅ m1) -> (p2 : m ≅ m2) -> ∃ (λ mm -> (m1 ≃ mm) × (m2 ≃ mm))
-- bc a .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) m1 m2 refl (braid≅ [] .(suc a ∷ []) .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m1 refl defmf) (cancel≅ .[] (.(suc a) ∷ .a ∷ []) .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m2 refl defmf₁) rewrite defmf rewrite defmf₁ =
--  (suc a ∷ a ∷ []) , (trans≅ (braid-c [ a ] []) (cancel [] (suc a ∷ a ∷ [])) , refl)

-- --- absurds
-- bc a .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) m1 m2 refl (braid≅ [] .(suc a ∷ []) .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m1 refl defmf) (cancel≅ l₁ (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m2 () defmf₁)
-- bc a .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) m1 m2 refl (braid≅ [] .(suc a ∷ []) .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m1 refl defmf) (cancel≅ l₁ (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ r₁) .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m2 () defmf₁)
-- bc a .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) m1 m2 refl (braid≅ (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) r .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m1 () defmf) (cancel≅ l₁ r₁ .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m2 defm₁ defmf₁)
-- bc a .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) m1 m2 refl (braid≅ (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ l) r .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m1 () defmf) (cancel≅ l₁ r₁ .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m2 defm₁ defmf₁)

-- --- impossible
-- bc a .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) m1 m2 refl (braid≅ l r .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m1 defm defmf) (swap≅ x l₁ r₁ .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m2 defm₁ defmf₁) = {!!}
-- bc a .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) m1 m2 refl (braid≅ l r .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m1 defm defmf) (braid≅ l₁ r₁ .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m2 defm₁ defmf₁) = {!!}
-- bc a .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) m1 m2 refl (cancel≅ l r .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m1 defm defmf) p2 = {!!}
-- bc a .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) m1 m2 refl (swap≅ x l r .(suc a ∷ a ∷ suc a ∷ suc a ∷ []) .m1 defm defmf) p2 = {!!}


postulate
  sc : (a b : ℕ) -> (suc b < a) -> (m m1 m2 : List ℕ) -> (defm : m ≡ a ∷ b ∷ b ∷ []) -> (p1 : m ≅ m1) -> (p2 : m ≅ m2) -> ∃ (λ mm -> (m1 ≃ mm) × (m2 ≃ mm))
  cb : (a : ℕ) -> (m m1 m2 : List ℕ) -> (defm : m ≡ suc a ∷ suc a ∷ a ∷ suc a ∷ []) -> (p1 : m ≅ m1) -> (p2 : m ≅ m2) -> ∃ (λ mm -> (m1 ≃ mm) × (m2 ≃ mm))
  sb : (a b : ℕ) -> (suc (suc b) < a) -> (m m1 m2 : List ℕ) -> (defm : m ≡ a ∷ (suc b) ∷ b ∷ suc b ∷ []) -> (p1 : m ≅ m1) -> (p2 : m ≅ m2) -> ∃ (λ mm -> (m1 ≃ mm) × (m2 ≃ mm))
  bs : (a b : ℕ) -> (suc b < a) -> (m m1 m2 : List ℕ) -> (defm : m ≡ (suc a) ∷ a ∷ (suc a) ∷ b ∷ []) -> (p1 : m ≅ m1) -> (p2 : m ≅ m2) -> ∃ (λ mm -> (m1 ≃ mm) × (m2 ≃ mm))
  bb : (a : ℕ) -> (m m1 m2 : List ℕ) -> (defm : m ≡ suc a ∷ a ∷ suc a ∷ a ∷ suc a ∷ []) -> (p1 : m ≅ m1) -> (p2 : m ≅ m2) -> ∃ (λ mm -> (m1 ≃ mm) × (m2 ≃ mm))

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
    x ≃⟨ x≃y ⟩ y≃z  = trans x≃y y≃z

    _≃∎ : ∀ (x : List ℕ)
           -----
          → x ≃ x
    x ≃∎  =  refl

open ≃-Reasoning

postulate
    ++-unit : l ++ [] ≡ l

refl≡ : {l l' : List ℕ} -> (l ≡ l') -> l ≃ l'
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

≅-abs-r : {x : ℕ} -> [] ≅ (x ∷ []) -> ⊥
≅-abs-r (cancel≅ [] r .[] .(_ ∷ []) () defmf)
≅-abs-r (cancel≅ (x ∷ l) r .[] .(_ ∷ []) () defmf)
≅-abs-r (swap≅ x [] r .[] .(_ ∷ []) () defmf)
≅-abs-r (swap≅ x (x₁ ∷ l) r .[] .(_ ∷ []) () defmf)
≅-abs-r (braid≅ [] r .[] .(_ ∷ []) () defmf)
≅-abs-r (braid≅ (x ∷ l) r .[] .(_ ∷ []) () defmf)

empty-reduction : (m : List ℕ) -> ([] ≅ m) -> ⊥
empty-reduction m (cancel≅ [] r .[] m () defmf)
empty-reduction m (cancel≅ (x ∷ l) r .[] m () defmf)
empty-reduction m (swap≅ x [] r .[] m () defmf)
empty-reduction m (swap≅ x (x₁ ∷ l) r .[] m () defmf)
empty-reduction m (braid≅ [] r .[] m () defmf)
empty-reduction m (braid≅ (x ∷ l) r .[] m () defmf)

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
  len-mod2 : (m1 m2 : List ℕ) -> (m1 ≅ m2) -> (mod2 (length m1) ≡ mod2 (length m2))
  one-one-reduction : (n1 n2 : ℕ) -> ((n1 ∷ []) ≅ (n2 ∷ [])) -> n1 ≡ n2
  two-two-reduction : (a b1 b2 : ℕ) -> ((a ∷ a ∷ []) ≅ (b1 ∷ b2 ∷ [])) -> (b1 ≡ b2) × (a ≡ b1)
  len-nonincreasing : (m1 m2 : List ℕ) -> (m1 ≅ m2) -> (length m2 ≤ length m1)
  one-reduction : (m : List ℕ) -> ((n ∷ []) ≅ m) -> m ≡ (n ∷ [])
  cancel-reduction : (m : List ℕ) -> ((n ∷ n ∷ []) ≅ m) -> (m ≡ []) ⊎ (m ≡ (n ∷ n ∷ []))
  diamond-separate : {l r l' r' ml mr : List ℕ} -> (ml ≡ l' ++ r) -> (mr ≡ l ++ r') -> (l ≅ l') -> (r ≅ r') -> (ml ≅ (l' ++ r')) × (mr ≅ (l' ++ r'))

index-reduction-l : {m mf : List ℕ} -> (p : m ≅ mf) -> ℕ × ℕ
index-reduction-l (cancel≅ l r m mf defm defmf) = length l , 3 + length l
index-reduction-l (swap≅ x l r m mf defm defmf) = length l , 3 + length l
index-reduction-l (braid≅ l r m mf defm defmf) = length l , 4 + length l

diamond : (m1 m2 m3 : List ℕ) -> (m1 ≅ m2) -> (m1 ≅ m3) -> ∃ (λ m -> (m2 ≃ m) × (m3 ≃ m))
diamond m1 m2 m3 p q = {!!}
