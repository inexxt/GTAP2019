{-# OPTIONS --without-K #-}
{-# OPTIONS --allow-unsolved-metas #-}

module FinTypesEq where
    open import FinTypes
    open import General

    -- data _≡_ : {T : Type} -> Member T -> Member T -> Set where
    --     refl₁ : * ≡ *
    --     reflₓ : {X : Type} -> {Y : Type}
    --             -> {p11 : Member X}
    --             -> {p21 : Member X}
    --             -> {p12 : Member Y}
    --             -> {p22 : Member Y}
    --             -> p11 ≡ p21
    --             -> p12 ≡ p22
    --             -> (p11 , p12) ≡ (p21 , p22)
    --     reflₗ : {X : Type} -> {Y : Type}
    --             -> {x1 : Member X}
    --             -> {x2 : Member X}
    --             -> x1 ≡ x2
    --             -> _≡_ {X + Y} (left x1) (left x2)
    --     reflᵣ : {X : Type} -> {Y : Type}
    --             -> {y1 : Member Y}
    --             -> {y2 : Member Y}
    --             -> y1 ≡ y2
    --             -> (right {X} y1) ≡ (right {X} y2)
    --
    -- refl : {A : Type} -> (a : Member A) -> a ≡ a
    -- refl * = refl₁
    -- refl (a , b) = reflₓ (refl a) (refl b)
    -- refl {A + B} (left a) = reflₗ {A} {B} (refl a)
    -- refl {A + B} (right b) = reflᵣ {A} {B} (refl b)
    --
    -- J≡ : {A : Type} ->
    --     {a : Member A} ->
    --     (C : {x : Member A} -> (a ≡ x) -> Type) ->
    --     (p : Member (C {a} (refl a))) ->
    --     {x : Member A} ->
    --     ((q : (a ≡ x)) -> Member (C q))
    -- J≡ {a = *} C p q = {! q  !}
    -- J≡ {a = a , a₁} C p q = {!   !}
    -- J≡ {a = left a} C p q = {!   !}
    -- J≡ {a = right a} C p q = {!   !}
    --
    -- ≡-Id : {T : Type} -> {a b : Member T} -> (a ≡ b) -> (a == b)
    --
    -- intro-prod : {A B C : Type} -> ((Member C) -> (Member A)) -> ((Member C) -> (Member B)) -> (Member C) -> (Member (A × B))
    -- intro-prod f g c = (f c) , (g c)
    --
    -- elim-prod : {A B : Type} ->
    --             {C : (Member (A × B)) -> Type} ->
    --             (f : (a : (Member A)) ->
    --                  (b : (Member B)) ->
    --                  (Member (C (a , b)))) ->
    --             (p : Member (A × B)) -> Member (C p)
    -- elim-prod f (a , b) = f a b

    ==-+ : {A B : Type} -> {a1 a2 : Member A} -> (a1 == a2) -> (left a1) == (left a2)
    ==-+ p = ap left p

    -- TODO do it with ap
    ==-× : {A B : Type} -> {a1 a2 : Member A} -> {b1 b2 : Member B} -> (a1 == a2) -> (b1 == b2) -> (a1 , b1) == (a2 , b2)
    ==-× idp idp = idp
