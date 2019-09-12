{-# OPTIONS --without-K #-}
{-# OPTIONS --allow-unsolved-metas #-}

module FinTypes where
    open import General
    open _≈_

    data Type : Set where
        𝟘   : Type
        𝟙   : Type
        _×_ : Type -> Type -> Type
        _+_ : Type -> Type -> Type

    data Member : Type -> Set where
        *     : Member 𝟙
        _,_     : {X : Type} -> {Y : Type} -> Member X -> Member Y -> Member (X × Y)
        left    : {X : Type} -> {Y : Type} -> Member X -> Member (X + Y)
        right   : {X : Type} -> {Y : Type} -> Member Y -> Member (X + Y)

    absurd𝟘 : {A : Set} -> Member 𝟘 -> A
    absurd𝟘 ()

    ×fst : {X : Type} -> {Y : Type} -> Member (X × Y) -> Member X
    ×fst (a , b) = a

    ×snd : {X : Type} -> {Y : Type} -> Member (X × Y) -> Member Y
    ×snd (a , b) = b
