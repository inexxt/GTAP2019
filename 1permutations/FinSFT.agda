{-# OPTIONS --without-K #-}
{-# OPTIONS --allow-unsolved-metas #-}

module FinSFT where
    open import FinTypes
    open import StandardFinTypes
    open import Data.Nat using (ℕ)
    open import Data.Fin
    open import NatSFT
    open import General
    open import FinTypesEq
    open ℕ

    myFinToFin : {T : Type} -> {t : StandardFinType T} -> (Member T) -> Fin (sftToNat t)
    myFinToFin {t = FinS t} (left x) = suc (myFinToFin x)
    myFinToFin {t = FinS t} (right *) = zero

    -- finToMyFin : {n : ℕ} -> (Fin n) -> Member (getTypeFromStandardType (proj₂ (natToSft n)))
    -- finToMyFin {suc n} zero = right *
    -- finToMyFin {suc n} (suc k) = left (finToMyFin k)

    arr : {T : Type} -> {t : StandardFinType T} -> Fin (sftToNat t) → Member T
    arr {t = FinS t} zero = right *
    arr {t = FinS t} (suc x) = left (arr x)

    e1 : {T : Type} -> {t : StandardFinType T} -> (a : Fin (sftToNat t)) → myFinToFin (arr a) == a
    e1 {𝟘} {Fin0} ()
    e1 {A + 𝟙} {FinS t} zero = idp
    e1 {A + 𝟙} {FinS t} (suc a) = ap suc (e1 a)

    e2 : {T : Type} -> {t : StandardFinType T} -> (b : Member T) → arr (myFinToFin b) == b
    e2 {A + 𝟙} {FinS t} (left a) = let e2a = e2 a in {!!}
    e2 {A + 𝟙} {FinS t} (right *) = idp

    finfin : {T : Type} -> {t : StandardFinType T} -> Fin (sftToNat t) ≈ (Member T)
    finfin = Equiv arr myFinToFin e1 e2

    -- finfin {_} {FinS t} = Equiv {!!} myFinToFin {!!} {!!}
                          -- let x = λ k -> p₂ (proj₂ (finToMyFin k)) in
                          -- Equiv (λ _ → right *) myFinToFin {!   !} {!   !}
