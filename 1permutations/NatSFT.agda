{-# OPTIONS --without-K #-}
{-# OPTIONS --allow-unsolved-metas #-}

module NatSFT where
    --- Nat isomorphisms, only for manual testing, not to be used in the core

    open import FinTypes
    open import StandardFinTypes
    open import Agda.Builtin.Sigma
    open import Data.Product using (∃)
    open import Data.Nat using (ℕ ; _<_)
    open ℕ

    natToSft : (n : ℕ) -> ∃ (λ t -> StandardFinType t)
    natToSft zero = 𝟘 , Fin0
    natToSft (suc n) = let (t , p) = natToSft n
                       in  t + 𝟙 , FinS p

    sftToNat : {T : Type} -> StandardFinType T -> ℕ
    sftToNat Fin0 = zero
    sftToNat (FinS n) = suc (sftToNat n)

    natToMemberSft : {T : Type} -> (n : ℕ) -> (k : ℕ) -> {p : k < n} -> Member ((natToSft n) .fst)
    natToMemberSft (suc n) zero = (right One)
    natToMemberSft (suc n) (suc k) = left (natToMemberSft n k)
