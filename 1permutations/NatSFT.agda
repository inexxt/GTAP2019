{-# OPTIONS --without-K #-}
{-# OPTIONS --allow-unsolved-metas #-}

module NatSFT where
    --- Nat isomorphisms, only for manual testing, not to be used in the core

    open import FinTypes
    open import StandardFinTypes
    open import Agda.Builtin.Sigma
    open import Data.Product using (∃)
    open import Data.Nat using (ℕ ; _<_)


    natToSft : (n : ℕ) -> ∃ (λ t -> StandardFinType t)
    natToSft ℕ.zero = 𝟘 , Fin0
    natToSft (ℕ.suc n) = let (t , p) = natToSft n
                       in  t + 𝟙 , FinS p

    sftToNat : {T : Type} -> StandardFinType T -> ℕ
    sftToNat Fin0 = ℕ.zero
    sftToNat (FinS n) = ℕ.suc (sftToNat n)

    natToMemberSft : {T : Type} -> (n : ℕ) -> (k : ℕ) -> {p : k < n} -> Member ((natToSft n) .fst)
    natToMemberSft (ℕ.suc n) ℕ.zero = (right *)
    natToMemberSft (ℕ.suc n) (ℕ.suc k) = left (natToMemberSft n k)
