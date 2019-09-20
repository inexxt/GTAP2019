{-# OPTIONS --without-K #-}

module SortingNat where
  open import Data.Empty
  open import Data.Nat
  open import Relation.Nullary
  open import Data.Sum
  open import Function
  open import Data.List
  import Relation.Binary.PropositionalEquality as PE
  open PE using (_≡_)

  absurd : {x y : ℕ} -> (¬ x ≤ y) -> (¬ y ≤ x) -> ⊥
  absurd {zero} {zero} p q = q z≤n
  absurd {zero} {suc y} p q = p z≤n
  absurd {suc x} {zero} p q = q z≤n
  absurd {suc x} {suc y} p q = absurd (λ z → p (s≤s z)) (λ z → q (s≤s z))

  _≤??_ : (x y : ℕ) → (x ≤ y ⊎ y ≤ x)
  x ≤?? y with (x ≤? y)
  (x ≤?? y) | yes p = inj₁ p
  (x ≤?? y) | no ¬p with (y ≤? x)
  (x ≤?? y) | no ¬p | yes p = inj₂ p
  (x ≤?? y) | no ¬p | no ¬p₁ =  ⊥-elim $ absurd ¬p ¬p₁

  open import Data.Nat.Properties using (≤-isPartialOrder)
  open import SortingAlgorithm ≤-isPartialOrder _≤??_
  open import SortedList ≤-isPartialOrder

  showSort : List ℕ -> List ℕ
  showSort xs = let ss = insertion-sort xs
                    ss' = Sorted-to-Sorted' ss in
                    Sorted'.list ss'

  test : (showSort $ 5 ∷ 3 ∷ 2 ∷ 4 ∷ 1 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
  test = _≡_.refl
