module _ where

open import Size

open import Data.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Int : {i : Size} -> Set where
  Pos : (x : ℕ) -> Int
  Neg : (x : ℕ) -> Int

-- _⊕_ : Int -> Int -> Int
-- Pos x ⊕ Pos y = Pos (x + y)
-- Neg x ⊕ Neg y = Neg (x + y)
-- Pos x ⊕ Neg zero = Pos x
-- Pos zero ⊕ Neg y = Neg y
-- Pos (suc x) ⊕ Neg (suc y) = (Pos x) ⊕ (Neg y)
-- --- problematic call
-- Neg x ⊕ Pos y = (Pos y) ⊕ (Neg x)

-- data Int : {i : Size} -> Set where
--   Pos : (x : ℕ) -> Int
--   Neg : (x : ℕ) -> Int

ord : Int -> ℕ
ord (Pos _) = 0
ord (Neg _) = 1

_⊕_ : (x : Int) -> {ord x : ℕ} -> Int -> Int
Pos x ⊕ Pos y = Pos (x + y)
Neg x ⊕ Neg y = Neg (x + y)
Pos x ⊕ Neg zero = Pos x
Pos zero ⊕ Neg y = Neg y
Pos (suc x) ⊕ Neg (suc y) = _⊕_ (Pos x) {0} (Neg y)
--- problematic call
_⊕_ (Neg x) {1} (Pos y) = _⊕_ (Pos y) {0} (Neg x)
