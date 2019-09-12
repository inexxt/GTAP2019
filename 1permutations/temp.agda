{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Cubical.Core.Everything
open import Cubical.Foundations.Embedding
open import Cubical.Data.Nat
open import Cubical.Data.SumFin
open import Cubical.Relation.Nullary

variable
  ℓ : Level

Aut : Type ℓ -> Type _
Aut T = T ≃ T

Emb : Type ℓ → Type _
Emb T = Σ (T → T) isEmbedding

Inj : Type ℓ → Type _
Inj T = Σ (T → T) λ f → ∀ x y → f x ≡ f y → x ≡ y

thm : {n : ℕ} → Emb (Fin n) ≃ Aut (Fin n)
thm = isoToEquiv (iso {!!} {!!} {!!} {!!})

tr : {n : ℕ} -> (Fin n) -> ((Fin n) -> (Fin n))
tr {suc n} k p with discreteFin k p
tr {suc n} k p | yes p₁ = (inl tt)
tr {suc n} k p | no ¬p with discreteFin k (inl tt)
tr {suc n} k p | no ¬p | yes p₁ = k
tr {suc n} k p | no ¬p | no ¬p₁ = p

tr-tr : {n : ℕ} -> (k : Fin n) -> (b : Fin n) -> tr k (tr k b) ≡ b
tr-tr {suc n} k (inl x) = {!!}
tr-tr {suc n} k (fsuc x) = {!!}

tr-equiv : {n : ℕ} -> (Fin n) -> (Iso (Fin n) (Fin n))
tr-equiv {n} k = iso (tr k) (tr k) (tr-tr k) (tr-tr k)

g : {n : ℕ} -> Inj (Fin n) -> Aut (Fin n)
g {zero} (f , p) = isoToEquiv (iso f ⊥-elim (λ b → ⊥-elim b) λ a → ⊥-elim a)
g {suc n} (f , p) = let a = f (inl tt)
                    in  {!!}
