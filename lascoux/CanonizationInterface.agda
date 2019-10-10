module CanonizationInterface where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; Σ; _×_; _,_; _,′_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)

open import General
open import Relation.Nullary
open import Data.Empty
open Relation.Binary.PropositionalEquality.≡-Reasoning

open ≤-Reasoning renaming (_∎ to _≤∎; begin_ to begin-≤_) hiding (_≡⟨_⟩_)
open import Arithmetic hiding (n)
open import Coxeter hiding (n; l)
open import Canonization hiding (n; l)

variable
    n : ℕ
    l : List ℕ

open ≃-Reasoning

F-canonize-p> : (n r i : ℕ)
                -> (0 < n)
                -> (r ≤ n)
                -> ((suc i) < n)
                -> (n < (suc i) + r)
                -> ((n ↓ r) ++ [ suc i ]) ≃ (i ∷ n ↓ r)
F-canonize-p> (suc n) (suc (suc r)) i pn (s≤s prn) (s≤s pin) (s≤s pirn) =
  let lmm : suc (n ∸ suc i) ≤ n
      lmm = ∸-implies-≤ {r = i} (≡-sym (∸-up pin))
      lm2 =
        begin
          i + suc (n ∸ suc i)
        ≡⟨ +-three-assoc {i} {1} {n ∸ suc i} ⟩
          suc i + (n ∸ suc i)
        ≡⟨ +-comm (suc i) (n ∸ suc i) ⟩
          (n ∸ suc i) + suc i
        ≡⟨ minus-plus {n} {suc i} {pin}⟩
          n
        ∎
      pin' : i ≡ n ∸ suc (n ∸ suc i)
      pin' = introduce-∸ lmm lm2

      n≤i+1+r : n ≤ (i + suc r)
      n≤i+1+r = ≤-down2
        (begin-≤
          suc n
         ≤⟨ pirn ⟩
          i + suc (suc r)
        ≤⟨ ≤-reflexive (+-three-assoc {i} {1} {suc r}) ⟩
          suc (i + suc r)
        ≤∎)

      pr2 : 1 ≤ suc i ∸ (n ∸ suc r)
      pr2 = introduce-∸-≤ (introduce-∸-≤l prn (≤-up n≤i+1+r)) (s≤s (introduce-∸-≤l prn n≤i+1+r))

      pirn' : n ∸ suc i + (suc i ∸ (n ∸ suc r)) ≤ n
      pirn' = eliminate-∸-≤ (introduce-∸-≤l (introduce-∸-≤l {n} {suc i} {r = suc r} prn (≤-up n≤i+1+r)) (≤-up-+ pin)) (∸-anti-≤ (∸-implies-≤ {r = n ∸ suc r} refl) pin)

      r1 = (suc n) ∸ (1 + (suc i))
      r2 = (1 + i) ∸ ((suc n) ∸ (suc (suc r)))

      call = canonize-p> (suc n) r1 r2 {i} pr2 (s≤s pirn') {pin'}

      lemma : suc r ≡ ((n ∸ suc i) + (suc i ∸ (n ∸ suc r)))
      lemma = {!!}

      left : n ∷ (n ↓ suc r) ++ suc i ∷ [] ≡ n ∷ (n ↓ (n ∸ suc i + (suc i ∸ (n ∸ suc r)))) ++ suc i ∷ []
      left = cong (λ l -> n ∷ l ++ [ suc i ]) (cong (λ k -> n ↓ k) lemma)

      right : (i ∷ n ∷ (n ↓ suc r)) ≡ (i ∷ n ∷ (n ↓ (n ∸ suc i + (suc i ∸ (n ∸ suc r)))))
      right = cong (λ l -> i ∷ n ∷ l) (cong (λ x -> n ↓ x) lemma)

  in
    ≃begin
      n ∷ (n ↓ suc r) ++ suc i ∷ []
    ≃⟨ refl≡ left ⟩
      _
    ≃⟨ call ⟩
      _
    ≃⟨ refl≡ (≡-sym right) ⟩
      i ∷ n ∷ (n ↓ suc r)
    ≃∎


-- TODO move the impossible cases up
-- r ≤ 1
F-canonize-p> (suc n) zero i pn prn (s≤s pin) (s≤s pirn) =
  let tt = begin-≤
             suc (suc n)
           ≤⟨ s≤s pirn ⟩
             suc (i + zero)
           ≤⟨ s≤s (≤-reflexive (+-comm i zero)) ⟩
             suc i
           ≤⟨ pin ⟩
             n
           ≤⟨ ≤-up (≤-reflexive refl) ⟩
             suc n
           ≤∎
  in  ⊥-elim (1+n≰n tt)
-- r ≤ 1
F-canonize-p> (suc n) (suc zero) i pn prn (s≤s pin) (s≤s pirn) =
  let tt = begin-≤
             suc (suc n)
           ≤⟨ s≤s pirn ⟩
             suc (i + 1)
           ≤⟨ s≤s (≤-reflexive (+-comm i 1)) ⟩
             suc (suc i)
           ≤⟨ s≤s pin ⟩
             suc n
           ≤∎
  in  ⊥-elim (1+n≰n tt)


F-canonize-p≡ : (n r i : ℕ)
                -> (0 < n)
                -> (r < n)
                -> ((suc i) < n)
                -> (((suc i) + 1 + r) ≡ n)
                -> ((n ↓ r) ++ [ suc i ]) ≃ (n ↓ (1 + r))
F-canonize-p≡ n r i pn prn pin pirn =
  let tx = begin
             (suc i) + suc r
           ≡⟨ cong suc (≡-sym (+-assoc i 1 r)) ⟩
             suc ((i + 1) + r)
           ≡⟨ pirn ⟩
             n
           ∎
  in  canonize-p≡ n r (suc i) pn prn (introduce-∸ prn tx)

F-canonize-p< : (n r i : ℕ)
                -> (0 < n)
                -> (r ≤ n)
                -> ((1 + i + r) < n)
                -> ((n ↓ r) ++ [ i ]) ≃ (i ∷ n ↓ r)
F-canonize-p< (suc n) zero i pn prn (s≤s pin) = refl
F-canonize-p< (suc zero) (suc r) zero pn prn (s≤s pin) = refl
F-canonize-p< (suc (suc n)) (suc r) i (s≤s pn) (s≤s prn) (s≤s pin) =
  let 1+i+r≤n : 1 + i + r ≤ n
      1+i+r≤n =
        begin-≤
          suc (i + r)
        ≤⟨ ≤-reflexive (≡-sym (+-three-assoc {i} {1} {r})) ⟩
          i + suc r
        ≤⟨ ≤-down2 pin ⟩
          n
        ≤∎
      rec = F-canonize-p< (suc n) r i (s≤s z≤n) prn (s≤s 1+i+r≤n)

      1+i≤n : 1 + i ≤ n
      1+i≤n = ≤-down-+ 1+i+r≤n
  in
    ≃begin
      suc n ∷ (suc n ↓ r) ++ i ∷ []
    ≃⟨ prepend (suc n) rec ⟩
      suc n ∷ i ∷ (suc n ↓ r)
    ≃⟨ ++-respects (swap (s≤s 1+i≤n)) refl ⟩
      i ∷ suc n ∷ (suc n ↓ r)
    ≃∎
