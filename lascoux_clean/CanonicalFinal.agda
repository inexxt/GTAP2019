{-# OPTIONS --allow-unsolved-metas --without-K #-}
module _ where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (Σ; ∃; _×_; _,_)

open import Relation.Nullary
open import Data.Empty
open import Data.Sum hiding (swap)
open import Data.Bool hiding (_<_; _≤_; _≟_; _<?_)
open import Data.Bool.Properties hiding (≤-reflexive; ≤-trans; _≟_; _<?_)
open import Function

open import Arithmetic hiding (n)
open import Lists
open import Compact hiding (n; l)
open import ImpossibleLemmas
open import SwapLemmas
open import Canonical
open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to ≤∎) hiding (_≡⟨_⟩_; _≡⟨⟩_)


open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)

open ≅*-Reasoning
open Relation.Binary.PropositionalEquality.≡-Reasoning
open _⊎_


-- Canonical proper represents canonicals with a non-empty last sequence
data CanonicalProper : (n : ℕ) -> Set where
  CanZ : CanonicalProper 0
  CanS : {n : ℕ} -> (l : Canonical n) -> {r : ℕ} -> (r ≤ n) -> CanonicalProper (suc n)


immersionProper : {n : ℕ} -> CanonicalProper n -> List ℕ
immersionProper {zero} CanZ = []
immersionProper {suc n} (CanS l {r} r≤n) = (immersion l) ++ (((suc n) ∸ (1 + r)) ↓ (1 + r))

always-reduces : (n k x : ℕ) -> (x ≤ k + n) -> (∃ (λ mf -> (n ↓ (1 + k) ++ [ x ]) ≅* mf)) ⊎ (suc x ≡ n)
always-reduces n k x px with suc x <? n
... | yes r = inj₁ (_ , (long-swap<-lr x n (1 + k) [] [] r))
... | no r with suc x ≟ n
... | yes rr = inj₂ rr
... | no rr with x ≟ n
... | no rrr = {!!}
always-reduces n zero x px | no r | no rr | yes rr2 rewrite rr2 = inj₁ (_ , (cancel [] []))
always-reduces n (suc k) x px | no r | no rr | yes rr2 with (always-reduces n k x (≤-trans (≤-reflexive rr2) (≤-up-+ rrr)))
always-reduces n (suc k) x px | no r | no rr | yes rr2 | inj₁ (rec-m , rec-p) = inj₁ (_ , l++ [ suc (k + n) ] rec-p)
always-reduces n (suc k) x px | no r | no rr | yes rr2 | inj₂ y = inj₂ y

lemma : (n r x : ℕ) -> (r ≤ n) -> (cl : Canonical n) -> (f : (mf : List ℕ) -> ((immersion {n} cl ++ ((n ∸ r) ↓ (1 + r))) ++ x ∷ []) ≅* mf -> ⊥) -> (n < x) ⊎ ((x ≡ n ∸ (1 + r)) × (suc r ≤ n))
lemma n r x pnr cl f with n <? x
... | yes q = inj₁ q
... | no q with  always-reduces (n ∸ r) r x (≤-trans (≤-down2 (≰⇒> q)) (≤-reflexive (≡-sym (plus-minus pnr))))
... | inj₁ (ar-m , ar-p) =
  let red =
        ≅*begin
          (immersion cl ++ ((n ∸ r) ↓ (1 + r))) ++ x ∷ []
        ≅*⟨ refl≡ (++-assoc (immersion cl) _ _) ⟩
          immersion cl ++ ((n ∸ r) ↓ (1 + r)) ++ x ∷ []
        ≅*⟨ l++ (immersion cl) ar-p ⟩
          _
        ≅*∎
  in  ⊥-elim (f _ red)
... | inj₂ qq = inj₂ ({!!} , {!!})

canonical-final≅ : (m : List ℕ) -> (f : (mf : List ℕ) -> (rev m ≅* mf) -> ⊥) -> ∃ (λ n -> ∃ (λ cl -> immersion {n} cl ≡ rev m))
canonical-final≅ [] f = zero , CanZ , refl
canonical-final≅ (x ∷ m) f with (canonical-final≅ m (λ mf red → f (mf ++ [ x ]) (++r [ x ] red)))
canonical-final≅ (x ∷ m) f | zero , CanZ , snd rewrite (≡-sym snd) = _ , canonical-append CanZ x z≤n
canonical-final≅ (x ∷ m) f | _ , CanS fst {zero} x₁ , snd = {!!} -- TODO this requires changing the signature to return canonicalProper instead of just canonical - then it will be impossible
canonical-final≅ (x ∷ m) f | _ , CanS {n₁} fst {suc r} x₁ , snd  with lemma n₁ r x (≤-down2 x₁) fst (λ mf mf-abs → f mf (subst (λ e -> (e ++ [ x ]) ≅* mf) snd mf-abs))
canonical-final≅ (x ∷ m) f | _ , CanS fst {suc r} x₁ , snd | inj₁ x₂ =
  let rec-m , rec-p = canonical-append (CanS fst {suc r} x₁) x x₂
  in  _ , rec-m , (≡-trans rec-p (start+end snd refl))
canonical-final≅ (x ∷ m) f | _ , CanS {n} fst {suc r} x₁ , snd | inj₂ (fst₁ , snd₁) =
  let tt =
        begin
          immersion fst ++ suc (r + (n ∸ suc r)) ∷ ((n ∸ suc r) ↓ (1 + r))
        ≡⟨ start+end (refl {x = immersion fst}) (head+tail (≡-trans (plus-minus snd₁) (≡-sym (plus-minus (≤-down snd₁)))) (≡-sym (++-↓ (n ∸ suc r) r))) ⟩
          immersion fst ++ r + (n ∸ r) ∷ (suc (n ∸ suc r) ↓ r) ++ n ∸ suc r ∷ []
        ≡⟨ start+end (refl {x = immersion fst}) (head+tail refl (start+end (cong (λ e -> e ↓ r) {!!}) (cong [_]  (≡-sym fst₁)))) ⟩
          immersion fst ++ r + (n ∸ r) ∷ ((n ∸ r) ↓ r) ++ x ∷ []
        ≡⟨ ≡-sym (++-assoc (immersion fst) _ [ x ]) ⟩
          (immersion fst ++ r + (n ∸ r) ∷ ((n ∸ r) ↓ r)) ++ x ∷ []
        ≡⟨ start+end snd (refl {x = [ x ]}) ⟩
          rev m ++ x ∷ []
        ∎
  in _ , ((CanS fst {suc (suc r)} (s≤s snd₁)) , tt)
