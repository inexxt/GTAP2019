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

abs-list : ([] ≡ l ++ [ n ]) -> ⊥
abs-list {[]} ()
abs-list {x ∷ l} ()

cut-last : {l1 l2 : List ℕ} -> {x1 x2 : ℕ} -> (l1 ++ [ x1 ] ≡ l2 ++ [ x2 ]) -> (l1 ≡ l2)
cut-last {[]} {[]} p = refl
cut-last {[]} {x ∷ []} ()
cut-last {[]} {x ∷ x₁ ∷ l2} ()
cut-last {x ∷ []} {[]} ()
cut-last {x ∷ x₁ ∷ l1} {[]} ()
cut-last {x ∷ l1} {x₁ ∷ l2} p = head+tail (cut-tail p) (cut-last (cut-head p))

cut-last-canonical : (x : ℕ) -> (cl : Canonical n) -> (immersion cl ≡ l ++ [ x ]) -> ∃ (λ nf -> ∃ (λ clf -> immersion {nf} clf ≡ l))
cut-last-canonical {zero} {l} x CanZ pp = ⊥-elim (abs-list pp)
cut-last-canonical {suc n} {l} x (CanS cl {zero} pr) pp = cut-last-canonical x cl (≡-trans (≡-sym ++-unit) pp)
cut-last-canonical {suc n} {l} x (CanS cl {suc r} pr) pp =
  let p1 =
        begin
          (immersion cl ++ (suc (n ∸ r) ↓ r)) ++ n ∸ r ∷ []
        ≡⟨ ++-assoc (immersion cl) (suc (n ∸ r) ↓ r) (n ∸ r ∷ []) ⟩
          immersion cl ++ (suc (n ∸ r) ↓ r) ++ [ n ∸ r ]
        ≡⟨ start+end (refl {x = immersion cl}) (++-↓ (n ∸ r) r) ⟩
          immersion cl ++ ((n ∸ r) ↓ (1 + r))
        ≡⟨ pp ⟩
          l ++ [ x ]
        ∎
      p2 =
        begin
          immersion cl ++ ((suc n ∸ r) ↓ r)
        ≡⟨ start+end (refl {x = immersion cl}) (cong (λ e -> e ↓ r) {!!}) ⟩
          immersion cl ++ (suc (n ∸ r) ↓ r)
        ≡⟨ cut-last p1 ⟩
          l
        ∎
  in  _ , (CanS cl {r} (≤-down pr)) , p2

is-canonical? : (m : List ℕ) -> Dec (∃ (λ nf -> ∃ (λ cl -> immersion {nf} cl ≡ rev m)))
is-canonical? [] = yes (_ , (CanZ , refl))
is-canonical? (x ∷ m) with is-canonical? m
... | yes (_ , CanZ , pp) rewrite (≡-sym pp) =
  let (clf , clf-p) = canonical-lift x z≤n CanZ
  in  yes (_ , canonical-append CanZ x z≤n)
... | yes (_ , CanS {n} cl q , pp) with n <? x
... | no  p = no λ {(_ , cl , pp) → p (cut-last-canonical x cl pp) }


everything-to-canonical : (m : List ℕ) -> ∃ (λ n -> ∃ (λ cl -> immersion {n} cl ≡ rev m))
everything-to-canonical m = {!!}
