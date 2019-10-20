{-# OPTIONS --allow-unsolved-metas #-}

module CriticalPairs where

open import Data.List
open import Data.Nat
open import Data.List.Properties
open import Data.Nat.Properties
open import Data.Product using (∃; _×_; _,_)
open import General
open import Relation.Nullary
open import Data.Empty
open import Data.Sum hiding (swap)
open import Data.Bool hiding (_<_; _≤_)
open import Data.Bool.Properties hiding (≤-reflexive; ≤-trans)

open import Arithmetic hiding (n)
open import Diamond hiding (n; l)
open ≤-Reasoning renaming (begin_ to ≤-begin_; _∎ to ≤∎) hiding (_≡⟨_⟩_; _≡⟨⟩_)


open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst) renaming (trans to ≡-trans; sym to ≡-sym)

variable
  n : ℕ
  l : List ℕ

∷-≡1 : {n1 n2 : ℕ} -> {l1 l2 : List ℕ} -> (n1 ∷ l1 ≡ n2 ∷ l2) -> (n1 ≡ n2)
∷-≡1 refl = refl

∷-≡2 : {n1 n2 : ℕ} -> {l1 l2 : List ℕ} -> (n1 ∷ l1 ≡ n2 ∷ l2) -> (l1 ≡ l2)
∷-≡2 refl = refl

force-x : (a x : ℕ) -> (l1 l2 : List ℕ) -> (a ∷ a ∷ a ∷ [] ≡ l1 ++ x ∷ l2) -> (a ≡ x)
force-x a .a [] .(a ∷ a ∷ []) refl = refl
force-x a .a (.a ∷ []) .(a ∷ []) refl = refl
force-x a .a (.a ∷ .a ∷ []) .[] refl = refl
force-x a x (x₁ ∷ x₂ ∷ x₃ ∷ []) l2 ()
force-x a x (x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ l1) l2 ()

abs-suc : {A : Set} -> suc n < n -> A
abs-suc {n} p = ⊥-elim (1+n≰n (≤-down p))

abs-≤ : {A : Set} -> n < n -> A
abs-≤ {n} p = ⊥-elim (1+n≰n p)

2-1++ : {a b c : ℕ} -> (l r : List ℕ) -> a ∷ b ∷ [] ≡ c ∷ l ++ r -> length r ≤ 1
2-1++ [] .(_ ∷ []) refl = s≤s z≤n
2-1++ (x ∷ []) .[] refl = z≤n

2-++1 : {a b c : ℕ} -> (l r : List ℕ) -> a ∷ b ∷ [] ≡ l ++ c ∷ r -> length l ≤ 1
2-++1 [] .(_ ∷ []) refl = z≤n
2-++1 (x ∷ []) .[] refl = s≤s z≤n
2-++1 (x ∷ x₁ ∷ []) r ()

postulate
  3-++2 : {a b c d e : ℕ} -> (l r : List ℕ) -> a ∷ b ∷ c ∷  [] ≡ l ++ d ∷ e ∷ r -> length l ≤ 1
  3-2++ : {a b c d e : ℕ} -> (l r : List ℕ) -> a ∷ b ∷ c ∷  [] ≡ d ∷ e ∷ l ++ r -> length r ≤ 1


≅-2 : {m1 m2 : List ℕ} -> m1 ≅ m2 -> 2 ≤ length m1
≅-2 cancel≅ = s≤s (s≤s z≤n)
≅-2 (swap≅ x) = s≤s (s≤s z≤n)
≅-2  braid≅ = s≤s (s≤s z≤n)
≅-2  (respects=r l nl {r} p deflr deflr') rewrite deflr rewrite (length-++ l {r}) =
  let rec = ≅-2 p
  in  ≤-up-+ rec
≅-2  (respects=l {l} r nr p deflr defl'r) rewrite deflr rewrite (length-++ l {r}) =
  let rec = ≅-2 p
  in  ≤-up-r-+ rec

--- critical pairs

cc : (a : ℕ) -> (m m1 m2 : List ℕ) -> (defm : m ≡ a ∷ a ∷ a ∷ []) -> (p1 : m ≅ m1) -> (p2 : m ≅ m2) -> ∃ (λ mm -> (m1 ≃ mm) × (m2 ≃ mm))
-- trivial, solved with two-two-reduction
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (respects=r .(x ∷ l) (nonempty-l x l) p1 deflr deflr') (respects=r .(x₁ ∷ l₁) (nonempty-l x₁ l₁) p2 deflr₁ deflr'') = {!!}
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (respects=l .(x ∷ l) (nonempty-l x l) p1 deflr defl'r) (respects=l .(x₁ ∷ l₁) (nonempty-l x₁ l₁) p2 deflr₁ defl'r₁) = {!!}
-- interesting - this is the case when i do (a(aa) -> a; (aa)a -> a)
cc _ .(x₁ ∷ x₁ ∷ x₁ ∷ []) m1 m2 refl (respects=r (_ ∷ []) (nonempty-l _ .[]) cancel≅ refl deflr') (respects=l {.x₁ ∷ .x₁ ∷ []} (x₁ ∷ []) (nonempty-l .x₁ .[]) cancel≅ refl defl'r) rewrite (defl'r) rewrite deflr' = [ x₁ ] , (refl , refl)

-- false
cc _ .(x₁ ∷ x₁ ∷ x₁ ∷ []) m1 m2 refl (respects=r (_ ∷ []) (nonempty-l _ .[]) cancel≅ refl deflr') (respects=l {.x₁ ∷ .x₁ ∷ []} (x₁ ∷ []) (nonempty-l .x₁ .[]) (swap≅ x) refl defl'r) = abs-suc x
cc _ .(_ ∷ _ ∷ _ ∷ []) .(_ ∷ []) m2 refl (respects=r (_ ∷ []) (nonempty-l _ .[]) cancel≅ refl refl) (respects=l {_ ∷ _ ∷ []} (_ ∷ []) (nonempty-l _ .[]) (respects=r (x ∷ l) (nonempty-l .x .l) {r} p2 deflr deflr'') refl defl'r) =
  let 2≤lenr : 2 ≤ length r
      2≤lenr = ≅-2 p2

      lenr≤1 : length r ≤ 1
      lenr≤1 = 2-1++ l r deflr
  in  abs-≤ (≤-trans 2≤lenr lenr≤1)
cc _ .(_ ∷ _ ∷ _ ∷ []) .(_ ∷ []) m2 refl (respects=r (_ ∷ []) (nonempty-l _ .[]) cancel≅ refl refl) (respects=l {_ ∷ _ ∷ []} (_ ∷ []) (nonempty-l _ .[]) (respects=l {l} (x ∷ r) (nonempty-l .x .r) p2 deflr defl'r₁) refl defl'r) =
  let 2≤lenl : 2 ≤ length l
      2≤lenl = ≅-2 p2

      lenl≤1 : length l ≤ 1
      lenl≤1 = 2-++1 l r deflr
  in  abs-≤ (≤-trans 2≤lenl lenl≤1)

-- false
cc _ .(x₁ ∷ x₁ ∷ x₁ ∷ []) m1 m2 refl (respects=r (_ ∷ []) (nonempty-l _ .[]) (swap≅ x) refl deflr') (respects=l {.x₁ ∷ .x₁ ∷ []} (x₁ ∷ []) (nonempty-l .x₁ .[]) p2 refl defl'r) = abs-suc x
cc _ .(x₁ ∷ x₁ ∷ x₁ ∷ []) m1 m2 refl (respects=r (_ ∷ []) (nonempty-l _ .[]) (respects=r .(x ∷ l) (nonempty-l x l) {r} p1 deflr deflr'') refl deflr') (respects=l {.x₁ ∷ .x₁ ∷ []} (x₁ ∷ []) (nonempty-l .x₁ .[]) p2 refl defl'r) =
  let 2≤lenr : 2 ≤ length r
      2≤lenr = ≅-2 p1

      lenr≤1 : length r ≤ 1
      lenr≤1 = 2-1++ l r deflr
  in  abs-≤ (≤-trans 2≤lenr lenr≤1)
cc _ .(x₁ ∷ x₁ ∷ x₁ ∷ []) m1 m2 refl (respects=r (_ ∷ []) (nonempty-l _ .[]) (respects=l {l} .(x ∷ r) (nonempty-l x r) p1 deflr defl'r₁) refl deflr') (respects=l {.x₁ ∷ .x₁ ∷ []} (x₁ ∷ []) (nonempty-l .x₁ .[]) p2 refl defl'r) =
  let 2≤lenl : 2 ≤ length l
      2≤lenl = ≅-2 p1

      lenl≤1 : length l ≤ 1
      lenl≤1 = 2-++1 l r deflr
  in  abs-≤ (≤-trans 2≤lenl lenl≤1)

-- false
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (respects=r (x ∷ x₂ ∷ r) (nonempty-l .x .(x₂ ∷ r)) {r₂} p1 deflr deflr') (respects=l {l} (x₁ ∷ r₁) (nonempty-l .x₁ .r₁) p2 deflr₁ defl'r) =
  let 2≤lenr : 2 ≤ length r₂
      2≤lenr = ≅-2 p1

      lenr≤1 : length r₂ ≤ 1
      lenr≤1 = 3-2++ r r₂ deflr
  in  abs-≤ (≤-trans 2≤lenr lenr≤1)
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (respects=r (x ∷ []) (nonempty-l .x .[]) p1 deflr deflr') (respects=l {l} (x₁ ∷ x₂ ∷ r) (nonempty-l .x₁ .(x₂ ∷ r)) p2 deflr₁ defl'r) =
  let 2≤lenl : 2 ≤ length l
      2≤lenl = ≅-2 p2

      lenl≤1 : length l ≤ 1
      lenl≤1 = 3-++2 l r deflr₁
  in  abs-≤ (≤-trans 2≤lenl lenl≤1)


-- interesting - this is the case when i do ((aa)a -> a; a(aa) -> a)
cc a .(a ∷ a ∷ a ∷ []) m1 m2 refl (respects=l r nr p1 deflr defl'r) (respects=r l nl p2 deflr₁ deflr') =
  let rec , rec1 , rec2 = cc a (a ∷ a ∷ a ∷ []) m2 m1 refl (respects=r l nl p2 deflr₁ deflr') (respects=l r nr p1 deflr defl'r)
  in  rec , rec2 , rec1

-- absurd
cc _ .(_ ∷ _ ∷ _ ∷ []) m1 m2 refl (respects=r (_ ∷ []) (nonempty-l _ .[]) p1 refl deflr') (respects=l {x ∷ x₂ ∷ x₃ ∷ []} (x₁ ∷ []) (nonempty-l .x₁ .[]) p2 () defl'r)
cc _ .(_ ∷ _ ∷ _ ∷ []) m1 m2 refl (respects=r (_ ∷ []) (nonempty-l _ .[]) p1 refl deflr') (respects=l {x ∷ x₂ ∷ x₃ ∷ x₄ ∷ l} (x₁ ∷ []) (nonempty-l .x₁ .[]) p2 () defl'r)
