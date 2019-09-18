{-# OPTIONS --cubical --without-K #-}

module Groups where
    -- open import Cubical.Core.Everything hiding (_≡_)
    open import Cubical.Foundations.Prelude
    open import Cubical.Core.Everything using (isEquiv ; _≃_)
    open import Cubical.Core.Primitives hiding ( _≡_ )
    open import Cubical.Core.Id hiding (_≡_)
    open import Cubical.Foundations.Equiv
    open import Cubical.Data.Nat
    open import Cubical.Data.Fin

    open import Level

    variable
      ℓ : Level

    data S3 : Set0 where
        * : S3
        e1 : * ≡ *
        e2 : * ≡ *
        b1 : e2 ∙ e1 ∙ e2 ≡ e1 ∙ e2 ∙ e1
        i1 : e1 ∙ e1 ≡ refl
        i2 : e2 ∙ e2 ≡ refl

    data F3 {ℓ} : Set ℓ where
        a1 : F3
        a2 : F3
        a3 : F3

    data 𝟘 {ℓ} : Set ℓ where

    data 𝟙 {ℓ} : Set ℓ where
        one : 𝟙

    ap : {A B : Set ℓ} -> {x y : A} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
    ap {x = x} f p = J (λ zz _ → f x ≡ f zz) refl p

    id : {A : Set ℓ} -> A -> A
    id a = a

    one≠zero : 𝟙 ≡ 𝟘 -> 𝟘
    one≠zero p = transport p one

    𝟘-elim : {A : Set ℓ} -> 𝟘 -> A
    𝟘-elim ()

    absurd : {A : Set ℓ} -> a1 ≡ a2 -> A
    absurd p =  𝟘-elim (one≠zero q)
        where
            f : F3 -> Set0
            f a1 = 𝟘
            f a2 = 𝟙
            f a3 = 𝟙

            q : 𝟙 ≡ 𝟘
            q = ap f {!p!}

    proj1≡ : {A : Set} -> {B : A -> Set} -> {a1 a2 : A} -> {b1 : B a1} -> {b2 : B a2} -> (a1 Σ., b1) ≡ (a2 Σ., b2) -> (a1 ≡ a2)
    proj1≡ p = ap Σ.fst p

    p : (f : F3 -> F3) -> isEquiv f -> * ≡ *
    p f e with f a1 , f a2 , f a3
    p f record { equiv-proof = equiv-proof } | a1 , a1 , _  = let a , b = equiv-proof a1
                                                                  t1 = b (a1 , {!!})
                                                                  t2 = b (a2 , {!!})
                                                                  abs = (sym t1) ∙ t2 in
                                                              absurd (proj1≡ abs)
    p f record { equiv-proof = equiv-proof } | _  , a1 , a1 = {!   !}
    p f record { equiv-proof = equiv-proof } | a1 , _  , a1 = {!   !}
    p f record { equiv-proof = equiv-proof } | a2 , a2 , _  = {!  !}
    p f record { equiv-proof = equiv-proof } | _  , a2 , a2 = {!   !}
    p f record { equiv-proof = equiv-proof } | a2 , _  , a2 = {!   !}
    p f record { equiv-proof = equiv-proof } | a3 , a3 , _  = {!  !}
    p f record { equiv-proof = equiv-proof } | _  , a3 , a3 = {!   !}
    p f record { equiv-proof = equiv-proof } | a3 , _  , a3 = {!   !}
    ... | a1 , a2 , a3 = refl
    ... | a1 , a3 , a2 =  e2
    ... | a2 , a1 , a3 =  e1
    ... | a2 , a3 , a1 =  e1 ∙ e2
    ... | a3 , a1 , a2 =  e2 ∙ e1
    ... | a3 , a2 , a1 =  e1 ∙ e2 ∙ e1

    proof : (F3 ≃ F3) ≃ (* ≡ *)
    proof = (λ { (f , e) → p f e}) , record { equiv-proof = eqv }
        where
            eqv = λ y → ? , ?

    data Sn {n : ℕ}: Set where
        Per : ((k : Fin n) -> (Fin (ℕ.suc (toℕ k)))) -> Sn

    -- 𝟛 : Set
    -- 𝟛 = Sn {3}

    -- -- x is a (12) cycle
    -- x : 𝟛
    -- x = Per (λ { zero → # 0 ;
    --             (suc zero) →  # 0 ;
    --             (suc (suc zero)) →  # 2  })
