{-# OPTIONS --without-K #-}
{-# OPTIONS --allow-unsolved-metas #-}

module FinTypesEquiv where
    open import General
    open import FinTypes
    open _≈_

    _≋_ : (A : Type) -> (B : Type) -> Set
    A ≋ B = _≈_ (Member A) (Member B)

    id : {A : Set} -> A -> A
    id x = x

    --- Reflexivity

    Equiv-reflex : {A : Type} -> A ≋ A
    Equiv-reflex = Equiv (λ z → z) (λ z → z) (λ a → idp) (λ b → idp)

    --- Symmetry

    Equiv-symmetry : {A B : Type} -> A ≋ B -> B ≋ A
    Equiv-symmetry (Equiv f g e1 e2) = Equiv g f e2 e1


    --- Composition

    Equiv-composition : {A B C : Type} -> (A ≋ B) -> (B ≋ C) -> (A ≋ C)
    Equiv-composition {A} {B} {C} (Equiv fab fba eab eba) (Equiv fbc fcb ebc ecb) =
        let a-c-a a = ap fba (ebc (fab a))
            c-a-c c = ap fbc (eba (fcb c))
        in  Equiv (fbc ∘ fab)
                  (fba ∘ fcb)
                  (λ a -> comp (a-c-a a) (eab a))
                  (λ c -> comp (c-a-c c) (ecb c))

    --- × Unit

    ×-embed𝟙 : {A : Type} -> Member A -> Member (𝟙 × A)
    ×-embed𝟙 a = (* , a)

    ×-project𝟙 : {A : Type} -> Member (𝟙 × A) -> Member A
    ×-project𝟙 (* , a) = a

    ×-unit : {A B : Type} -> (𝟙 × A) ≋ A
    ×-unit = Equiv ×-project𝟙 ×-embed𝟙 (λ {(* , a) → idp}) λ b → idp

    --- × Commutativity

    ×-swap : {A B : Type} -> Member (A × B) -> Member (B × A)
    ×-swap (a , b) = (b , a)

    lemma-×-swap : {A B : Type} -> (ab : Member (A × B)) -> (×-swap (×-swap ab)) == ab
    lemma-×-swap (a , b) = idp

    ×-commut : {A B : Type} -> (A × B) ≋ (B × A)
    ×-commut = Equiv ×-swap ×-swap lemma-×-swap lemma-×-swap


    --- × Associativity

    r-×assc : {A B C : Type} -> Member (A × (B × C)) -> Member ((A × B) × C)
    r-×assc (a , (b , c)) = ((a , b) , c)

    l-×assc : {A B C : Type} -> Member ((A × B) × C) -> Member (A × (B × C))
    l-×assc ((a , b) , c) = (a , (b , c))

    rl-×assc-lemma : {A B C : Type} -> (a : Member ((A × B) × C)) -> r-×assc (l-×assc a) == a
    rl-×assc-lemma ((a , b) , c) = idp

    lr-×assc-lemma : {A B C : Type} -> (a : Member (A × (B × C))) -> l-×assc (r-×assc a) == a
    lr-×assc-lemma (a , (b , c)) = idp

    ×-assoc : {A B C : Type} -> (A × (B × C)) ≋ ((A × B) × C)
    ×-assoc = Equiv r-×assc l-×assc lr-×assc-lemma rl-×assc-lemma

    --- × Unit

    +-embed𝟘 : {A : Type} -> Member A -> Member (𝟘 + A)
    +-embed𝟘 a = right a

    +-project𝟘 : {A : Type} -> Member (𝟘 + A) -> Member A
    +-project𝟘 (right a) = a

    +-project-embed𝟘 : {A : Type} -> (a : Member (𝟘 + A)) -> +-embed𝟘 (+-project𝟘 a) == a
    +-project-embed𝟘 (right a) = idp

    +-unit : {A : Type} -> (𝟘 + A) ≋ A
    +-unit = Equiv +-project𝟘 +-embed𝟘 +-project-embed𝟘 λ x -> idp

    --- 𝟘 × A = 𝟘

    ×𝟘 : {A : Type} -> 𝟘 ≋ (𝟘 × A)
    ×𝟘 = let absurd-eq = (λ a -> absurd𝟘 {×fst (absurd𝟘 a) == a} a)
             absurd-proj = (λ b -> absurd𝟘 {absurd𝟘 (×fst b) == b} (×fst b))
         in  Equiv absurd𝟘 ×fst absurd-eq absurd-proj

    --- + Commutativity

    +-swap : {A B : Type} -> Member (A + B) -> Member (B + A)
    +-swap (left x) = right x
    +-swap (right x) = left x

    lemma-+-swap : {A B : Type} -> (ab : Member (A + B)) -> (+-swap (+-swap ab)) == ab
    lemma-+-swap (left x) = idp
    lemma-+-swap (right x) = idp

    +-commut : {A B : Type} -> (A + B) ≋ (B + A)
    +-commut = Equiv +-swap +-swap lemma-+-swap lemma-+-swap

    --- + Associativity

    r-+assc : {A B C : Type} -> Member (A + (B + C)) -> Member ((A + B) + C)
    r-+assc (left x) = left (left x)
    r-+assc (right (left x)) = left (right x)
    r-+assc (right (right x)) = right x

    l-+assc : {A B C : Type} -> Member ((A + B) + C) -> Member (A + (B + C))
    l-+assc (left (left x)) = left x
    l-+assc (left (right x)) = right (left x)
    l-+assc (right x) = right (right x)

    rl-+assc-lemma : {A B C : Type} -> (a : Member ((A + B) + C)) -> r-+assc (l-+assc a) == a
    rl-+assc-lemma (left (left x)) = idp
    rl-+assc-lemma (left (right x)) = idp
    rl-+assc-lemma (right x) = idp

    lr-+assc-lemma : {A B C : Type} -> (a : Member (A + (B + C))) -> l-+assc (r-+assc a) == a
    lr-+assc-lemma (left x) = idp
    lr-+assc-lemma (right (left x)) = idp
    lr-+assc-lemma (right (right x)) = idp

    +-assoc : {A B C : Type} -> (A + (B + C)) ≋ ((A + B) + C)
    +-assoc = Equiv r-+assc l-+assc lr-+assc-lemma rl-+assc-lemma


    --- Distrbutivity

    distrib : {A B C : Type} -> Member ((B + C) × A) -> Member ((B × A) + (C × A))
    distrib ((left b) , a) = left (b , a)
    distrib ((right c) , a) = right (c , a)

    unify : {A B C : Type} -> Member ((B × A) + (C × A)) -> Member ((B + C) × A)
    unify (left (b , a)) = ((left b) , a)
    unify (right (b , a)) = ((right b) , a)

    unify-distrib-lemma : {A B C : Type} -> (a : Member ((B × A) + (C × A))) -> distrib (unify a) == a
    unify-distrib-lemma (left (b , a)) = idp
    unify-distrib-lemma (right (b , a)) = idp

    distrib-unify-lemma : {A B C : Type} -> (a : Member ((B + C) × A)) -> unify (distrib a) == a
    distrib-unify-lemma ((left b) , a) = idp
    distrib-unify-lemma ((right b) , a) = idp

    ×+-distrib : {A B C : Type} -> ((B + C) × A) ≋ ((B × A) + (C × A))
    ×+-distrib = Equiv distrib unify distrib-unify-lemma unify-distrib-lemma

    --- Equiv respects +
    Equiv-+respects : {A B C D : Type} -> (A ≋ B) -> (C ≋ D) -> (A + C) ≋ (B + D)
    Equiv-+respects (Equiv f₁ g₁ x₁ y₁) (Equiv f₂ g₂ x₂ y₂) = Equiv {!!} {!!} {!!} {!!}

    Equiv-×respects : {A B C D : Type} -> (A ≋ B) -> (C ≋ D) -> (A × C) ≋ (B × D)
    Equiv-×respects (Equiv f₁ g₁ x₁ y₁) (Equiv f₂ g₂ x₂ y₂) = Equiv {!!} {!!} {!!} {!!}
