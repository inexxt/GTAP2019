{-# OPTIONS --without-K #-}
{-# OPTIONS --allow-unsolved-metas #-}

module FinTypes where
    data Type : Set where
        𝟘   : Type
        𝟙   : Type
        _×_ : Type -> Type -> Type
        _+_ : Type -> Type -> Type

    data Member : Type -> Set where
        *     : Member 𝟙
        _,_     : {X : Type} -> {Y : Type} -> Member X -> Member Y -> Member (X × Y)
        left    : {X : Type} -> {Y : Type} -> Member X -> Member (X + Y)
        right   : {X : Type} -> {Y : Type} -> Member Y -> Member (X + Y)

    absurd𝟘 : {A : Set} -> Member 𝟘 -> A
    absurd𝟘 ()

    ×fst : {X : Type} -> {Y : Type} -> Member (X × Y) -> Member X
    ×fst (a , b) = a

    ×snd : {X : Type} -> {Y : Type} -> Member (X × Y) -> Member Y
    ×snd (a , b) = b

    data _≣_ : {T : Type} -> Member T -> Member T -> Set where
        refl₁ : * ≣ *
        reflₓ : {X : Type} -> {Y : Type}
                -> {p11 : Member X}
                -> {p21 : Member X}
                -> {p12 : Member Y}
                -> {p22 : Member Y}
                -> p11 ≣ p21
                -> p12 ≣ p22
                -> (p11 , p12) ≣ (p21 , p22)
        reflₗ : {X : Type} -> {Y : Type}
                -> {x1 : Member X}
                -> {x2 : Member X}
                -> x1 ≣ x2
                -> _≣_ {X + Y} (left x1) (left x2)
        reflᵣ : {X : Type} -> {Y : Type}
                -> {y1 : Member Y}
                -> {y2 : Member Y}
                -> y1 ≣ y2
                -> (right {X} y1) ≣ (right {X} y2)
        ≣comp : {A : Type} -> {a b c : Member A} -> a ≣ b -> b ≣ c -> a ≣ c
        ≣app  : {A B : Type} -> {a b : Member A} -> (f : Member A -> Member B) -> a ≣ b -> (f a) ≣ (f b)

    refl : {A : Type} -> (a : Member A) -> a ≣ a
    refl * = refl₁
    refl (a , b) = reflₓ (refl a) (refl b)
    refl {A + B} (left a) = reflₗ {A} {B} (refl a)
    refl {A + B} (right b) = reflᵣ {A} {B} (refl b)

    record _≈_ (A B : Type) : Set where
        constructor Equiv
        field
            f : (Member A -> Member B)
            g : (Member B -> Member A)
            x : ((a : Member A) -> (g (f a)) ≣ a)
            y : ((b : Member B) -> (f (g b)) ≣ b)

    open _≈_

    id : {A : Set} -> A -> A
    id x = x

    --- Reflexivity

    Equiv-reflex : {A : Type} -> A ≈ A
    Equiv-reflex = Equiv id id refl refl

    --- Symmetry

    Equiv-symmetry : {A B : Type} -> A ≈ B -> B ≈ A
    Equiv-symmetry (Equiv f g e1 e2) = Equiv g f e2 e1

    --- Function Composition

    _∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
    f ∘ g = λ x -> f (g x)

    --- Composition

    Equiv-composition : {A B C : Type} -> (A ≈ B) -> (B ≈ C) -> (A ≈ C)
    Equiv-composition {A} {B} {C} (Equiv fab fba eab eba) (Equiv fbc fcb ebc ecb) =
        let a-c-a a = ≣app fba (ebc (fab a))
            c-a-c c = ≣app fbc (eba (fcb c))
        in  Equiv (fbc ∘ fab)
                  (fba ∘ fcb)
                  (λ a -> ≣comp (a-c-a a) (eab a))
                  (λ c -> ≣comp (c-a-c c) (ecb c))

    --- × Unit

    ×-embed𝟙 : {A : Type} -> Member A -> Member (𝟙 × A)
    ×-embed𝟙 a = (* , a)

    ×-project𝟙 : {A : Type} -> Member (𝟙 × A) -> Member A
    ×-project𝟙 (* , a) = a

    ×-unit : {A B : Type} -> (𝟙 × A) ≈ A
    ×-unit = Equiv ×-project𝟙 ×-embed𝟙 (λ {(* , a) → refl (* , a)}) refl

    --- × Commutativity

    ×-swap : {A B : Type} -> Member (A × B) -> Member (B × A)
    ×-swap (a , b) = (b , a)

    lemma-×-swap : {A B : Type} -> (ab : Member (A × B)) -> (×-swap (×-swap ab)) ≣ ab
    lemma-×-swap (a , b) = refl (a , b)

    ×-commut : {A B : Type} -> (A × B) ≈ (B × A)
    ×-commut = Equiv ×-swap ×-swap lemma-×-swap lemma-×-swap

    --- × Associativity

    r-×assc : {A B C : Type} -> Member (A × (B × C)) -> Member ((A × B) × C)
    r-×assc (a , (b , c)) = ((a , b) , c)

    l-×assc : {A B C : Type} -> Member ((A × B) × C) -> Member (A × (B × C))
    l-×assc ((a , b) , c) = (a , (b , c))

    rl-×assc-lemma : {A B C : Type} -> (a : Member ((A × B) × C)) -> r-×assc (l-×assc a) ≣ a
    rl-×assc-lemma ((a , b) , c) = refl ((a , b) , c)

    lr-×assc-lemma : {A B C : Type} -> (a : Member (A × (B × C))) -> l-×assc (r-×assc a) ≣ a
    lr-×assc-lemma (a , (b , c)) = refl (a , (b , c))

    ×-assoc : {A B C : Type} -> (A × (B × C)) ≈ ((A × B) × C)
    ×-assoc = Equiv r-×assc l-×assc lr-×assc-lemma rl-×assc-lemma

    --- × Unit

    +-embed𝟘 : {A : Type} -> Member A -> Member (𝟘 + A)
    +-embed𝟘 a = right a

    +-project𝟘 : {A : Type} -> Member (𝟘 + A) -> Member A
    +-project𝟘 (right a) = a

    +-project-embed𝟘 : {A : Type} -> (a : Member (𝟘 + A)) -> +-embed𝟘 (+-project𝟘 a) ≣ a
    +-project-embed𝟘 (right a) = refl (right a)

    +-unit : {A : Type} -> (𝟘 + A) ≈ A
    +-unit = Equiv +-project𝟘 +-embed𝟘 +-project-embed𝟘 refl

    --- 𝟘 × A = 𝟘

    ×𝟘 : {A : Type} -> 𝟘 ≈ (𝟘 × A)
    ×𝟘 = let absurd-eq = (λ a -> absurd𝟘 {×fst (absurd𝟘 a) ≣ a} a)
             absurd-proj = (λ b -> absurd𝟘 {absurd𝟘 (×fst b) ≣ b} (×fst b))
         in  Equiv absurd𝟘 ×fst absurd-eq absurd-proj

    --- + Commutativity

    +-swap : {A B : Type} -> Member (A + B) -> Member (B + A)
    +-swap (left x) = right x
    +-swap (right x) = left x

    lemma-+-swap : {A B : Type} -> (ab : Member (A + B)) -> (+-swap (+-swap ab)) ≣ ab
    lemma-+-swap (left x) = refl (left x)
    lemma-+-swap (right x) = refl (right x)

    +-commut : {A B : Type} -> (A + B) ≈ (B + A)
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

    rl-+assc-lemma : {A B C : Type} -> (a : Member ((A + B) + C)) -> r-+assc (l-+assc a) ≣ a
    rl-+assc-lemma (left (left x)) = refl (left (left x))
    rl-+assc-lemma (left (right x)) = refl (left (right x))
    rl-+assc-lemma (right x) = refl (right x)

    lr-+assc-lemma : {A B C : Type} -> (a : Member (A + (B + C))) -> l-+assc (r-+assc a) ≣ a
    lr-+assc-lemma (left x) = refl (left x)
    lr-+assc-lemma (right (left x)) = refl (right (left x))
    lr-+assc-lemma (right (right x)) = refl (right (right x))

    +-assoc : {A B C : Type} -> (A + (B + C)) ≈ ((A + B) + C)
    +-assoc = Equiv r-+assc l-+assc lr-+assc-lemma rl-+assc-lemma

    --- Distrbutivity

    distrib : {A B C : Type} -> Member ((B + C) × A) -> Member ((B × A) + (C × A))
    distrib ((left b) , a) = left (b , a)
    distrib ((right c) , a) = right (c , a)

    unify : {A B C : Type} -> Member ((B × A) + (C × A)) -> Member ((B + C) × A)
    unify (left (b , a)) = ((left b) , a)
    unify (right (b , a)) = ((right b) , a)

    unify-distrib-lemma : {A B C : Type} -> (a : Member ((B × A) + (C × A))) -> distrib (unify a) ≣ a
    unify-distrib-lemma (left (b , a)) = refl (left (b , a))
    unify-distrib-lemma (right (b , a)) = refl (right (b , a))

    distrib-unify-lemma : {A B C : Type} -> (a : Member ((B + C) × A)) -> unify (distrib a) ≣ a
    distrib-unify-lemma ((left b) , a) = refl ((left b) , a)
    distrib-unify-lemma ((right b) , a) = refl ((right b) , a)

    ×+-distrib : {A B C : Type} -> ((B + C) × A) ≈ ((B × A) + (C × A))
    ×+-distrib = Equiv distrib unify distrib-unify-lemma unify-distrib-lemma

    --- Equiv respects +
    Equiv-+respects : {A B C D : Type} -> (A ≈ B) -> (C ≈ D) -> (A + C) ≈ (B + D)
    Equiv-+respects e1 e2 = {!   !}

    Equiv-×respects : {A B C D : Type} -> (A ≈ B) -> (C ≈ D) -> (A × C) ≈ (B × D)
    Equiv-×respects e1 e2 = {!   !}
