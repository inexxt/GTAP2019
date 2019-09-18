{-# OPTIONS --without-K #-}

module General where
    open import Level

    variable
        ι ℓ l : Level

    _∘_ : {A : Set ℓ} -> {B : Set ι} -> {C : Set l} -> (B -> C) -> (A -> B) -> A -> C
    f ∘ g = λ x -> f (g x)

    data _==_ {A : Set ℓ} (a : A) : (b : A) ->  Set ℓ where
        idp : a == a

    J : {A : Set ℓ} ->
        {a : A} ->
        (C : {x : A} -> (a == x) -> Set ι) ->
        (p : C {a} idp) ->
        {x : A} ->
        ((q : (a == x)) -> C q)
    J C p = λ { idp → p }

    ap : {A : Set ℓ} -> {B : Set ι} -> {a b : A} -> (f : A -> B) -> (a == b) -> (f(a) == f(b))
    ap {a = a} f p = J (λ {x} q → f a == f x) idp p

    -- ap : {A : Set ℓ} -> {B : Set ι} -> {a b : A} -> (f : A -> B) -> (a == b) -> (f(a) == f(b))
    -- ap f idp = idp

    coe : {A B : Set ℓ} -> (A == B) -> A -> B
    coe idp a = a

    transport : {A : Set ℓ} -> {a b : A} -> (C : A -> Set ι) -> (a == b) -> (C(a) -> C(b))
    transport C = coe ∘ (ap C)

    apd : {A : Set ℓ} -> {C : A -> Set ι} -> {a b : A} -> (f : (a : A) -> C a) -> (p : (a == b)) -> (transport C p (f a)) == (f b)
    apd {C = C} f idp = idp

    rev : {A : Set ℓ} -> {a b : A} -> (p : a == b) -> (b == a)
    rev {a = a} {b = b} p = transport ((λ x -> (x == a))) p idp

    --- TODO I should do that with transport and ap, not with path induction
    comp : {A : Set ℓ} -> {a b c : A} -> (p : a == b) -> (q : b == c) -> (a == c)
    comp {a = a} {b = .a} {c = .a} idp idp = idp

    --- Non-dependent Product and Sum

    data Prod (T1 T2 : Set) : Set where
        _times_ : T1 -> T2 -> Prod T1 T2

    p₁ : {T1 T2 : Set} -> Prod T1 T2 -> T1
    p₁ (a times b) = a

    p₂ : {T1 T2 : Set} -> Prod T1 T2 -> T2
    p₂ (a times b) = b

    data Sum (T1 T2 : Set) : Set where
        left : T1 -> Sum T1 T2
        right : T2 -> Sum T1 T2

    record _≈_ (A B : Set) : Set where
        constructor Equiv
        field
            f : (A -> B)
            g : (B -> A)
            x : ((a : A) -> (g (f a)) == a)
            y : ((b : B) -> (f (g b)) == b)
