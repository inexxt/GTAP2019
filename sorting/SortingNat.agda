{-# OPTIONS --without-K #-}

module SortingNat where
  open import Data.Empty

  absurd : {x y : ℕ} -> (¬ x ≤ y) -> (¬ y ≤ x) -> ⊥
  absurd {zero} {zero} p q = q z≤n
  absurd {zero} {suc y} p q = p z≤n
  absurd {suc x} {zero} p q = q z≤n
  absurd {suc x} {suc y} p q = absurd (λ z → p (s≤s z)) (λ z → q (s≤s z))

  _≤??_ : (x y : ℕ) → (x ≤ y ⊎ y ≤ x)
  x ≤?? y with (x ≤? y)
  (x ≤?? y) | yes p = inj₁ p
  (x ≤?? y) | no ¬p with (y ≤? x)
  (x ≤?? y) | no ¬p | yes p = inj₂ p
  (x ≤?? y) | no ¬p | no ¬p₁ =  ⊥-elim $ absurd ¬p ¬p₁

  open import Data.Nat.Properties using () renaming (≤-isPartialOrder to po)
  open import SortingAlgorithm {ℕ} {Data.Nat._≤_} po _≤??_

  showSort : List ℕ -> List ℕ
  showSort xs = let ss = insertion-sort xs
                    ss' = SortedList.Sorted-to-Sorted' po ss in
                    SortedList.Sorted'.list ss'

  test : (showSort $ 5 ∷ 3 ∷ 2 ∷ 4 ∷ 1 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
  test = _≡_.refl

  ---------------------------------------------------------------------------
  -- Insertion sort with a list of swaps
  ---------------------------------------------------------------------------

  -- -- Insertion sort, O(n^2)
  -- insert : ∀ {xs} → (x : A) → Sorted xs → Sorted (x ∷ xs)
  -- insert x [] = cons x here [] []
  -- insert x (cons u p0 u≤*us us) with (x ≤? u)
  -- ... | (inj₁ p) = cons x here (insert-less p0 p (trans* p u≤*us)) $ cons u p0 u≤*us us
  -- ... | (inj₂ p) = cons u (there p0) (p ∷ u≤*us) (insert x us)
  --
  -- insertion-sort : (xs : List A) → Sorted xs
  -- insertion-sort [] = []
  -- insertion-sort (x ∷ xs) = insert x (insertion-sort xs)


  ---------------------------------------------------------------------------
  -- Selection sort
  ---------------------------------------------------------------------------

  -- import Data.Vec as Vec
  -- open Vec using (Vec;toList;fromList;_∷_;[])
  --
  -- -- select least element from a non-empty list x∷xs
  -- select1 : ∀ {n} (xs : Vec A (suc n))
  --         → (∃₂ \y ys → (y ◂ toList ys ≡ toList xs) × (y ≤* toList ys))
  -- select1 (x ∷ []) = x , [] , here , []
  -- select1 {suc n} (x ∷ xs)
  --   = bound-≡ (lem n) $
  --     select1 xs >>= \{ (z , zs , perm , least)
  --     → x ≤? z >>= \
  --       { (inj₁ p) → x , xs , here , insert-less perm p (trans* p least)
  --       ; (inj₂ p) → z , (x ∷ zs) , there perm , (p ∷ least)
  --       }}
  --   where
  --     lem : ∀ n → n + 1 ≡ 1 + n
  --     lem = solve 1 (\n → n :+ con 1 := con 1 :+ n) PE.refl
  --
  -- selection-sort1 : ∀ {n} (xs : Vec A n) → (Sorted (toList xs))
  -- selection-sort1 [] = return []
  -- selection-sort1 {suc n} xs
  --   = bound-+ (lem n) $
  --     select1 xs >>= \
  --     { (y , ys , perm , least)
  --     → cons y perm least <$> selection-sort1 ys }
  --   where
  --     lem : ∀ n → n + (n ^ 2) + (n + 1) ≡ (1 + n) ^ 2
  --     lem = solve 1 (\n → n :+ (n :^ 2) :+ (n :+ con 1)
  --                      := (con 1 :+ n) :^ 2) PE.refl
  --
  -- toList∘fromList : ∀ (xs : List A) → toList (fromList xs) ≡ xs
  -- toList∘fromList [] = PE.refl
  -- toList∘fromList (x ∷ xs) = PE.cong (_∷_ x) (toList∘fromList xs)
  --
  -- selection-sort2 : ∀ (xs : List A) → (Sorted xs)
  -- selection-sort2 xs = PE.subst Sorted (toList∘fromList xs)
  --                    <$> selection-sort1 (fromList xs)
