```agda
{-# OPTIONS --safe #-}
module semdtt where
```

Dependent sum types
```agda
data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B

ind-Σ : {A : Set} {B : A → Set}
        (C : Σ A B → Set)
      → ((x : A) (y : B x) → C (x , y))
      → (z : Σ A B) → C z
ind-Σ C f (z₁ , z₂) = f z₁ z₂
```
