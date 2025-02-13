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
      → (z : Σ A B)
      → ((x : A) (y : B x) → C (x , y)) → C z
ind-Σ C (z₁ , z₂) s = s z₁ z₂
```

Identity types
```agda
data id {A : Set} : A → A → Set where
  refl : (a : A) → id a a

ind-id : {A : Set}
       → (B : (x y : A) → id x y → Set)
       → (a b : A)
       → (u : id a b)
       → ((z : A) → B z z (refl z))
       → B a b u
ind-id B a .a (refl .a) s = s a
```
