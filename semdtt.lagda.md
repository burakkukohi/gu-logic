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

Identity types
```agda
data id {A : Set} : A → A → Set where
  refl : (a : A) → id a a

ind-id : {A : Set}
       → (B : (x y : A) → id x y → Set)
       → (s : (z : A) → B z z (refl z))
       → (a b : A)
       → (u : id a b)
       → B a b u
ind-id B s a .a (refl .a) = s a
```

id is symmetric
```agda
id-symm : {A : Set} (a b : A) → id a b → id b a
id-symm a .a (refl .a) = refl a
```

id is transitive
```agda
id-trans : {A : Set} (a b c : A) → id a b → id b c → id a c
id-trans a .a c (refl .a) = λ x → x
```

Action on path
```agda
ap : {A B : Set}
     (f : A → B)
   → (a a' : A)
   → id a a'
   → id (f a) (f a')
ap f a .a (refl .a) = refl (f a)
```
