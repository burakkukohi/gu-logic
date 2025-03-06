```agda
{-# OPTIONS --safe --without-K #-}
module semdtt where
```
# Empty
```agda
data 𝟘 : Set where
```

# Unit
```agda
data 𝟙 : Set where
  ⋆ : 𝟙
```

# Nat
```agda
data ℕ : Set where
  z : ℕ
  suc : ℕ → ℕ
```

# Id
```agda
data Id {A : Set} : A → A → Set where
  refl : (a : A) → Id a a
```

# Peano axiom 4
```agda
pa-4[not-MLTT] : Id z (suc z) → 𝟘
pa-4[not-MLTT] ()

_≡_ : ℕ → ℕ → Set
z ≡ z = 𝟙
z ≡ suc n = 𝟘
suc m ≡ z = 𝟘
suc m ≡ suc n = m ≡ n

id-gives-≡ : (m n : ℕ) → Id m n → m ≡ n
id-gives-≡ z .z (refl .z) = ⋆
id-gives-≡ (suc m) .(suc m) (refl .(suc m)) = id-gives-≡ m m (refl m)

pa-4 : Id z (suc z) → 𝟘
pa-4 p = I (id-gives-≡ z (suc z) p) where
  I : 𝟘 → 𝟘
  I = λ x → x
  
```
