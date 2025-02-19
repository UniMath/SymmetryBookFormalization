# The absolute value function on the integers

```agda
module elementary-number-theory.absolute-value-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.positive-integers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.unit-type
```

</details>

## Idea

The {{#concept "absolute value" Disambiguation="of an integer" Agda=abs-ℤ}} of
an integer is the natural number with the same distance from `0`.

## Definitions

### The absolute value of an integer

```agda
abs-ℤ : ℤ → ℕ
abs-ℤ (inl x) = succ-ℕ x
abs-ℤ (inr (inl star)) = zero-ℕ
abs-ℤ (inr (inr x)) = succ-ℕ x

int-abs-ℤ : ℤ → ℤ
int-abs-ℤ = int-ℕ ∘ abs-ℤ
```

## Properties

### The absolute value of `int-ℕ n` is `n` itself

```agda
abs-int-ℕ : (n : ℕ) → abs-ℤ (int-ℕ n) ＝ n
abs-int-ℕ zero-ℕ = refl
abs-int-ℕ (succ-ℕ n) = refl
```

### `|-x| ＝ |x|`

```agda
abs-neg-ℤ : (x : ℤ) → abs-ℤ (neg-ℤ x) ＝ abs-ℤ x
abs-neg-ℤ (inl x) = refl
abs-neg-ℤ (inr (inl star)) = refl
abs-neg-ℤ (inr (inr x)) = refl
```

### If `x` is nonnegative, then `int-abs-ℤ x ＝ x`

```agda
int-abs-is-nonnegative-ℤ : (x : ℤ) → is-nonnegative-ℤ x → int-abs-ℤ x ＝ x
int-abs-is-nonnegative-ℤ (inr (inl star)) h = refl
int-abs-is-nonnegative-ℤ (inr (inr x)) h = refl
```

### `|x| ＝ 0` if and only if `x ＝ 0`

```agda
eq-abs-ℤ : (x : ℤ) → is-zero-ℕ (abs-ℤ x) → is-zero-ℤ x
eq-abs-ℤ (inr (inl star)) p = refl

abs-eq-ℤ : (x : ℤ) → is-zero-ℤ x → is-zero-ℕ (abs-ℤ x)
abs-eq-ℤ .zero-ℤ refl = refl
```

### `|x - 1| ≤ |x| + 1`

```agda
predecessor-law-abs-ℤ :
  (x : ℤ) → (abs-ℤ (pred-ℤ x)) ≤-ℕ (succ-ℕ (abs-ℤ x))
predecessor-law-abs-ℤ (inl x) =
  refl-leq-ℕ (succ-ℕ x)
predecessor-law-abs-ℤ (inr (inl star)) =
  refl-leq-ℕ zero-ℕ
predecessor-law-abs-ℤ (inr (inr zero-ℕ)) =
  star
predecessor-law-abs-ℤ (inr (inr (succ-ℕ x))) =
  leq-succ-leq-ℕ x (succ-ℕ x) (succ-leq-ℕ x)
```

### `|x + 1| ≤ |x| + 1`

```agda
successor-law-abs-ℤ :
  (x : ℤ) → (abs-ℤ (succ-ℤ x)) ≤-ℕ (succ-ℕ (abs-ℤ x))
successor-law-abs-ℤ (inl zero-ℕ) =
  star
successor-law-abs-ℤ (inl (succ-ℕ x)) =
  leq-succ-leq-ℕ x (succ-ℕ x) (succ-leq-ℕ x)
successor-law-abs-ℤ (inr (inl star)) =
  refl-leq-ℕ zero-ℕ
successor-law-abs-ℤ (inr (inr x)) =
  refl-leq-ℕ (succ-ℕ x)
```

### The absolute value function is subadditive

```agda
subadditive-abs-ℤ :
  (x y : ℤ) → (abs-ℤ (x +ℤ y)) ≤-ℕ ((abs-ℤ x) +ℕ (abs-ℤ y))
subadditive-abs-ℤ x (inl zero-ℕ) =
  concatenate-eq-leq-eq-ℕ
    ( ap abs-ℤ (right-add-neg-one-ℤ x))
    ( predecessor-law-abs-ℤ x)
    ( refl)
subadditive-abs-ℤ x (inl (succ-ℕ y)) =
  concatenate-eq-leq-eq-ℕ
    ( ap abs-ℤ (right-predecessor-law-add-ℤ x (inl y)))
    ( transitive-leq-ℕ
      ( abs-ℤ (pred-ℤ (x +ℤ (inl y))))
      ( succ-ℕ (abs-ℤ (x +ℤ (inl y))))
      ( (abs-ℤ x) +ℕ (succ-ℕ (succ-ℕ y)))
      ( subadditive-abs-ℤ x (inl y))
      ( predecessor-law-abs-ℤ (x +ℤ (inl y))))
    ( refl)
subadditive-abs-ℤ x (inr (inl star)) =
  concatenate-eq-leq-eq-ℕ
    ( ap abs-ℤ (right-unit-law-add-ℤ x))
    ( refl-leq-ℕ (abs-ℤ x))
    ( refl)
subadditive-abs-ℤ x (inr (inr zero-ℕ)) =
  concatenate-eq-leq-eq-ℕ
    ( ap abs-ℤ (right-add-one-ℤ x))
    ( successor-law-abs-ℤ x)
    ( refl)
subadditive-abs-ℤ x (inr (inr (succ-ℕ y))) =
  concatenate-eq-leq-eq-ℕ
    ( ap abs-ℤ (right-successor-law-add-ℤ x (inr (inr y))))
    ( transitive-leq-ℕ
      ( abs-ℤ (succ-ℤ (x +ℤ (inr (inr y)))))
      ( succ-ℕ (abs-ℤ (x +ℤ (inr (inr y)))))
      ( succ-ℕ ((abs-ℤ x) +ℕ (succ-ℕ y)))
      ( subadditive-abs-ℤ x (inr (inr y)))
      ( successor-law-abs-ℤ (x +ℤ (inr (inr y)))))
    ( refl)
```

### `|-x| ＝ |x|`

```agda
negative-law-abs-ℤ :
  (x : ℤ) → abs-ℤ (neg-ℤ x) ＝ abs-ℤ x
negative-law-abs-ℤ (inl x) = refl
negative-law-abs-ℤ (inr (inl star)) = refl
negative-law-abs-ℤ (inr (inr x)) = refl
```

### If `x` is positive then `|x|` is positive

```agda
is-positive-abs-ℤ :
  (x : ℤ) → is-positive-ℤ x → is-positive-ℤ (int-abs-ℤ x)
is-positive-abs-ℤ (inr (inr x)) H = star
```

### If `x` is nonzero then `|x|` is nonzero

```agda
is-nonzero-abs-ℤ :
  (x : ℤ) → is-positive-ℤ x → is-nonzero-ℕ (abs-ℤ x)
is-nonzero-abs-ℤ (inr (inr x)) H = is-nonzero-succ-ℕ x
```

### The absolute value distributes over multiplication

```agda
distributive-abs-mul-ℤ' :
  (x y : ℤ) → abs-ℤ (explicit-mul-ℤ x y) ＝ abs-ℤ x *ℕ abs-ℤ y
distributive-abs-mul-ℤ' (inl x) (inl y) =
  abs-int-ℕ _
distributive-abs-mul-ℤ' (inl x) (inr (inl star)) =
  inv (right-zero-law-mul-ℕ x)
distributive-abs-mul-ℤ' (inl x) (inr (inr y)) =
  ( abs-neg-ℤ (inl ((x *ℕ (succ-ℕ y)) +ℕ y))) ∙
  ( abs-int-ℕ ((succ-ℕ x) *ℕ (succ-ℕ y)))
distributive-abs-mul-ℤ' (inr (inl star)) (inl y) =
  refl
distributive-abs-mul-ℤ' (inr (inr x)) (inl y) =
  ( abs-neg-ℤ (inl ((x *ℕ (succ-ℕ y)) +ℕ y))) ∙
  ( abs-int-ℕ (succ-ℕ ((x *ℕ (succ-ℕ y)) +ℕ y)))
distributive-abs-mul-ℤ' (inr (inl star)) (inr (inl star)) =
  refl
distributive-abs-mul-ℤ' (inr (inl star)) (inr (inr x)) =
  refl
distributive-abs-mul-ℤ' (inr (inr x)) (inr (inl star)) =
  inv (right-zero-law-mul-ℕ (succ-ℕ x))
distributive-abs-mul-ℤ' (inr (inr x)) (inr (inr y)) =
  abs-int-ℕ _

distributive-abs-mul-ℤ :
  (x y : ℤ) → abs-ℤ (x *ℤ y) ＝ abs-ℤ x *ℕ abs-ℤ y
distributive-abs-mul-ℤ x y =
  ap abs-ℤ (compute-mul-ℤ x y) ∙ distributive-abs-mul-ℤ' x y
```

### `|(-x)y| ＝ |xy|`

```agda
left-negative-law-mul-abs-ℤ :
  (x y : ℤ) → abs-ℤ (x *ℤ y) ＝ abs-ℤ ((neg-ℤ x) *ℤ y)
left-negative-law-mul-abs-ℤ x y =
  equational-reasoning
    abs-ℤ (x *ℤ y)
    ＝ abs-ℤ (neg-ℤ (x *ℤ y))
      by (inv (negative-law-abs-ℤ (x *ℤ y)))
    ＝ abs-ℤ ((neg-ℤ x) *ℤ y)
      by (ap abs-ℤ (inv (left-negative-law-mul-ℤ x y)))
```

### `|x(-y)| ＝ |xy|`

```agda
right-negative-law-mul-abs-ℤ :
  (x y : ℤ) → abs-ℤ (x *ℤ y) ＝ abs-ℤ (x *ℤ (neg-ℤ y))
right-negative-law-mul-abs-ℤ x y =
  equational-reasoning
    abs-ℤ (x *ℤ y)
    ＝ abs-ℤ (neg-ℤ (x *ℤ y))
      by (inv (negative-law-abs-ℤ (x *ℤ y)))
    ＝ abs-ℤ (x *ℤ (neg-ℤ y))
      by (ap abs-ℤ (inv (right-negative-law-mul-ℤ x y)))
```

### `|(-x)(-y)| ＝ |xy|`

```agda
double-negative-law-mul-abs-ℤ :
  (x y : ℤ) → abs-ℤ (x *ℤ y) ＝ abs-ℤ ((neg-ℤ x) *ℤ (neg-ℤ y))
double-negative-law-mul-abs-ℤ x y =
  (right-negative-law-mul-abs-ℤ x y) ∙ (left-negative-law-mul-abs-ℤ x (neg-ℤ y))
```
