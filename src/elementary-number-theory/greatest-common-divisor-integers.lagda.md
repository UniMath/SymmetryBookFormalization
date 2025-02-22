# The greatest common divisor of integers

```agda
module elementary-number-theory.greatest-common-divisor-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.equality-integers
open import elementary-number-theory.greatest-common-divisor-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.unit-integers
open import elementary-number-theory.unit-similarity-integers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Definition

### The predicate of being a greatest common divisor

```agda
is-common-divisor-ℤ : ℤ → ℤ → ℤ → UU lzero
is-common-divisor-ℤ x y d = (div-ℤ d x) × (div-ℤ d y)

is-gcd-ℤ : ℤ → ℤ → ℤ → UU lzero
is-gcd-ℤ x y d =
  is-nonnegative-ℤ d × ((k : ℤ) → is-common-divisor-ℤ x y k ↔ div-ℤ k d)
```

### The greatest common divisor of two integers

```agda
nat-gcd-ℤ : ℤ → ℤ → ℕ
nat-gcd-ℤ x y = gcd-ℕ (abs-ℤ x) (abs-ℤ y)

gcd-ℤ : ℤ → ℤ → ℤ
gcd-ℤ x y = int-ℕ (nat-gcd-ℤ x y)
```

## Properties

### The greatest common divisor is invariant under negatives

```agda
module _
  (x y : ℤ)
  where

  preserves-gcd-left-neg-ℤ : gcd-ℤ (neg-ℤ x) y ＝ gcd-ℤ x y
  preserves-gcd-left-neg-ℤ =
    ap (int-ℕ ∘ (λ z → gcd-ℕ z (abs-ℤ y))) (abs-neg-ℤ x)

  preserves-gcd-right-neg-ℤ : gcd-ℤ x (neg-ℤ y) ＝ gcd-ℤ x y
  preserves-gcd-right-neg-ℤ =
    ap (int-ℕ ∘ (gcd-ℕ (abs-ℤ x))) (abs-neg-ℤ y)
```

### A natural number `d` is a common divisor of two natural numbers `x` and `y` if and only if `int-ℕ d` is a common divisor of `int-ℕ x` and `ind-ℕ y`

```agda
is-common-divisor-int-is-common-divisor-ℕ :
  {x y d : ℕ} →
  is-common-divisor-ℕ x y d → is-common-divisor-ℤ (int-ℕ x) (int-ℕ y) (int-ℕ d)
is-common-divisor-int-is-common-divisor-ℕ =
  map-product div-int-div-ℕ div-int-div-ℕ

is-common-divisor-is-common-divisor-int-ℕ :
  {x y d : ℕ} →
  is-common-divisor-ℤ (int-ℕ x) (int-ℕ y) (int-ℕ d) → is-common-divisor-ℕ x y d
is-common-divisor-is-common-divisor-int-ℕ {x} {y} {d} =
  map-product div-div-int-ℕ div-div-int-ℕ
```

### If `ux ＝ x'` and `vy ＝ y'` for two units `u` and `v`, then `d` is a common divisor of `x` and `y` if and only if `d` is a common divisor of `x'` and `y'`

```agda
is-common-divisor-sim-unit-ℤ :
  {x x' y y' d d' : ℤ} → sim-unit-ℤ x x' → sim-unit-ℤ y y' → sim-unit-ℤ d d' →
  is-common-divisor-ℤ x y d → is-common-divisor-ℤ x' y' d'
is-common-divisor-sim-unit-ℤ H K L =
  map-product (div-sim-unit-ℤ L H) (div-sim-unit-ℤ L K)
```

### If `ux ＝ x'` and `vy ＝ y'` for two units `u` and `v`, then `d` is a greatest common divisor of `x` and `y` if and only if `c` is a greatest common divisor of `x'` and `y'`

```agda
is-gcd-sim-unit-ℤ :
  {x x' y y' d : ℤ} →
  sim-unit-ℤ x x' → sim-unit-ℤ y y' →
  is-gcd-ℤ x y d → is-gcd-ℤ x' y' d
pr1 (is-gcd-sim-unit-ℤ H K (pair x _)) = x
pr1 (pr2 (is-gcd-sim-unit-ℤ H K (pair _ G)) k) =
  ( pr1 (G k)) ∘
  ( is-common-divisor-sim-unit-ℤ
    ( symmetric-sim-unit-ℤ _ _ H)
    ( symmetric-sim-unit-ℤ _ _ K)
    ( refl-sim-unit-ℤ k))
pr2 (pr2 (is-gcd-sim-unit-ℤ H K (pair _ G)) k) =
  ( is-common-divisor-sim-unit-ℤ H K (refl-sim-unit-ℤ k)) ∘
  ( pr2 (G k))
```

### An integer `d` is a common divisor of `x` and `y` if and only if `|d|` is a common divisor of `x` and `y`

```agda
is-common-divisor-int-abs-is-common-divisor-ℤ :
  {x y d : ℤ} →
  is-common-divisor-ℤ x y d → is-common-divisor-ℤ x y (int-abs-ℤ d)
is-common-divisor-int-abs-is-common-divisor-ℤ =
  map-product div-int-abs-divisor-div-ℤ div-int-abs-divisor-div-ℤ

is-common-divisor-is-common-divisor-int-abs-ℤ :
  {x y d : ℤ} →
  is-common-divisor-ℤ x y (int-abs-ℤ d) → is-common-divisor-ℤ x y d
is-common-divisor-is-common-divisor-int-abs-ℤ =
  map-product div-div-int-abs-divisor-ℤ div-div-int-abs-divisor-ℤ

is-common-divisor-is-gcd-ℤ :
  (a b d : ℤ) → is-gcd-ℤ a b d → is-common-divisor-ℤ a b d
is-common-divisor-is-gcd-ℤ a b d H = pr2 (pr2 H d) (refl-div-ℤ d)
```

### A natural number `d` is a greatest common divisor of two natural numbers `x` and `y` if and only if `int-ℕ d` is a greatest common divisor of `int-ℕ x` and `int-ℕ y`

```agda
is-gcd-int-is-gcd-ℕ :
  {x y d : ℕ} → is-gcd-ℕ x y d → is-gcd-ℤ (int-ℕ x) (int-ℕ y) (int-ℕ d)
pr1 (is-gcd-int-is-gcd-ℕ {x} {y} {d} H) = is-nonnegative-int-ℕ d
pr1 (pr2 (is-gcd-int-is-gcd-ℕ {x} {y} {d} H) k) =
  ( ( ( ( div-div-int-abs-divisor-ℤ) ∘
        ( div-int-div-ℕ)) ∘
      ( pr1 (H (abs-ℤ k)))) ∘
    ( is-common-divisor-is-common-divisor-int-ℕ)) ∘
  ( is-common-divisor-int-abs-is-common-divisor-ℤ)
pr2 (pr2 (is-gcd-int-is-gcd-ℕ {x} {y} {d} H) k) =
  ( ( ( ( is-common-divisor-is-common-divisor-int-abs-ℤ) ∘
        ( is-common-divisor-int-is-common-divisor-ℕ)) ∘
      ( pr2 (H (abs-ℤ k)))) ∘
    ( div-div-int-ℕ)) ∘
  ( div-int-abs-divisor-div-ℤ)

is-gcd-is-gcd-int-ℕ :
  {x y d : ℕ} → is-gcd-ℤ (int-ℕ x) (int-ℕ y) (int-ℕ d) → is-gcd-ℕ x y d
pr1 (is-gcd-is-gcd-int-ℕ {x} {y} {d} H k) =
  ( ( div-div-int-ℕ) ∘
    ( pr1 (pr2 H (int-ℕ k)))) ∘
  ( is-common-divisor-int-is-common-divisor-ℕ)
pr2 (is-gcd-is-gcd-int-ℕ {x} {y} {d} H k) =
  ( ( is-common-divisor-is-common-divisor-int-ℕ) ∘
    ( pr2 (pr2 H (int-ℕ k)))) ∘
  ( div-int-div-ℕ)
```

### `gcd-ℤ x y` is a greatest common divisor of `x` and `y`

```agda
is-nonnegative-gcd-ℤ : (x y : ℤ) → is-nonnegative-ℤ (gcd-ℤ x y)
is-nonnegative-gcd-ℤ x y = is-nonnegative-int-ℕ (nat-gcd-ℤ x y)

gcd-nonnegative-ℤ : ℤ → ℤ → nonnegative-ℤ
pr1 (gcd-nonnegative-ℤ x y) = gcd-ℤ x y
pr2 (gcd-nonnegative-ℤ x y) = is-nonnegative-gcd-ℤ x y

is-gcd-gcd-ℤ : (x y : ℤ) → is-gcd-ℤ x y (gcd-ℤ x y)
pr1 (is-gcd-gcd-ℤ x y) = is-nonnegative-gcd-ℤ x y
pr1 (pr2 (is-gcd-gcd-ℤ x y) k) =
  ( ( ( ( ( div-sim-unit-ℤ
            ( sim-unit-abs-ℤ k)
            ( refl-sim-unit-ℤ (gcd-ℤ x y))) ∘
          ( div-int-div-ℕ)) ∘
        ( pr1 (is-gcd-gcd-ℕ (abs-ℤ x) (abs-ℤ y) (abs-ℤ k)))) ∘
      ( is-common-divisor-is-common-divisor-int-ℕ)) ∘
    ( is-common-divisor-int-abs-is-common-divisor-ℤ)) ∘
  ( is-common-divisor-sim-unit-ℤ
    ( symmetric-sim-unit-ℤ (int-abs-ℤ x) x (sim-unit-abs-ℤ x))
    ( symmetric-sim-unit-ℤ (int-abs-ℤ y) y (sim-unit-abs-ℤ y))
    ( refl-sim-unit-ℤ k))
pr2 (pr2 (is-gcd-gcd-ℤ x y) k) =
  ( ( ( ( ( is-common-divisor-sim-unit-ℤ
            ( sim-unit-abs-ℤ x)
            ( sim-unit-abs-ℤ y)
            ( refl-sim-unit-ℤ k)) ∘
          ( is-common-divisor-is-common-divisor-int-abs-ℤ)) ∘
        ( is-common-divisor-int-is-common-divisor-ℕ)) ∘
      ( pr2 (is-gcd-gcd-ℕ (abs-ℤ x) (abs-ℤ y) (abs-ℤ k)))) ∘
    ( div-div-int-ℕ)) ∘
  ( div-sim-unit-ℤ
    ( symmetric-sim-unit-ℤ (int-abs-ℤ k) k (sim-unit-abs-ℤ k))
    ( refl-sim-unit-ℤ (gcd-ℤ x y)))
```

### The gcd in `ℕ` of `x` and `y` is equal to the gcd in `ℤ` of `int-ℕ x` and `int-ℕ y`

```agda
eq-gcd-gcd-int-ℕ :
  (x y : ℕ) → gcd-ℤ (int-ℕ x) (int-ℕ y) ＝ int-ℕ (gcd-ℕ x y)
eq-gcd-gcd-int-ℕ x y =
  ( ( ap
      ( λ x → int-ℕ (gcd-ℕ x (abs-ℤ (int-ℕ y))))
      ( abs-int-ℕ x)) ∙
    ( ap
      ( λ y → int-ℕ (gcd-ℕ x y))
      ( abs-int-ℕ y)))
```

### The gcd of `x` and `y` divides both `x` and `y`

```agda
is-common-divisor-gcd-ℤ :
  (x y : ℤ) → is-common-divisor-ℤ x y (gcd-ℤ x y)
is-common-divisor-gcd-ℤ x y =
  pr2 (pr2 (is-gcd-gcd-ℤ x y) (gcd-ℤ x y)) (refl-div-ℤ (gcd-ℤ x y))

div-left-gcd-ℤ : (x y : ℤ) → div-ℤ (gcd-ℤ x y) x
div-left-gcd-ℤ x y = pr1 (is-common-divisor-gcd-ℤ x y)

div-right-gcd-ℤ : (x y : ℤ) → div-ℤ (gcd-ℤ x y) y
div-right-gcd-ℤ x y = pr2 (is-common-divisor-gcd-ℤ x y)
```

### Any common divisor of `x` and `y` divides the greatest common divisor

```agda
div-gcd-is-common-divisor-ℤ :
  (x y k : ℤ) → is-common-divisor-ℤ x y k → div-ℤ k (gcd-ℤ x y)
div-gcd-is-common-divisor-ℤ x y k H =
  pr1 (pr2 (is-gcd-gcd-ℤ x y) k) H
```

### If either `x` or `y` is a positive integer, then `gcd-ℤ x y` is positive

```agda
is-positive-gcd-is-positive-left-ℤ :
  (x y : ℤ) → is-positive-ℤ x → is-positive-ℤ (gcd-ℤ x y)
is-positive-gcd-is-positive-left-ℤ x y H =
  is-positive-int-is-nonzero-ℕ
    ( gcd-ℕ (abs-ℤ x) (abs-ℤ y))
    ( is-nonzero-gcd-ℕ
      ( abs-ℤ x)
      ( abs-ℤ y)
      ( λ p → is-nonzero-abs-ℤ x H (f p)))
  where
  f : is-zero-ℕ ((abs-ℤ x) +ℕ (abs-ℤ y)) → is-zero-ℕ (abs-ℤ x)
  f = is-zero-left-is-zero-add-ℕ (abs-ℤ x) (abs-ℤ y)

is-positive-gcd-is-positive-right-ℤ :
  (x y : ℤ) → is-positive-ℤ y → is-positive-ℤ (gcd-ℤ x y)
is-positive-gcd-is-positive-right-ℤ x y H =
  is-positive-int-is-nonzero-ℕ
    ( gcd-ℕ (abs-ℤ x) (abs-ℤ y))
    ( is-nonzero-gcd-ℕ
      ( abs-ℤ x)
      ( abs-ℤ y)
      ( λ p → is-nonzero-abs-ℤ y H (f p)))
  where
  f : is-zero-ℕ ((abs-ℤ x) +ℕ (abs-ℤ y)) → is-zero-ℕ (abs-ℤ y)
  f = is-zero-right-is-zero-add-ℕ (abs-ℤ x) (abs-ℤ y)

is-positive-gcd-ℤ :
  (x y : ℤ) → (is-positive-ℤ x) + (is-positive-ℤ y) →
  is-positive-ℤ (gcd-ℤ x y)
is-positive-gcd-ℤ x y (inl H) = is-positive-gcd-is-positive-left-ℤ x y H
is-positive-gcd-ℤ x y (inr H) = is-positive-gcd-is-positive-right-ℤ x y H
```

### `gcd-ℤ a b` is zero if and only if both `a` and `b` are zero

```agda
is-zero-gcd-ℤ :
  (a b : ℤ) → is-zero-ℤ a → is-zero-ℤ b → is-zero-ℤ (gcd-ℤ a b)
is-zero-gcd-ℤ zero-ℤ zero-ℤ refl refl =
  ap int-ℕ is-zero-gcd-zero-zero-ℕ

is-zero-left-is-zero-gcd-ℤ :
  (a b : ℤ) → is-zero-ℤ (gcd-ℤ a b) → is-zero-ℤ a
is-zero-left-is-zero-gcd-ℤ a b =
  is-zero-is-zero-div-ℤ a (gcd-ℤ a b) (div-left-gcd-ℤ a b)

is-zero-right-is-zero-gcd-ℤ :
  (a b : ℤ) → is-zero-ℤ (gcd-ℤ a b) → is-zero-ℤ b
is-zero-right-is-zero-gcd-ℤ a b =
  is-zero-is-zero-div-ℤ b (gcd-ℤ a b) (div-right-gcd-ℤ a b)
```

### `gcd-ℤ` is commutative

```agda
is-commutative-gcd-ℤ : (x y : ℤ) → gcd-ℤ x y ＝ gcd-ℤ y x
is-commutative-gcd-ℤ x y =
  ap int-ℕ (is-commutative-gcd-ℕ (abs-ℤ x) (abs-ℤ y))
```

### `gcd-ℕ 1 b ＝ 1`

```agda
is-one-is-gcd-one-ℤ : {b x : ℤ} → is-gcd-ℤ one-ℤ b x → is-one-ℤ x
is-one-is-gcd-one-ℤ {b} {x} H with
  ( is-one-or-neg-one-is-unit-ℤ x
    ( is-unit-div-one-ℤ x (pr1 (is-common-divisor-is-gcd-ℤ one-ℤ b x H))))
... | inl p = p
... | inr p = ex-falso (tr is-nonnegative-ℤ p (pr1 H))

is-one-gcd-one-ℤ : (b : ℤ) → is-one-ℤ (gcd-ℤ one-ℤ b)
is-one-gcd-one-ℤ b = is-one-is-gcd-one-ℤ (is-gcd-gcd-ℤ one-ℤ b)
```

### `gcd-ℤ a 1 ＝ 1`

```agda
is-one-is-gcd-one-ℤ' : {a x : ℤ} → is-gcd-ℤ a one-ℤ x → is-one-ℤ x
is-one-is-gcd-one-ℤ' {a} {x} H with
  ( is-one-or-neg-one-is-unit-ℤ x
    ( is-unit-div-one-ℤ x (pr2 (is-common-divisor-is-gcd-ℤ a one-ℤ x H))))
... | inl p = p
... | inr p = ex-falso (tr is-nonnegative-ℤ p (pr1 H))

is-one-gcd-one-ℤ' : (a : ℤ) → is-one-ℤ (gcd-ℤ a one-ℤ)
is-one-gcd-one-ℤ' a = is-one-is-gcd-one-ℤ' (is-gcd-gcd-ℤ a one-ℤ)
```

### `gcd-ℤ 0 b ＝ abs-ℤ b`

```agda
is-sim-id-is-gcd-zero-ℤ : {b x : ℤ} → gcd-ℤ zero-ℤ b ＝ x → sim-unit-ℤ x b
is-sim-id-is-gcd-zero-ℤ {b} {x} H = antisymmetric-div-ℤ x b
  (pr2 (is-common-divisor-is-gcd-ℤ zero-ℤ b x
    (tr (λ t → is-gcd-ℤ zero-ℤ b t) H (
      is-gcd-gcd-ℤ zero-ℤ b))))
  (tr (λ t → div-ℤ b t) H
    (div-gcd-is-common-divisor-ℤ zero-ℤ b b
      (pair' (div-zero-ℤ b) (refl-div-ℤ b))))

is-id-is-gcd-zero-ℤ : {b x : ℤ} → gcd-ℤ zero-ℤ b ＝ x → x ＝ int-ℕ (abs-ℤ b)
is-id-is-gcd-zero-ℤ {inl b} {x} H
  with (is-plus-or-minus-sim-unit-ℤ (is-sim-id-is-gcd-zero-ℤ {inl b} {x} H))
... | inl p =
  ex-falso
    ( Eq-eq-ℤ
      ( inv (pr2 (lem (gcd-ℤ zero-ℤ (inl b)) gcd-is-nonneg)) ∙ (H ∙ p)))
  where
  gcd-is-nonneg : is-nonnegative-ℤ (gcd-ℤ zero-ℤ (inl b))
  gcd-is-nonneg = is-nonnegative-int-ℕ (gcd-ℕ 0 (succ-ℕ b))
  lem : (y : ℤ) → is-nonnegative-ℤ y → Σ (unit + ℕ) (λ z → y ＝ inr z)
  lem (inr z) H = pair z refl
... | inr p = inv (neg-neg-ℤ x) ∙ ap neg-ℤ p
is-id-is-gcd-zero-ℤ {inr (inl star)} {x} H =
  inv H ∙ is-zero-gcd-ℤ zero-ℤ zero-ℤ refl refl
is-id-is-gcd-zero-ℤ {inr (inr b)} {x} H
  with
  is-plus-or-minus-sim-unit-ℤ (is-sim-id-is-gcd-zero-ℤ {inr (inr b)} {x} H)
... | inl p = p
... | inr p =
  ex-falso
    ( Eq-eq-ℤ
      ( ( inv (pr2 (lem (gcd-ℤ zero-ℤ (inl b)) gcd-is-nonneg))) ∙
        ( H ∙ (inv (neg-neg-ℤ x) ∙ ap neg-ℤ p))))
  where
  gcd-is-nonneg : is-nonnegative-ℤ (gcd-ℤ zero-ℤ (inl b))
  gcd-is-nonneg = is-nonnegative-int-ℕ (gcd-ℕ 0 (succ-ℕ b))
  lem : (y : ℤ) → is-nonnegative-ℤ y → Σ (unit + ℕ) (λ z → y ＝ inr z)
  lem (inr z) H = pair z refl
```

### `gcd-ℤ a 0 ＝ abs-ℤ a`

```agda
is-sim-id-is-gcd-zero-ℤ' : {a x : ℤ} → gcd-ℤ a zero-ℤ ＝ x → sim-unit-ℤ x a
is-sim-id-is-gcd-zero-ℤ' {a} {x} H = is-sim-id-is-gcd-zero-ℤ {a} {x}
  ((is-commutative-gcd-ℤ zero-ℤ a) ∙ H)

is-id-is-gcd-zero-ℤ' : {a x : ℤ} → gcd-ℤ a zero-ℤ ＝ x → x ＝ int-ℕ (abs-ℤ a)
is-id-is-gcd-zero-ℤ' {a} {x} H =
  is-id-is-gcd-zero-ℤ {a} {x} (is-commutative-gcd-ℤ zero-ℤ a ∙ H)
```
