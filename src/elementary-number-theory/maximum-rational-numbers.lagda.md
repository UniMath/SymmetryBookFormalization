# Maximum on the rational numbers

```agda
module elementary-number-theory.maximum-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.coproduct-types
open import foundation.identity-types
open import foundation.transport-along-identifications

open import order-theory.decidable-total-orders
```

</details>

## Idea

We define the operation of maximum
([least upper bound](order-theory.least-upper-bounds-posets.md)) for the
[rational numbers](elementary-number-theory.rational-numbers.md).

## Definition

```agda
max-ℚ : ℚ → ℚ → ℚ
max-ℚ = max-Decidable-Total-Order ℚ-Decidable-Total-Order
```

## Properties

### Associativity of `max-ℚ`

```agda
associative-max-ℚ : (x y z : ℚ) → max-ℚ (max-ℚ x y) z ＝ max-ℚ x (max-ℚ y z)
associative-max-ℚ =
  associative-max-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### Commutativity of `max-ℚ`

```agda
commutative-max-ℚ : (x y : ℚ) → max-ℚ x y ＝ max-ℚ y x
commutative-max-ℚ =
  commutative-max-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### `max-ℚ` is idempotent

```agda
idempotent-max-ℚ : (x : ℚ) → max-ℚ x x ＝ x
idempotent-max-ℚ =
  idempotent-max-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### The maximum is an upper bound

```agda
leq-left-max-ℚ : (x y : ℚ) → x ≤-ℚ max-ℚ x y
leq-left-max-ℚ = leq-left-max-Decidable-Total-Order ℚ-Decidable-Total-Order

leq-right-max-ℚ : (x y : ℚ) → y ≤-ℚ max-ℚ x y
leq-right-max-ℚ = leq-right-max-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### If both `x` and `y` are less than `z`, so is their maximum

```agda
le-max-le-both-ℚ : (z x y : ℚ) → le-ℚ x z → le-ℚ y z → le-ℚ (max-ℚ x y) z
le-max-le-both-ℚ z x y x<z y<z with decide-le-leq-ℚ x y
... | inl x<y =
  inv-tr
    ( λ w → le-ℚ w z)
    ( left-leq-right-max-Decidable-Total-Order
      ( ℚ-Decidable-Total-Order)
      ( x)
      ( y)
      ( leq-le-ℚ {x} {y} x<y))
    ( y<z)
... | inr y≤x =
  inv-tr
    ( λ w → le-ℚ w z)
    ( right-leq-left-max-Decidable-Total-Order ℚ-Decidable-Total-Order x y y≤x)
    ( x<z)
```
