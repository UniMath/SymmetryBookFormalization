# Minimum on the rational numbers

```agda
module elementary-number-theory.minimum-rational-numbers where
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

We define the operation of minimum
([greatest lower bound](order-theory.greatest-lower-bounds-posets.md)) for the
[rational numbers](elementary-number-theory.rational-numbers.md).

## Definition

```agda
min-ℚ : ℚ → ℚ → ℚ
min-ℚ = min-Decidable-Total-Order ℚ-Decidable-Total-Order
```

## Properties

### Associativity of `min-ℚ`

```agda
associative-min-ℚ : (x y z : ℚ) → min-ℚ (min-ℚ x y) z ＝ min-ℚ x (min-ℚ y z)
associative-min-ℚ =
  associative-min-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### Commutativity of `min-ℚ`

```agda
commutative-min-ℚ : (x y : ℚ) → min-ℚ x y ＝ min-ℚ y x
commutative-min-ℚ =
  commutative-min-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### `min-ℚ` is idempotent

```agda
idempotent-min-ℚ : (x : ℚ) → min-ℚ x x ＝ x
idempotent-min-ℚ =
  idempotent-min-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### The minimum is a lower bound

```agda
leq-left-min-ℚ : (x y : ℚ) → min-ℚ x y ≤-ℚ x
leq-left-min-ℚ = leq-left-min-Decidable-Total-Order ℚ-Decidable-Total-Order

leq-right-min-ℚ : (x y : ℚ) → min-ℚ x y ≤-ℚ y
leq-right-min-ℚ = leq-right-min-Decidable-Total-Order ℚ-Decidable-Total-Order
```

### If `z` is less than both `x` and `y`, it is less than their minimum

```agda
le-min-le-both-ℚ : (z x y : ℚ) → le-ℚ z x → le-ℚ z y → le-ℚ z (min-ℚ x y)
le-min-le-both-ℚ z x y z<x z<y with decide-le-leq-ℚ x y
... | inl x<y =
  inv-tr
    ( le-ℚ z)
    ( left-leq-right-min-Decidable-Total-Order
      ( ℚ-Decidable-Total-Order)
      ( x)
      ( y)
      ( leq-le-ℚ {x} {y} x<y))
    ( z<x)
... | inr y≤x =
  inv-tr
    ( le-ℚ z)
    ( right-leq-left-min-Decidable-Total-Order ℚ-Decidable-Total-Order x y y≤x)
    ( z<y)
```
