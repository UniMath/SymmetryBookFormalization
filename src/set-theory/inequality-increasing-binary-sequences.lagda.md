# Inequality of increasing binary sequences

```agda
module set-theory.inequality-increasing-binary-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.constant-maps
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.double-negation-stable-equality
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.homotopies
open import foundation.inequality-booleans
open import foundation.injective-maps
open import foundation.logical-operations-booleans
open import foundation.maybe
open import foundation.negated-equality
open import foundation.propositions
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.tight-apartness-relations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.identity-types

open import order-theory.order-preserving-maps-posets
open import order-theory.posets
open import order-theory.preorders
open import order-theory.total-orders

open import set-theory.cantor-space
open import set-theory.increasing-binary-sequences
```

</details>

## Idea

Given two
[increasing binary sequences](set-theory.inequality-increasing-binary-sequences.md)
`x` and `y`, then `x` is _less than or equal_ to `y` if `yᵢ ≤ xᵢ` for every
`i : ℕ`. This defines the
{{#concept "standard inequality" Disambiguation="on increasing binary sequences" Agda=leq-ℕ∞↑}}
relation on increasing binary sequences.

## Definitions

```agda
leq-ℕ∞↑ : ℕ∞↑ → ℕ∞↑ → UU lzero
leq-ℕ∞↑ x y = (n : ℕ) → leq-bool (sequence-ℕ∞↑ y n) (sequence-ℕ∞↑ x n)

infix 30 _≤-ℕ∞↑_
_≤-ℕ∞↑_ : ℕ∞↑ → ℕ∞↑ → UU lzero
_≤-ℕ∞↑_ = leq-ℕ∞↑

is-prop-leq-ℕ∞↑ : (x y : ℕ∞↑) → is-prop (x ≤-ℕ∞↑ y)
is-prop-leq-ℕ∞↑ x y =
  is-prop-Π (λ n → is-prop-leq-bool {sequence-ℕ∞↑ y n} {sequence-ℕ∞↑ x n})

leq-prop-ℕ∞↑ : ℕ∞↑ → ℕ∞↑ → Prop lzero
leq-prop-ℕ∞↑ x y = (leq-ℕ∞↑ x y , is-prop-leq-ℕ∞↑ x y)
```

## Properties

### Inequality of increasing binary sequences is reflexive

```agda
abstract
  refl-leq-ℕ∞↑ :
    (x : ℕ∞↑) → leq-ℕ∞↑ x x
  refl-leq-ℕ∞↑ x n =
    refl-leq-bool {sequence-ℕ∞↑ x n}

abstract
  leq-Eq-ℕ∞↑' :
    (x y : ℕ∞↑) →
    Eq-ℕ∞↑ y x → leq-ℕ∞↑ x y
  leq-Eq-ℕ∞↑' x y H = leq-eq-bool ∘ H

abstract
  leq-Eq-ℕ∞↑ :
    (x y : ℕ∞↑) →
    Eq-ℕ∞↑ x y → leq-ℕ∞↑ x y
  leq-Eq-ℕ∞↑ x y H =
    leq-Eq-ℕ∞↑' x y (inv-htpy H)

abstract
  leq-eq-ℕ∞↑ :
    (x y : ℕ∞↑) →
    x ＝ y → leq-ℕ∞↑ x y
  leq-eq-ℕ∞↑ x .x refl =
    refl-leq-ℕ∞↑ x
```

### Inequality of increasing binary sequences is transitive

```agda
transitive-leq-ℕ∞↑ :
  (x y z : ℕ∞↑) → y ≤-ℕ∞↑ z → x ≤-ℕ∞↑ y → x ≤-ℕ∞↑ z
transitive-leq-ℕ∞↑ x y z p q n =
  transitive-leq-bool
    { sequence-ℕ∞↑ z n}
    { sequence-ℕ∞↑ y n}
    { sequence-ℕ∞↑ x n}
    ( q n)
    ( p n)
```

### Inequality of increasing binary sequences is antisymmetric

```agda
antisymmetric-leq-ℕ∞↑ :
  (x y : ℕ∞↑) → x ≤-ℕ∞↑ y → y ≤-ℕ∞↑ x → x ＝ y
antisymmetric-leq-ℕ∞↑ x y p q =
  eq-Eq-ℕ∞↑
    ( λ n →
      antisymmetric-leq-bool
        { sequence-ℕ∞↑ x n}
        { sequence-ℕ∞↑ y n}
        ( q n)
        ( p n))
```

### The poset of increasing binary sequences

```agda
is-preorder-leq-ℕ∞↑ :
  is-preorder-Relation-Prop leq-prop-ℕ∞↑
is-preorder-leq-ℕ∞↑ =
  ( refl-leq-ℕ∞↑ ,
    transitive-leq-ℕ∞↑)

ℕ∞↑-Preorder : Preorder lzero lzero
ℕ∞↑-Preorder =
  ( ℕ∞↑ ,
    leq-prop-ℕ∞↑ ,
    is-preorder-leq-ℕ∞↑)

ℕ∞↑-Poset : Poset lzero lzero
ℕ∞↑-Poset =
  ( ℕ∞↑-Preorder ,
    antisymmetric-leq-ℕ∞↑)
```

### The successor function preserves order

```agda
preserves-order-succ-ℕ∞↑ :
  (x y : ℕ∞↑) → x ≤-ℕ∞↑ y → (succ-ℕ∞↑ x) ≤-ℕ∞↑ (succ-ℕ∞↑ y)
preserves-order-succ-ℕ∞↑ x y p zero-ℕ = star
preserves-order-succ-ℕ∞↑ x y p (succ-ℕ n) = p n
```

### The successor function is inflationary

```agda
leq-succ-ℕ∞↑ : (x : ℕ∞↑) → x ≤-ℕ∞↑ (succ-ℕ∞↑ x)
leq-succ-ℕ∞↑ x zero-ℕ = star
leq-succ-ℕ∞↑ x (succ-ℕ n) = is-increasing-sequence-ℕ∞↑ x n
```

### Zero is the smallest element

```agda
leq-zero-ℕ∞↑ : (x : ℕ∞↑) → zero-ℕ∞↑ ≤-ℕ∞↑ x
leq-zero-ℕ∞↑ x n = leq-true-bool {sequence-ℕ∞↑ x n}

Eq-leq-zero-ℕ∞↑ :
  (x : ℕ∞↑) → x ≤-ℕ∞↑ zero-ℕ∞↑ → Eq-ℕ∞↑ x zero-ℕ∞↑
Eq-leq-zero-ℕ∞↑ x p = eq-leq-true-bool ∘ p

eq-leq-zero-ℕ∞↑ : (x : ℕ∞↑) → x ≤-ℕ∞↑ zero-ℕ∞↑ → x ＝ zero-ℕ∞↑
eq-leq-zero-ℕ∞↑ x p = eq-Eq-ℕ∞↑ (Eq-leq-zero-ℕ∞↑ x p)
```

### Infinity is the largest element

```agda
infinity-leq-ℕ∞↑ : (x : ℕ∞↑) → x ≤-ℕ∞↑ infinity-ℕ∞↑
infinity-leq-ℕ∞↑ x n = leq-false-bool {sequence-ℕ∞↑ x n}

Eq-leq-infinity-ℕ∞↑ : (x : ℕ∞↑) → infinity-ℕ∞↑ ≤-ℕ∞↑ x → Eq-ℕ∞↑ x infinity-ℕ∞↑
Eq-leq-infinity-ℕ∞↑ x p = eq-leq-false-bool ∘ p

eq-leq-infinity-ℕ∞↑ : (x : ℕ∞↑) → infinity-ℕ∞↑ ≤-ℕ∞↑ x → x ＝ infinity-ℕ∞↑
eq-leq-infinity-ℕ∞↑ x p = eq-Eq-ℕ∞↑ (Eq-leq-infinity-ℕ∞↑ x p)
```
