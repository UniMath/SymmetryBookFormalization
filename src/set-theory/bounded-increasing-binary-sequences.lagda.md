# Bounded increasing binary sequences

```agda
module set-theory.bounded-increasing-binary-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-natural-numbers
open import elementary-number-theory.equality-natural-numbers
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
open import foundation.homotopies
open import foundation.inequality-booleans
open import foundation.injective-maps
open import foundation.logical-operations-booleans
open import foundation.maybe
open import foundation.negated-equality
open import foundation.negation
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

open import logic.double-negation-dense-maps
open import logic.double-negation-eliminating-maps

open import order-theory.order-preserving-maps-posets
open import order-theory.posets
open import order-theory.subposets

open import set-theory.cantor-space
open import set-theory.finite-elements-increasing-binary-sequences
open import set-theory.increasing-binary-sequences
open import set-theory.inequality-increasing-binary-sequences
```

</details>

## Idea

Given an [increasing binary sequence](set-theory.increasing-binary-sequences.md)
`n`, then another increasing binary sequence `x` is
{{#concept "bounded" Disambiguation="increasing binary sequence by increasing binary sequence" Agda=bounded-ℕ∞↑}}
if `x ≤ n`.

## Definitions

### Bounded increasing binary sequences

```agda
bounded-ℕ∞↑ : (n : ℕ∞↑) → UU lzero
bounded-ℕ∞↑ n = Σ ℕ∞↑ (_≤-ℕ∞↑ n)

module _
  (n : ℕ∞↑) (k : bounded-ℕ∞↑ n)
  where

  increasing-binary-sequence-bounded-ℕ∞↑ : ℕ∞↑
  increasing-binary-sequence-bounded-ℕ∞↑ = pr1 k

  sequence-bounded-ℕ∞↑ : ℕ → bool
  sequence-bounded-ℕ∞↑ = sequence-ℕ∞↑ increasing-binary-sequence-bounded-ℕ∞↑

  is-increasing-sequence-bounded-ℕ∞↑ :
    is-increasing-binary-sequence sequence-bounded-ℕ∞↑
  is-increasing-sequence-bounded-ℕ∞↑ =
    is-increasing-sequence-ℕ∞↑ increasing-binary-sequence-bounded-ℕ∞↑

  is-bounded-bounded-ℕ∞↑ : increasing-binary-sequence-bounded-ℕ∞↑ ≤-ℕ∞↑ n
  is-bounded-bounded-ℕ∞↑ = pr2 k

abstract
  is-set-bounded-ℕ∞↑ : (n : ℕ∞↑) → is-set (bounded-ℕ∞↑ n)
  is-set-bounded-ℕ∞↑ n = is-set-type-subtype (λ k → leq-prop-ℕ∞↑ k n) is-set-ℕ∞↑
```

### Successor-bounded increasing binary sequences

```agda
succ-bounded-ℕ∞↑ : (n : ℕ∞↑) → UU lzero
succ-bounded-ℕ∞↑ n = Σ ℕ∞↑ (λ k → (succ-ℕ∞↑ k) ≤-ℕ∞↑ n)

module _
  (n : ℕ∞↑) (k : succ-bounded-ℕ∞↑ n)
  where

  increasing-binary-sequence-succ-bounded-ℕ∞↑ : ℕ∞↑
  increasing-binary-sequence-succ-bounded-ℕ∞↑ = pr1 k

  sequence-succ-bounded-ℕ∞↑ : ℕ → bool
  sequence-succ-bounded-ℕ∞↑ =
    sequence-ℕ∞↑ increasing-binary-sequence-succ-bounded-ℕ∞↑

  is-increasing-sequence-succ-bounded-ℕ∞↑ :
    is-increasing-binary-sequence sequence-succ-bounded-ℕ∞↑
  is-increasing-sequence-succ-bounded-ℕ∞↑ =
    is-increasing-sequence-ℕ∞↑ increasing-binary-sequence-succ-bounded-ℕ∞↑

  is-succ-bounded-succ-bounded-ℕ∞↑ :
    succ-ℕ∞↑ increasing-binary-sequence-succ-bounded-ℕ∞↑ ≤-ℕ∞↑ n
  is-succ-bounded-succ-bounded-ℕ∞↑ = pr2 k

  bounded-succ-succ-bounded-ℕ∞↑ : bounded-ℕ∞↑ n
  bounded-succ-succ-bounded-ℕ∞↑ =
    ( succ-ℕ∞↑ increasing-binary-sequence-succ-bounded-ℕ∞↑ ,
      is-succ-bounded-succ-bounded-ℕ∞↑)

  is-bounded-succ-bounded-ℕ∞↑ :
    increasing-binary-sequence-succ-bounded-ℕ∞↑ ≤-ℕ∞↑ n
  is-bounded-succ-bounded-ℕ∞↑ =
    transitive-leq-ℕ∞↑
      ( increasing-binary-sequence-succ-bounded-ℕ∞↑)
      ( succ-ℕ∞↑ increasing-binary-sequence-succ-bounded-ℕ∞↑)
      ( n)
      ( is-succ-bounded-succ-bounded-ℕ∞↑)
      ( leq-succ-ℕ∞↑ increasing-binary-sequence-succ-bounded-ℕ∞↑)

  bounded-succ-bounded-ℕ∞↑ : bounded-ℕ∞↑ n
  bounded-succ-bounded-ℕ∞↑ =
    ( increasing-binary-sequence-succ-bounded-ℕ∞↑ , is-bounded-succ-bounded-ℕ∞↑)

abstract
  is-set-succ-bounded-ℕ∞↑ : (n : ℕ∞↑) → is-set (succ-bounded-ℕ∞↑ n)
  is-set-succ-bounded-ℕ∞↑ n =
    is-set-type-subtype (λ k → leq-prop-ℕ∞↑ (succ-ℕ∞↑ k) n) is-set-ℕ∞↑
```

### Inequality on bounded increasing binary sequences

```agda
module _
  (n : ℕ∞↑)
  where

  bounded-ℕ∞↑-Poset : Poset lzero lzero
  bounded-ℕ∞↑-Poset = poset-Subposet ℕ∞↑-Poset (λ k → leq-prop-ℕ∞↑ k n)

  leq-bounded-ℕ∞↑ : (x y : bounded-ℕ∞↑ n) → UU lzero
  leq-bounded-ℕ∞↑ = leq-Poset bounded-ℕ∞↑-Poset

  leq-prop-bounded-ℕ∞↑ : (x y : bounded-ℕ∞↑ n) → Prop lzero
  leq-prop-bounded-ℕ∞↑ = leq-prop-Poset bounded-ℕ∞↑-Poset

  refl-leq-bounded-ℕ∞↑ : (x : bounded-ℕ∞↑ n) → leq-bounded-ℕ∞↑ x x
  refl-leq-bounded-ℕ∞↑ = refl-leq-Poset bounded-ℕ∞↑-Poset

  transitive-leq-bounded-ℕ∞↑ :
    (x y z : bounded-ℕ∞↑ n) →
    leq-bounded-ℕ∞↑ y z → leq-bounded-ℕ∞↑ x y → leq-bounded-ℕ∞↑ x z
  transitive-leq-bounded-ℕ∞↑ = transitive-leq-Poset bounded-ℕ∞↑-Poset

  antisymmetric-leq-bounded-ℕ∞↑ :
    (x y : bounded-ℕ∞↑ n) → leq-bounded-ℕ∞↑ x y → leq-bounded-ℕ∞↑ y x → x ＝ y
  antisymmetric-leq-bounded-ℕ∞↑ = antisymmetric-leq-Poset bounded-ℕ∞↑-Poset
```

### The zero element

```agda
zero-bounded-ℕ∞↑ : (n : ℕ∞↑) → bounded-ℕ∞↑ n
zero-bounded-ℕ∞↑ n = (zero-ℕ∞↑ , leq-zero-ℕ∞↑ n)
```

### The successor function

```agda
inclusion-bounded-succ-bounded-ℕ∞↑ :
  (n : ℕ∞↑) → bounded-ℕ∞↑ n → bounded-ℕ∞↑ (succ-ℕ∞↑ n)
inclusion-bounded-succ-bounded-ℕ∞↑ n x =
  ( increasing-binary-sequence-bounded-ℕ∞↑ n x ,
    transitive-leq-ℕ∞↑
      ( increasing-binary-sequence-bounded-ℕ∞↑ n x)
      ( n)
      ( succ-ℕ∞↑ n)
      ( leq-succ-ℕ∞↑ n)
      ( is-bounded-bounded-ℕ∞↑ n x))

inclusion-succ-bounded-ℕ∞↑ :
  (n : ℕ∞↑) → bounded-ℕ∞↑ n → bounded-ℕ∞↑ (succ-ℕ∞↑ n)
inclusion-succ-bounded-ℕ∞↑ n x =
  ( succ-ℕ∞↑ (increasing-binary-sequence-bounded-ℕ∞↑ n x) ,
    preserves-order-succ-ℕ∞↑
      ( increasing-binary-sequence-bounded-ℕ∞↑ n x)
      ( n)
      ( is-bounded-bounded-ℕ∞↑ n x))
```

### Every increasing binary sequence is bounded by itself

```agda
self-bounded-ℕ∞↑ : (n : ℕ∞↑) → bounded-ℕ∞↑ n
self-bounded-ℕ∞↑ n = (n , refl-leq-ℕ∞↑ n)
```

## Properties

### Bounded increasing binary sequences have tight apartness

```agda
bounded-ℕ∞↑-Type-With-Tight-Apartness :
  ℕ∞↑ → Type-With-Tight-Apartness lzero lzero
bounded-ℕ∞↑-Type-With-Tight-Apartness n =
  subtype-Type-With-Tight-Apartness
    ( ℕ∞↑-Type-With-Tight-Apartness)
    ( λ k → leq-prop-ℕ∞↑ k n)
```

### Bounded increasing binary sequences have double negation stable equality

```agda
has-double-negation-stable-equality-bounded-ℕ∞↑ :
  (n : ℕ∞↑) → has-double-negation-stable-equality (bounded-ℕ∞↑ n)
has-double-negation-stable-equality-bounded-ℕ∞↑ n =
  has-double-negation-stable-equality-type-Type-With-Tight-Apartness
    ( bounded-ℕ∞↑-Type-With-Tight-Apartness n)
```

### If `n` is finite then `bounded-ℕ∞↑ n` is a finite set with `n + 1` elements

> TODO
