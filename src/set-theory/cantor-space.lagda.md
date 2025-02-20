# Cantor space

```agda
module set-theory.cantor-space where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.double-negation-stable-equality
open import foundation.empty-types
open import foundation.lawveres-fixed-point-theorem
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.tight-apartness-relations
open import foundation.unit-type
open import foundation.universe-levels

open import set-theory.cantors-diagonal-argument
open import set-theory.countable-sets
open import set-theory.uncountable-sets

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "Cantor space" Disambiguation="as a type" Agda=cantor-space WD="Cantor space" WDID=Q616653}}
is the [set](foundation-core.sets.md) of
[functions](foundation-core.function-types.md) `ℕ → bool`. In other words, it is
the set of [binary](foundation.booleans.md)
[sequences](foundation.sequences.md).

## Definition

```agda
cantor-space : UU lzero
cantor-space = ℕ → bool
```

## Properties

### The cantor space has a tight apartness relation

```agda
tight-apartness-relation-cantor-space :
  Tight-Apartness-Relation lzero cantor-space
tight-apartness-relation-cantor-space =
  tight-apartness-relation-function-into-Type-With-Tight-Apartness
    ℕ
    bool-Type-With-Tight-Apartness

cantor-space-Type-With-Tight-Apartness : Type-With-Tight-Apartness lzero lzero
cantor-space-Type-With-Tight-Apartness =
  function-into-Type-With-Tight-Apartness ℕ bool-Type-With-Tight-Apartness
```

### The cantor space has double negation stable equality

```agda
has-double-negation-stable-equality-cantor-space :
  has-double-negation-stable-equality cantor-space
has-double-negation-stable-equality-cantor-space =
  has-double-negation-stable-equality-type-Type-With-Tight-Apartness
    cantor-space-Type-With-Tight-Apartness
```

### The cantor space is a set

```agda
is-set-cantor-space : is-set cantor-space
is-set-cantor-space = is-set-function-type is-set-bool

cantor-space-Set : Set lzero
cantor-space-Set = (cantor-space , is-set-cantor-space)
```

### The cantor space is uncountable

```agda
is-uncountable-cantor-space : is-uncountable cantor-space-Set
is-uncountable-cantor-space =
  is-uncountable-sequence-discrete-type-diagonal-argument-Cantor
    ( bool-Discrete-Type)
    ( true)
    ( false)
    ( neq-true-false-bool)
```

## External links

- [Cantor space](https://en.wikipedia.org/wiki/Cantor_space) at Wikipedia
- [Cantor space](https://ncatlab.org/nlab/show/Cantor+space) at $n$Lab
