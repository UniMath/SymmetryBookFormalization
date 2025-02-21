# Indiscrete types

```agda
module foundation.indiscrete-types where
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
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.isolated-elements
open import foundation.universe-levels

open import foundation-core.identity-types

open import orthogonal-factorization-systems.null-types
open import orthogonal-factorization-systems.types-local-at-maps

open import set-theory.inclusion-natural-numbers-increasing-binary-sequences
open import set-theory.increasing-binary-sequences
```

</details>

## Idea

A type `A` is {{#concept "indiscrete" Disambiguation="type" Agda=is-indiscrete}}
if it is [local](orthogonal-factorization-systems.types-local-at-maps.md) at the
map

```text
  ℕ+{∞} → ℕ∞.
```

This defines a topological (duh!)
[modality](orthogonal-factorization-systems.higher-modalities.md) presented by
the predicate that `∞` is an isolated element in `ℕ∞`.

The terminology _indiscrete_ is justified by the topological model of type
theory: a type is indiscrete if and only if every sequence of points converges
to every element.

## Definitions

### The predicate of being indiscrete

```agda
is-indiscrete' : {l : Level} → UU l → UU l
is-indiscrete' A = is-local inclusion-ℕ∞↑-Maybe-ℕ A

is-indiscrete : {l : Level} → UU l → UU l
is-indiscrete A = (n : ℕ∞↑) → is-null (is-decidable (infinity-ℕ∞↑ ＝ n)) A
```

### The type of indiscrete types

```agda
Indiscrete-Type : (l : Level) → UU (lsuc l)
Indiscrete-Type l = Σ (UU l) (is-indiscrete)

module _
  {l : Level} (X : Indiscrete-Type l)
  where

  type-Indiscrete-Type : UU l
  type-Indiscrete-Type = pr1 X

  is-indiscrete-type-Indiscrete-Type : is-indiscrete type-Indiscrete-Type
  is-indiscrete-type-Indiscrete-Type = pr2 X
```

## Properties

### A type is local at the inclusion `ℕ+{∞} → ℕ∞` if and only if it views `∞` as isolated

> This remains to be formalized.

### Indiscrete types are closed under dependent sums

This is a corollary of being a topological modality.

> This remains to be formalized.

### Indiscrete types are closed under dependent products

This is a corollary of being a topological modality.

> This remains to be formalized.

### The identity types of an indiscrete type are indiscrete

This is a corollary of being a topological modality.

> This remains to be formalized.

## Conjectures

### If the booleans are indiscrete, then the weak limited principle of omniscience holds

> This remains to be formalized.

### Indiscrete types are logically compact

> This remains to be formalized.
