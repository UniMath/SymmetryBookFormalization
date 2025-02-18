# Fiber sequences

```agda
module synthetic-homotopy-theory.fiber-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospan-diagrams
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.families-of-equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-fibers-of-maps
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inverse-sequential-diagrams
open import foundation.pullbacks
open import foundation.standard-pullbacks
open import foundation.unit-type
open import foundation.universal-property-pullbacks
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.fiber-inclusions-of-maps
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

A [sequential diagram](foundation.inverse-sequential-diagrams.md) of pointed
types and maps that extend infinitely to the left

```text
     f₃      f₂      f₁      f₀
  ⋯ ---> A₃ ---> A₂ ---> A₁ ---> A₀
```

is a {{#concept "fiber sequence" Agda=fiber-sequence}} if every pair of
consecutive maps is a
[fiber inclusion](synthetic-homotopy-theory.fiber-inclusions-of-maps.md)

```text
        fₙ₊₁
  Aₙ₊₂ -----> Aₙ₊₁
  | ⌟         |
  |           | fₙ
  ∨           ∨
  * --------> Aₙ.
```

## Definitions

### The predicate of being a fiber sequence

```agda
module _
  {l : Level} (A : (n : ℕ) → Pointed-Type l)
  (f : (n : ℕ) → type-Pointed-Type (A (succ-ℕ n)) → type-Pointed-Type (A n))
  where

  is-fiber-sequence : UU l
  is-fiber-sequence =
    (n : ℕ) →
    is-fiber-inclusion-of-map (f n) (point-Pointed-Type (A n)) (f (succ-ℕ n))
```

### The type of fiber sequences

```agda
fiber-sequence : (l : Level) → UU (lsuc l)
fiber-sequence l =
  Σ ( (n : ℕ) → Pointed-Type l)
    ( λ A →
      Σ ( (n : ℕ) → type-Pointed-Type (A (succ-ℕ n)) → type-Pointed-Type (A n))
        ( is-fiber-sequence A))
```
