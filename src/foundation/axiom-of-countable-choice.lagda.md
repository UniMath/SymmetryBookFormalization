# The axiom of countable choice

```agda
module foundation.axiom-of-countable-choice where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.axiom-of-choice
open import foundation.function-types
open import foundation.inhabited-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "axiom of countable choice" WD="axiom of countable choice" WDID=Q1000116 Agda=ACω}}
asserts that for every family of [inhabited](foundation.inhabited-types.md)
types `F` indexed by the type `ℕ` of
[natural numbers](elementary-number-theory.natural-numbers.md), the type of
sections of that family `(n : ℕ) → B n` is inhabited.

## Definition

### Instances of choice

```agda
instance-countable-choice : {l : Level} → (ℕ → Set l) → UU l
instance-countable-choice F =
  ((n : ℕ) → is-inhabited (type-Set (F n))) →
  is-inhabited ((n : ℕ) → type-Set (F n))
```

### The axiom of countable choice

```agda
level-countable-choice : (l : Level) → UU (lsuc l)
level-countable-choice l = (F : ℕ → Set l) → instance-countable-choice F

axiom-of-countable-choice : UUω
axiom-of-countable-choice = {l : Level} → level-countable-choice l
```

## Properties

### The axiom of choice for sets implies the axiom of countable choice

```agda
level-countable-choice-level-axiom-of-choice-Set :
  {l : Level} → level-axiom-of-choice-Set lzero l → level-countable-choice l
level-countable-choice-level-axiom-of-choice-Set ac-l = ac-l ℕ-Set

countable-choice-axiom-of-choice-Set :
  axiom-of-choice-Set → axiom-of-countable-choice
countable-choice-axiom-of-choice-Set ac =
  level-countable-choice-level-axiom-of-choice-Set ac
```

## Table of choice principles

{{#include tables/choice-principles.md}}

## External links

- [Axiom of countable choice](https://ncatlab.org/nlab/show/countable+choice) at
  nLab
