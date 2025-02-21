# Baire space

```agda
module set-theory.baire-space where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.double-negation-stable-equality
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.lawveres-fixed-point-theorem
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.tight-apartness-relations
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.identity-types
open import foundation-core.propositions

open import set-theory.cantors-diagonal-argument
open import set-theory.countable-sets
open import set-theory.uncountable-sets
```

</details>

## Idea

The
{{#concept "Baire space" Disambiguation="as a type" Agda=baire-space WD="Baire space" WDID=Q803936}}
is the [set](foundation-core.sets.md) of
[functions](foundation-core.function-types.md) `ℕ → ℕ`. In other words, it is
the set of infinite [sequences](foundation.sequences.md) of
[natural numbers](elementary-number-theory.natural-numbers.md).

## Definition

```agda
baire-space : UU lzero
baire-space = ℕ → ℕ
```

## Properties

### The Baire space has a tight apartness relation

```agda
tight-apartness-relation-baire-space :
  Tight-Apartness-Relation lzero baire-space
tight-apartness-relation-baire-space =
  tight-apartness-relation-function-into-Type-With-Tight-Apartness
    ℕ
    ℕ-Type-With-Tight-Apartness

baire-space-Type-With-Tight-Apartness : Type-With-Tight-Apartness lzero lzero
baire-space-Type-With-Tight-Apartness =
  function-into-Type-With-Tight-Apartness ℕ ℕ-Type-With-Tight-Apartness
```

### The Baire space has double negation stable equality

```agda
has-double-negation-stable-equality-baire-space :
  has-double-negation-stable-equality baire-space
has-double-negation-stable-equality-baire-space =
  has-double-negation-stable-equality-type-Type-With-Tight-Apartness
    baire-space-Type-With-Tight-Apartness
```

### The Baire space is a set

```agda
is-set-baire-space : is-set baire-space
is-set-baire-space = is-set-function-type is-set-ℕ

baire-space-Set : Set lzero
baire-space-Set = (baire-space , is-set-baire-space)
```

### The Baire space is uncountable

We give two proofs. The first proof uses that the successor function on the
nautral numbers has no fixed points and applies
[Lawvere's fixed point theorem](foundation.lawveres-fixed-point-theorem.md). The
second proof uses that equality on the natural numbers is
[decidable](foundation.decidable-types.md), and applies
[Cantor's diagonal argument](set-theory.cantors-diagonal-argument.md).

```agda
abstract
  is-uncountable-baire-space : is-uncountable baire-space-Set
  is-uncountable-baire-space P =
    apply-universal-property-trunc-Prop
      ( is-directly-countable-is-countable baire-space-Set succ-ℕ P)
      ( empty-Prop)
      ( λ H →
        apply-universal-property-trunc-Prop
          ( fixed-point-theorem-Lawvere (pr2 H) succ-ℕ)
          ( empty-Prop)
          ( λ F →
            reductio-ad-absurdum (pr2 F) (has-no-fixed-points-succ-ℕ (pr1 F))))

abstract
  is-uncountable-baire-space' : is-uncountable baire-space-Set
  is-uncountable-baire-space' =
    is-uncountable-sequence-discrete-type-diagonal-argument-Cantor
      ( ℕ-Discrete-Type)
      ( 0)
      ( 1)
      ( is-nonzero-one-ℕ ∘ inv)
```

## External links

- [Baire space (set theory)](<https://en.wikipedia.org/wiki/Baire_space_(set_theory)>)
  at Wikipedia
- [Baire space of sequences](https://ncatlab.org/nlab/show/Baire+space+of+sequences)
  at $n$Lab
