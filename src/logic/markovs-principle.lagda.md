# Markov's principle

```agda
module logic.markovs-principle where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.inhabited-types
open import foundation.negation
open import foundation.universal-quantification
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets

open import logic.markovian-types

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

{{#concept "Markov's principle" WDID=Q3922074 WD="Markov's principle" Agda=Markov's-Principle}}
asserts that if a [decidable subtype](foundation.decidable-subtypes.md) `𝒫` of
the [natural numbers](elementary-number-theory.natural-numbers.md) `ℕ` is not
[full](foundation.full-subtypes.md), then
[there is](foundation.existential-quantification.md) a natural number `n` that
is not in `𝒫`.

Markov's principle is an example of a _constructive taboo_. It is a consequence
of the [law of excluded middle](foundation.law-of-excluded-middle.md) that is
not provable generally in constructive mathematics.

## Definitions

### Markov's principle

```agda
Markov's-Principle : UU lzero
Markov's-Principle = is-markovian ℕ
```

## Properties

### Markov's principle is constructively valid for upwards closed subtypes

**Proof.** Assume given an ascending chain of decidable propositions `Pᵢ ⇒ Pᵢ₊₁`
indexed by the natural numbers `ℕ`. This gives a decidable subtype `𝒫` of `ℕ`
given by `i ∈ 𝒫` iff `Pᵢ` is true. Observe that if `i ∈ 𝒫` then every `j ≥ i` is
also in `𝒫`, and there must exist a least such `i ∈ 𝒫`. Therefore,
`𝒫 = Σ (m ∈ ℕ) (m ≥ k)` for some `k`. So, if `¬ (∀ᵢ Pᵢ)` it is necessarily the
case that `¬ P₀`.

```agda
markovs-principle-upwards-closed-structure :
  {l : Level} (P : ℕ → UU l)
  (H : (n : ℕ) → P n → P (succ-ℕ n)) → ¬ ((n : ℕ) → P n) → Σ ℕ (¬_ ∘ P)
markovs-principle-upwards-closed-structure P H q = (0 , λ x → q (ind-ℕ x H))
```

## Table of choice principles

{{#include tables/choice-principles.md}}

## External links

- [Taboos.MarkovsPrinciple](https://martinescardo.github.io/TypeTopology/Taboos.MarkovsPrinciple.html)
  at TypeTopology
- [limited principle of omniscience](https://ncatlab.org/nlab/show/limited+principle+of+omniscience)
  at $n$Lab
