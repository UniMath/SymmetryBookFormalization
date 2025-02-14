# The weak limited principle of omniscience

```agda
module foundation.weak-limited-principle-of-omniscience where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.empty-types
open import foundation.function-types
open import foundation.inhabited-types
open import foundation.limited-principle-of-omniscience
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels
open import foundation.weak-law-of-excluded-middle

open import logic.de-morgan-types
```

</details>

## Statement

The {{#concept "weak limited principle of omniscience"}} (WLPO) asserts that
every [decidable subtype](foundation.decidable-subtypes.md) of the
[natural numbers](elementary-number-theory.natural-numbers.md) is either
[empty](foundation.empty-types.md) or it is not.

### Particular instances of the weak limited principle of omniscience

```agda
instance-WLPO-Prop : {l : Level} → decidable-subtype l ℕ → Prop l
instance-WLPO-Prop S =
  is-decidable-Prop (is-empty-Prop (type-decidable-subtype S))

instance-WLPO : {l : Level} → decidable-subtype l ℕ → UU l
instance-WLPO S = type-Prop (instance-WLPO-Prop S)
```

### The weak limited principle of omniscience

```agda
level-WLPO : (l : Level) → UU (lsuc l)
level-WLPO l = (S : decidable-subtype l ℕ) → instance-WLPO S

WLPO : UUω
WLPO = {l : Level} → level-WLPO l
```

## Properties

### The limited principle of omniscience implies the weak limited principle of omniscience

```agda
level-WLPO-LPO : {l : Level} → level-LPO l → level-WLPO l
level-WLPO-LPO l-lpo S with l-lpo S
... | inl inhabited-S =
  inr (λ empty-S → rec-trunc-Prop empty-Prop empty-S inhabited-S)
... | inr not-inhabited-S = inl (not-inhabited-S ∘ unit-trunc-Prop)

WLPO-LPO : LPO → WLPO
WLPO-LPO lpo = level-WLPO-LPO lpo
```

### The weak law of excluded middle implies the weak limited principle of omniscience

```agda
level-WLPO-WLEM : {l : Level} → level-WLEM l → level-WLPO l
level-WLPO-WLEM wlem S with wlem (is-inhabited-Prop (type-decidable-subtype S))
... | inl ¬S = inl (λ s → ¬S (unit-trunc-Prop s))
... | inr ¬¬S = inr (λ ¬S → ¬¬S (rec-trunc-Prop empty-Prop ¬S))

WLPO-WLEM : WLEM → WLPO
WLPO-WLEM wlem = level-WLPO-WLEM wlem
```

## Table of choice principles

{{#include tables/choice-principles.md}}

## See also

- [The principle of omniscience](foundation.principle-of-omniscience.md)
- [The limited principle of omniscience](foundation.limited-principle-of-omniscience.md)
- [The lesser limited principle of omniscience](foundation.lesser-limited-principle-of-omniscience.md)
- [Markov's principle](logic.markovs-principle.md)

## External links

- [Taboos.WLPO](https://martinescardo.github.io/TypeTopology/Taboos.WLPO.html)
  at TypeTopology
- [weak limited principle of omniscience](https://ncatlab.org/nlab/show/weak+limited+principle+of+omniscience)
  at $n$Lab
