# The limited principle of omniscience

```agda
module foundation.limited-principle-of-omniscience where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.principle-of-omniscience
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Statement

The
{{#concept "limited principle of omniscience" WDID=Q6549544 WD="limited principle of omniscience" Agda=LPO}}
(LPO) asserts that every [decidable subtype](foundation.decidable-subtypes.md)
of the [natural numbers](elementary-number-theory.natural-numbers.md) is either
[inhabited](foundation.inhabited-types.md) or
[empty](foundation.empty-types.md).

### Instances of LPO

```agda
instance-LPO-Prop : {l : Level} → decidable-subtype l ℕ → Prop l
instance-LPO-Prop S = is-decidable-Prop (trunc-Prop (type-decidable-subtype S))

instance-LPO : {l : Level} → decidable-subtype l ℕ → UU l
instance-LPO S = type-Prop (instance-LPO-Prop S)
```

### The limited principle of omniscience

```agda
level-LPO : (l : Level) → UU (lsuc l)
level-LPO l = (S : decidable-subtype l ℕ) → instance-LPO S

LPO : UUω
LPO = {l : Level} → level-LPO l
```

## Table of choice principles

{{#include tables/choice-principles.md}}

## External links

- [Taboos.LPO](https://martinescardo.github.io/TypeTopology/Taboos.LPO.html) at
  TypeTopology
- [limited principle of omniscience](https://ncatlab.org/nlab/show/limited+principle+of+omniscience)
  at $n$Lab
