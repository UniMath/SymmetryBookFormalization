# The weak law of excluded middle

```agda
module foundation.weak-law-of-excluded-middle where
```

<details><summary>Imports</summary>

```agda
open import foundation.law-of-excluded-middle
open import foundation.propositions
open import foundation.universe-levels

open import logic.de-morgan-types
```

</details>

## Idea

The {{#concept "weak law of excluded middle" Agda=WLEM}} asserts that any
[proposition](foundation-core.propositions.md) `P` is
[De Morgan](logic.de-morgan-propositions.md).

## Definition

```agda
level-WLEM : (l : Level) → UU (lsuc l)
level-WLEM l = (P : Prop l) → is-de-morgan (type-Prop P)

level-prop-WLEM : (l : Level) → Prop (lsuc l)
level-prop-WLEM l = Π-Prop (Prop l) (λ P → is-de-morgan-Prop (type-Prop P))

WLEM : UUω
WLEM = {l : Level} → level-WLEM l
```

### The law of excluded middle implies the weak law of excluded middle

```agda
level-WLEM-LEM : {l : Level} → level-LEM l → level-WLEM l
level-WLEM-LEM lem P = is-de-morgan-is-decidable (lem P)

WLEM-LEM : LEM → WLEM
WLEM-LEM lem = level-WLEM-LEM lem
```

## Table of choice principles

{{#include tables/choice-principles.md}}

## External links

- [Weak excluded middle](https://ncatlab.org/nlab/show/weak+excluded+middle) at
  nLab
