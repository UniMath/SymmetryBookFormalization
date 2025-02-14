# The law of excluded middle

```agda
module foundation.law-of-excluded-middle where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels

open import univalent-combinatorics.2-element-types
```

</details>

## Idea

The
{{#concept "law of excluded middle" WD="principle of excluded middle" WDID=Q468422 Agda=LEM}}
asserts that any [proposition](foundation-core.propositions.md) `P` is
[decidable](foundation.decidable-types.md).

## Definition

```agda
level-LEM : (l : Level) → UU (lsuc l)
level-LEM l = (P : Prop l) → is-decidable (type-Prop P)

level-prop-LEM : (l : Level) → Prop (lsuc l)
level-prop-LEM l = Π-Prop (Prop l) (is-decidable-Prop)

LEM : UUω
LEM = {l : Level} → level-LEM l
```

## Properties

### Given LEM, we obtain a map from the type of propositions to the type of decidable propositions

```agda
decidable-prop-Prop :
  {l : Level} → level-LEM l → Prop l → Decidable-Prop l
pr1 (decidable-prop-Prop lem P) = type-Prop P
pr1 (pr2 (decidable-prop-Prop lem P)) = is-prop-type-Prop P
pr2 (pr2 (decidable-prop-Prop lem P)) = lem P
```

### The unrestricted law of excluded middle does not hold

```agda
abstract
  no-global-decidability :
    {l : Level} → ¬ ((X : UU l) → is-decidable X)
  no-global-decidability {l} d =
    is-not-decidable-type-2-Element-Type (λ X → d (pr1 X))
```

## Table of choice principles

{{#include tables/choice-principles.md}}

## External links

- [Excluded middle](https://ncatlab.org/nlab/show/excluded+middle) at nLab
