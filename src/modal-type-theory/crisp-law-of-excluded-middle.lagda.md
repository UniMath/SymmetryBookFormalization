# The crisp law of excluded middle

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.crisp-law-of-excluded-middle where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.decidable-propositions
open import foundation-core.propositions
```

</details>

## Idea

The {{#concept "crisp law of excluded middle" Agda=Crisp-LEM}} asserts that any
[crisp](modal-type-theory.crisp-types.md)
[proposition](foundation-core.propositions.md) `P` is
[decidable](foundation.decidable-types.md).

## Definition

```agda
Crisp-LEM : (@♭ l : Level) → UU (lsuc l)
Crisp-LEM l = (@♭ P : Prop l) → is-decidable (type-Prop P)
```

## Properties

### Given crisp LEM, we obtain a map from crisp propositions to decidable propositions

```agda
decidable-prop-Crisp-Prop :
  {@♭ l : Level} → Crisp-LEM l → @♭ Prop l → Decidable-Prop l
pr1 (decidable-prop-Crisp-Prop lem P) = type-Prop P
pr1 (pr2 (decidable-prop-Crisp-Prop lem P)) = is-prop-type-Prop P
pr2 (pr2 (decidable-prop-Crisp-Prop lem P)) = lem P
```

## Table of choice principles

{{#include tables/choice-principles.md}}

## References

{{#bibliography}} {{#reference Shu18}}
