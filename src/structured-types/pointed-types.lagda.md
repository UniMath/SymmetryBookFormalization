# Pointed types

```agda
module structured-types.pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "pointed type" WD="pointed space" WDID=Q1419329 Agda=Pointed-Type}}
is a type `A` [equipped](foundation.structure.md) with an element `a : A`.

## Definition

### The universe of pointed types

```agda
Pointed-Type : (l : Level) → UU (lsuc l)
Pointed-Type l = Σ (UU l) (λ X → X)

module _
  {l : Level} (A : Pointed-Type l)
  where

  type-Pointed-Type : UU l
  type-Pointed-Type = pr1 A

  point-Pointed-Type : type-Pointed-Type
  point-Pointed-Type = pr2 A

  point-point-Pointed-Type : unit → type-Pointed-Type
  point-point-Pointed-Type = point point-Pointed-Type
```

### Evaluation at the base point

```agda
ev-point-Pointed-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) {B : UU l2} →
  (type-Pointed-Type A → B) → B
ev-point-Pointed-Type A f = f (point-Pointed-Type A)
```

## See also

- The notion of _nonempty types_ is treated in
  [`foundation.empty-types`](foundation.empty-types.md).
- The notion of _inhabited types_ is treated in
  [`foundation.inhabited-types`](foundation.inhabited-types.md).
