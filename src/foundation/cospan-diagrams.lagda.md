# Cospan diagrams

```agda
module foundation.cospan-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.cospans
open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "cospan diagram" Agda=cospan-diagram}} consists of two types `A`
and `B` and a [cospan](foundation.cospans.md) `A -f-> X <-g- B` between them.

## Definitions

```agda
cospan-diagram :
  (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
cospan-diagram l1 l2 l3 =
  Σ (UU l1) (λ A → Σ (UU l2) (cospan l3 A))

module _
  {l1 l2 l3 : Level} (c : cospan-diagram l1 l2 l3)
  where

  left-type-cospan-diagram : UU l1
  left-type-cospan-diagram = pr1 c

  right-type-cospan-diagram : UU l2
  right-type-cospan-diagram = pr1 (pr2 c)

  cospan-cospan-diagram :
    cospan l3 left-type-cospan-diagram right-type-cospan-diagram
  cospan-cospan-diagram = pr2 (pr2 c)
```
