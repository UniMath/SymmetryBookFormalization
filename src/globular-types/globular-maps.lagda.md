# Maps between globular types

```agda
{-# OPTIONS --guardedness #-}

module globular-types.globular-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import globular-types.globular-types
```

</details>

## Idea

A {{#concept "map" Disambiguation="globular types" Agda=globular-map}} `f`
between [globular types](globular-types.globular-types.md) `A` and `B` is a map
`F₀` of $0$-cells, and for every pair of $n$-cells `x` and `y`, a map of
$(n+1)$-cells

```text
  F_{𝑛+1} : (𝑛+1)-Cell A x y → (𝑛+1)-Cell B (F_𝑛 x) (F_𝑛 y).
```

## Definitions

### Maps between globular types

```agda
record
  globular-map
    {l1 l2 l3 l4 : Level} (A : Globular-Type l1 l2) (B : Globular-Type l3 l4) :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  coinductive
  field
    0-cell-globular-map :
      0-cell-Globular-Type A → 0-cell-Globular-Type B

    1-cell-globular-map-globular-map :
      {x y : 0-cell-Globular-Type A} →
      globular-map
        ( 1-cell-globular-type-Globular-Type A x y)
        ( 1-cell-globular-type-Globular-Type B
          ( 0-cell-globular-map x)
          ( 0-cell-globular-map y))

open globular-map public

module _
  {l1 l2 l3 l4 : Level}
  {A : Globular-Type l1 l2} {B : Globular-Type l3 l4}
  (F : globular-map A B)
  where

  1-cell-globular-map :
    {x y : 0-cell-Globular-Type A} →
    1-cell-Globular-Type A x y →
    1-cell-Globular-Type B
      ( 0-cell-globular-map F x)
      ( 0-cell-globular-map F y)
  1-cell-globular-map =
    0-cell-globular-map (1-cell-globular-map-globular-map F)

module _
  {l1 l2 l3 l4 : Level}
  {A : Globular-Type l1 l2} {B : Globular-Type l3 l4}
  (F : globular-map A B)
  where

  2-cell-globular-map-globular-map :
    {x y : 0-cell-Globular-Type A}
    (f g : 1-cell-Globular-Type A x y) →
    globular-map
      ( 2-cell-globular-type-Globular-Type A f g)
      ( 2-cell-globular-type-Globular-Type B
        ( 1-cell-globular-map F f)
        ( 1-cell-globular-map F g))
  2-cell-globular-map-globular-map f g =
    1-cell-globular-map-globular-map
      ( 1-cell-globular-map-globular-map F)

  2-cell-globular-map :
    {x y : 0-cell-Globular-Type A}
    {f g : 1-cell-Globular-Type A x y} →
    2-cell-Globular-Type A f g →
    2-cell-Globular-Type B
      ( 1-cell-globular-map F f)
      ( 1-cell-globular-map F g)
  2-cell-globular-map =
    1-cell-globular-map (1-cell-globular-map-globular-map F)

module _
  {l1 l2 l3 l4 : Level}
  {A : Globular-Type l1 l2} {B : Globular-Type l3 l4}
  (F : globular-map A B)
  where

  3-cell-globular-map-globular-map :
    {x y : 0-cell-Globular-Type A}
    {f g : 1-cell-Globular-Type A x y}
    (s t : 2-cell-Globular-Type A f g) →
    globular-map
      ( 3-cell-globular-type-Globular-Type A s t)
      ( 3-cell-globular-type-Globular-Type B
        ( 2-cell-globular-map F s)
        ( 2-cell-globular-map F t))
  3-cell-globular-map-globular-map =
    2-cell-globular-map-globular-map
      ( 1-cell-globular-map-globular-map F)

  3-cell-globular-map :
    {x y : 0-cell-Globular-Type A}
    {f g : 1-cell-Globular-Type A x y} →
    {H K : 2-cell-Globular-Type A f g} →
    3-cell-Globular-Type A H K →
    3-cell-Globular-Type B
      ( 2-cell-globular-map F H)
      ( 2-cell-globular-map F K)
  3-cell-globular-map =
    2-cell-globular-map (1-cell-globular-map-globular-map F)
```

### The identity map on a globular type

```agda
id-globular-map :
  {l1 l2 : Level} (A : Globular-Type l1 l2) → globular-map A A
0-cell-globular-map (id-globular-map A) = id
1-cell-globular-map-globular-map (id-globular-map A) =
  id-globular-map (1-cell-globular-type-Globular-Type A _ _)
```

### Composition of maps of globular types

```agda
comp-globular-map :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : Globular-Type l1 l2}
  {B : Globular-Type l3 l4}
  {C : Globular-Type l5 l6} →
  globular-map B C → globular-map A B → globular-map A C
comp-globular-map g f =
  λ where
  .0-cell-globular-map →
    0-cell-globular-map g ∘ 0-cell-globular-map f
  .1-cell-globular-map-globular-map →
    comp-globular-map
      ( 1-cell-globular-map-globular-map g)
      ( 1-cell-globular-map-globular-map f)
```

## See also

- The dependent counterpart to globular maps is
  [sections of dependent globular types](type-theories.sections-dependent-globular-types.md)
