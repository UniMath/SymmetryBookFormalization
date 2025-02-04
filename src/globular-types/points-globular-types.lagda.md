# Points of globular types

```agda
{-# OPTIONS --guardedness #-}

module globular-types.points-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.unit-type
open import foundation.universe-levels

open import globular-types.globular-maps
open import globular-types.globular-types
open import globular-types.unit-globular-type
```

</details>

## Idea

A {{#concept "point" Disambiguation="globular type" Agda=point-Globular-Type}}
of a [globular type](globular-types.globular-types.md) `G` consists of a 0-cell
`x₀ : G₀` and a point in the globular type `G' x₀ x₀` of 1-cells from `x₀` to
itself. Equivalently, a point is a
[globular map](globular-types.globular-maps.md) from the
[unit globular type](globular-types.unit-globular-type.md) `𝟏` to `G`.

## Definitions

### Points of globular types

```agda
record point-Globular-Type
  {l1 l2 : Level} (G : Globular-Type l1 l2) : UU (l1 ⊔ l2)
  where
  coinductive

  field
    0-cell-point-Globular-Type : 0-cell-Globular-Type G

  field
    1-cell-point-point-Globular-Type :
      point-Globular-Type
        ( 1-cell-globular-type-Globular-Type G
          ( 0-cell-point-Globular-Type)
          ( 0-cell-point-Globular-Type))

open point-Globular-Type public

1-cell-point-Globular-Type :
  {l1 l2 : Level} (G : Globular-Type l1 l2) (x : point-Globular-Type G) →
  1-cell-Globular-Type G
    ( 0-cell-point-Globular-Type x)
    ( 0-cell-point-Globular-Type x)
1-cell-point-Globular-Type G x =
  0-cell-point-Globular-Type (1-cell-point-point-Globular-Type x)
```

## Properties

### Evaluating globular maps at points

```agda
ev-point-globular-map :
  {l1 l2 l3 l4 : Level} {G : Globular-Type l1 l2} {H : Globular-Type l3 l4}
  (f : globular-map G H) → point-Globular-Type G → point-Globular-Type H
0-cell-point-Globular-Type (ev-point-globular-map f x) =
  0-cell-globular-map f (0-cell-point-Globular-Type x)
1-cell-point-point-Globular-Type (ev-point-globular-map f x) =
  ev-point-globular-map
    ( 1-cell-globular-map-globular-map f)
    ( 1-cell-point-point-Globular-Type x)
```

### Points are globular maps from the terminal globular type

#### The globular map associated to a point of a globular type

```agda
globular-map-point-Globular-Type :
  {l1 l2 : Level} (G : Globular-Type l1 l2) →
  point-Globular-Type G → globular-map unit-Globular-Type G
0-cell-globular-map (globular-map-point-Globular-Type G x) star =
  0-cell-point-Globular-Type x
1-cell-globular-map-globular-map (globular-map-point-Globular-Type G x) =
  globular-map-point-Globular-Type
    ( 1-cell-globular-type-Globular-Type G _ _)
    ( 1-cell-point-point-Globular-Type x)
```
