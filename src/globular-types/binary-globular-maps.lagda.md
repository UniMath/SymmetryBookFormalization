# Binary globular maps

```agda
{-# OPTIONS --guardedness #-}

module globular-types.binary-globular-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import globular-types.globular-maps
open import globular-types.globular-types
open import globular-types.points-globular-types
```

</details>

## Idea

Consider three [globular types](globular-types.globular-types.md) `G`, `H`, and
`K`. A {{#concept "binary globular map" Agda=binary-globular-map}}
`f : G → H → K` consists of a binary map

```text
  f₀ : G₀ → H₀ → K₀
```

and for every `x x' : G₀`, `y y' : H₀` a binary globular map

```text
  f' : G' x x' → H' y y' → K (f x y) (f x' y')
```

on the `1`-cells of `G` and `H`.

## Definitions

### Binary globular maps

```agda
record
  binary-globular-map
    {l1 l2 l3 l4 l5 l6 : Level}
    (G : Globular-Type l1 l2) (H : Globular-Type l3 l4)
    (K : Globular-Type l5 l6) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  where
  coinductive
  field
    0-cell-binary-globular-map :
      0-cell-Globular-Type G → 0-cell-Globular-Type H →
      0-cell-Globular-Type K

    1-cell-binary-globular-map-binary-globular-map :
      {x x' : 0-cell-Globular-Type G}
      {y y' : 0-cell-Globular-Type H} →
      binary-globular-map
        ( 1-cell-globular-type-Globular-Type G x x')
        ( 1-cell-globular-type-Globular-Type H y y')
        ( 1-cell-globular-type-Globular-Type K
          ( 0-cell-binary-globular-map x y)
          ( 0-cell-binary-globular-map x' y'))

open binary-globular-map public
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {G : Globular-Type l1 l2} {H : Globular-Type l3 l4} {K : Globular-Type l5 l6}
  (F : binary-globular-map G H K)
  where

  1-cell-binary-globular-map :
    {x x' : 0-cell-Globular-Type G} {y y' : 0-cell-Globular-Type H} →
    1-cell-Globular-Type G x x' →
    1-cell-Globular-Type H y y' →
    1-cell-Globular-Type K
      ( 0-cell-binary-globular-map F x y)
      ( 0-cell-binary-globular-map F x' y')
  1-cell-binary-globular-map =
    0-cell-binary-globular-map
      ( 1-cell-binary-globular-map-binary-globular-map F)

  2-cell-binary-globular-map :
    {x x' : 0-cell-Globular-Type G}
    {y y' : 0-cell-Globular-Type H}
    {f f' : 1-cell-Globular-Type G x x'}
    {g g' : 1-cell-Globular-Type H y y'} →
    2-cell-Globular-Type G f f' →
    2-cell-Globular-Type H g g' →
    2-cell-Globular-Type K
      ( 1-cell-binary-globular-map f g)
      ( 1-cell-binary-globular-map f' g')
  2-cell-binary-globular-map =
    0-cell-binary-globular-map
      ( 1-cell-binary-globular-map-binary-globular-map
        ( 1-cell-binary-globular-map-binary-globular-map F))
```

### Evaluating one of the arguments of a binary globular map

```agda
ev-left-binary-globular-map :
  {l1 l2 l3 l4 l5 l6 : Level}
  {G : Globular-Type l1 l2} {H : Globular-Type l3 l4} {K : Globular-Type l5 l6}
  (F : binary-globular-map G H K) (x : point-Globular-Type G) → globular-map H K
0-cell-globular-map (ev-left-binary-globular-map F x) =
  0-cell-binary-globular-map F (0-cell-point-Globular-Type x)
1-cell-globular-map-globular-map (ev-left-binary-globular-map F x) =
  ev-left-binary-globular-map
    ( 1-cell-binary-globular-map-binary-globular-map F)
    ( 1-cell-point-point-Globular-Type x)

ev-right-binary-globular-map :
  {l1 l2 l3 l4 l5 l6 : Level}
  {G : Globular-Type l1 l2} {H : Globular-Type l3 l4} {K : Globular-Type l5 l6}
  (F : binary-globular-map G H K) (x : point-Globular-Type H) → globular-map G K
0-cell-globular-map (ev-right-binary-globular-map F x) y =
  0-cell-binary-globular-map F y (0-cell-point-Globular-Type x)
1-cell-globular-map-globular-map (ev-right-binary-globular-map F x) =
  ev-right-binary-globular-map
    ( 1-cell-binary-globular-map-binary-globular-map F)
    ( 1-cell-point-point-Globular-Type x)
```
