# Composition structure on globular types

```agda
{-# OPTIONS --guardedness #-}

module globular-types.composition-structure-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import globular-types.binary-globular-maps
open import globular-types.globular-types
open import globular-types.transitive-globular-types
```

</details>

## Idea

A
{{#concept "composition structure" Disambiguation="globular type" Agda=composition-Globular-Type}}
on a [globular type](globular-types.globular-types.md) `G` consists of a
[binary globular map](globular-types.binary-globular-maps.md)

```text
  - ∘ - : G' y z → G' x y → G' x z,
```

and for any two `0`-cells `x y : G₀` a composition structure on the globular
type `G' x y` of `1`-cells of `G`. More explicitly, a composition structure
consists of binary operations

```text
  - ∘ - : (𝑛+1)-Cell G y z → (𝑛+1)-Cell G x y → (𝑛+1)-Cell G x z,
```

each of which preserve all higher cells of the globular type `G`. In comparison
to [transitivity structure](globular-types.transitive-globular-types.md) on
globular types, this also gives horizontal composition of higher cells.

## Definitions

### Globular composition structure

```agda
record
  composition-Globular-Type
    {l1 l2 : Level} (G : Globular-Type l1 l2) : UU (l1 ⊔ l2)
  where
  coinductive

  field
    comp-binary-globular-map-composition-Globular-Type :
      {x y z : 0-cell-Globular-Type G} →
      binary-globular-map
        ( 1-cell-globular-type-Globular-Type G y z)
        ( 1-cell-globular-type-Globular-Type G x y)
        ( 1-cell-globular-type-Globular-Type G x z)

  field
    composition-1-cell-globular-type-Globular-Type :
      {x y : 0-cell-Globular-Type G} →
      composition-Globular-Type
        ( 1-cell-globular-type-Globular-Type G x y)

  comp-1-cell-composition-Globular-Type :
    {x y z : 0-cell-Globular-Type G} →
    1-cell-Globular-Type G y z →
    1-cell-Globular-Type G x y →
    1-cell-Globular-Type G x z
  comp-1-cell-composition-Globular-Type =
    0-cell-binary-globular-map
      comp-binary-globular-map-composition-Globular-Type

  horizontal-comp-2-cell-composition-Globular-Type :
    {x y z : 0-cell-Globular-Type G} →
    {g g' : 1-cell-Globular-Type G y z} →
    {f f' : 1-cell-Globular-Type G x y} →
    2-cell-Globular-Type G g g' →
    2-cell-Globular-Type G f f' →
    2-cell-Globular-Type G
      ( comp-1-cell-composition-Globular-Type g f)
      ( comp-1-cell-composition-Globular-Type g' f')
  horizontal-comp-2-cell-composition-Globular-Type =
    1-cell-binary-globular-map
      ( comp-binary-globular-map-composition-Globular-Type)

  horizontal-comp-3-cell-composition-Globular-Type' :
    {x y z : 0-cell-Globular-Type G}
    {g g' : 1-cell-Globular-Type G y z}
    {f f' : 1-cell-Globular-Type G x y}
    {α α' : 2-cell-Globular-Type G g g'}
    {β β' : 2-cell-Globular-Type G f f'} →
    3-cell-Globular-Type G α α' →
    3-cell-Globular-Type G β β' →
    3-cell-Globular-Type G
      ( horizontal-comp-2-cell-composition-Globular-Type α β)
      ( horizontal-comp-2-cell-composition-Globular-Type α' β')
  horizontal-comp-3-cell-composition-Globular-Type' =
    2-cell-binary-globular-map
      comp-binary-globular-map-composition-Globular-Type

open composition-Globular-Type public
```

```agda
module _
  {l1 l2 : Level} {G : Globular-Type l1 l2} (H : composition-Globular-Type G)
  where

  comp-2-cell-composition-Globular-Type :
    {x y : 0-cell-Globular-Type G} →
    {f g h : 1-cell-Globular-Type G x y} →
    2-cell-Globular-Type G g h →
    2-cell-Globular-Type G f g →
    2-cell-Globular-Type G f h
  comp-2-cell-composition-Globular-Type =
    comp-1-cell-composition-Globular-Type
      ( composition-1-cell-globular-type-Globular-Type H)

  horizontal-comp-3-cell-composition-Globular-Type :
    {x y : 0-cell-Globular-Type G}
    {f g h : 1-cell-Globular-Type G x y}
    {α α' : 2-cell-Globular-Type G g h}
    {β β' : 2-cell-Globular-Type G f g} →
    3-cell-Globular-Type G α α' →
    3-cell-Globular-Type G β β' →
    3-cell-Globular-Type G
      ( comp-2-cell-composition-Globular-Type α β)
      ( comp-2-cell-composition-Globular-Type α' β')
  horizontal-comp-3-cell-composition-Globular-Type =
    horizontal-comp-2-cell-composition-Globular-Type
      ( composition-1-cell-globular-type-Globular-Type H)

module _
  {l1 l2 : Level} {G : Globular-Type l1 l2} (H : composition-Globular-Type G)
  where

  comp-3-cell-composition-Globular-Type :
    {x y : 0-cell-Globular-Type G} →
    {f g : 1-cell-Globular-Type G x y} →
    {α β γ : 2-cell-Globular-Type G f g} →
    3-cell-Globular-Type G β γ →
    3-cell-Globular-Type G α β →
    3-cell-Globular-Type G α γ
  comp-3-cell-composition-Globular-Type =
    comp-2-cell-composition-Globular-Type
      ( composition-1-cell-globular-type-Globular-Type H)
```

## Properties

### Globular types with composition structure are transitive

```agda
is-transitive-composition-Globular-Type :
  {l1 l2 : Level} {G : Globular-Type l1 l2} →
  composition-Globular-Type G →
  is-transitive-Globular-Type G
comp-1-cell-is-transitive-Globular-Type
  ( is-transitive-composition-Globular-Type H) =
  comp-1-cell-composition-Globular-Type H
is-transitive-1-cell-globular-type-is-transitive-Globular-Type
  ( is-transitive-composition-Globular-Type H) =
  is-transitive-composition-Globular-Type
    ( composition-1-cell-globular-type-Globular-Type H)
```

## See also

- [Noncoherent wild $\omega$-semiprecategories](wild-category-theory.noncoherent-wild-omega-semiprecategories.md)
