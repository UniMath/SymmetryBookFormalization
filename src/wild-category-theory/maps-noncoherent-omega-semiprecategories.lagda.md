# Maps between noncoherent ω-semiprecategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.maps-noncoherent-omega-semiprecategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import globular-types.globular-maps
open import globular-types.globular-types

open import wild-category-theory.noncoherent-omega-semiprecategories
```

</details>

## Idea

A
{{#concept "map" Disambiguation="between noncoherent ω-semiprecategories" Agda=map-Noncoherent-ω-Semiprecategory}}
`f` between
[noncoherent ω-semiprecategories](wild-category-theory.noncoherent-omega-semiprecategories.md)
`𝒜` and `ℬ` is a [globular map](globular-types.globular-maps.md) between their
underlying [globular types](globular-types.globular-types.md). More
specifically, a map `F` between noncoherent ω-semiprecategories consists of a
map on objects `F₀ : obj 𝒜 → obj ℬ`, and for every pair of $n$-morphisms `f` and
`g`, a map of $(n+1)$-morphisms

```text
  Fₙ₊₁ : (𝑛+1)-hom 𝒞 f g → (𝑛+1)-hom 𝒟 (Fₙ f) (Fₙ g).
```

A map between noncoherent ω-semiprecategories does not have to preserve the
identities or composition in any shape or form, and is the least structured
notion of a "morphism" between noncoherent ω-semiprecategories. For a notion of
"morphism" between noncoherent ω-semiprecategories that in one sense preserves
this additional structure, see
[colax functors between noncoherent ω-semiprecategories](wild-category-theory.colax-functors-noncoherent-omega-semiprecategories.md).

## Definitions

### Maps between noncoherent ω-semiprecategories

```agda
map-Noncoherent-ω-Semiprecategory :
  {l1 l2 l3 l4 : Level}
  (𝒜 : Noncoherent-ω-Semiprecategory l1 l2)
  (ℬ : Noncoherent-ω-Semiprecategory l3 l4) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
map-Noncoherent-ω-Semiprecategory 𝒜 ℬ =
  globular-map
    ( globular-type-Noncoherent-ω-Semiprecategory 𝒜)
    ( globular-type-Noncoherent-ω-Semiprecategory ℬ)

module _
  {l1 l2 l3 l4 : Level}
  (𝒜 : Noncoherent-ω-Semiprecategory l1 l2)
  (ℬ : Noncoherent-ω-Semiprecategory l3 l4)
  (F : map-Noncoherent-ω-Semiprecategory 𝒜 ℬ)
  where

  obj-map-Noncoherent-ω-Semiprecategory :
    obj-Noncoherent-ω-Semiprecategory 𝒜 →
    obj-Noncoherent-ω-Semiprecategory ℬ
  obj-map-Noncoherent-ω-Semiprecategory =
    0-cell-globular-map F

  hom-globular-map-map-Noncoherent-ω-Semiprecategory :
    {x y : obj-Noncoherent-ω-Semiprecategory 𝒜} →
    globular-map
      ( hom-globular-type-Noncoherent-ω-Semiprecategory 𝒜 x y)
      ( hom-globular-type-Noncoherent-ω-Semiprecategory ℬ
        ( obj-map-Noncoherent-ω-Semiprecategory x)
        ( obj-map-Noncoherent-ω-Semiprecategory y))
  hom-globular-map-map-Noncoherent-ω-Semiprecategory =
    1-cell-globular-map-globular-map F

  hom-map-Noncoherent-ω-Semiprecategory :
    {x y : obj-Noncoherent-ω-Semiprecategory 𝒜} →
    hom-Noncoherent-ω-Semiprecategory 𝒜 x y →
    hom-Noncoherent-ω-Semiprecategory ℬ
      ( obj-map-Noncoherent-ω-Semiprecategory x)
      ( obj-map-Noncoherent-ω-Semiprecategory y)
  hom-map-Noncoherent-ω-Semiprecategory =
    0-cell-globular-map
      ( hom-globular-map-map-Noncoherent-ω-Semiprecategory)

  2-hom-map-Noncoherent-ω-Semiprecategory :
    {x y : obj-Noncoherent-ω-Semiprecategory 𝒜}
    {f g : hom-Noncoherent-ω-Semiprecategory 𝒜 x y} →
    2-hom-Noncoherent-ω-Semiprecategory 𝒜 f g →
    2-hom-Noncoherent-ω-Semiprecategory ℬ
      ( hom-map-Noncoherent-ω-Semiprecategory f)
      ( hom-map-Noncoherent-ω-Semiprecategory g)
  2-hom-map-Noncoherent-ω-Semiprecategory =
    1-cell-globular-map
      ( hom-globular-map-map-Noncoherent-ω-Semiprecategory)

  hom-noncoherent-ω-semiprecategory-map-Noncoherent-ω-Semiprecategory :
    (x y : obj-Noncoherent-ω-Semiprecategory 𝒜) →
    map-Noncoherent-ω-Semiprecategory
      ( hom-noncoherent-ω-semiprecategory-Noncoherent-ω-Semiprecategory
        ( 𝒜)
        ( x)
        ( y))
      ( hom-noncoherent-ω-semiprecategory-Noncoherent-ω-Semiprecategory
        ( ℬ)
        ( obj-map-Noncoherent-ω-Semiprecategory x)
        ( obj-map-Noncoherent-ω-Semiprecategory y))
  hom-noncoherent-ω-semiprecategory-map-Noncoherent-ω-Semiprecategory
    x y =
    1-cell-globular-map-globular-map F
```

### The identity map on a noncoherent ω-semiprecategory

```agda
module _
  {l1 l2 : Level} (𝒜 : Noncoherent-ω-Semiprecategory l1 l2)
  where

  id-map-Noncoherent-ω-Semiprecategory :
    map-Noncoherent-ω-Semiprecategory 𝒜 𝒜
  id-map-Noncoherent-ω-Semiprecategory =
    id-globular-map _
```

### Composition of maps between noncoherent ω-semiprecategories

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (𝒜 : Noncoherent-ω-Semiprecategory l1 l2)
  (ℬ : Noncoherent-ω-Semiprecategory l3 l4)
  (𝒞 : Noncoherent-ω-Semiprecategory l5 l6)
  (G : map-Noncoherent-ω-Semiprecategory ℬ 𝒞)
  (F : map-Noncoherent-ω-Semiprecategory 𝒜 ℬ)
  where

  comp-map-Noncoherent-ω-Semiprecategory :
    map-Noncoherent-ω-Semiprecategory 𝒜 𝒞
  comp-map-Noncoherent-ω-Semiprecategory =
    comp-globular-map G F
```
