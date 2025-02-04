# Postcomposition of morphisms in noncoherent ω-semiprecategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.postcomposition-morphisms-noncoherent-omega-semiprecategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import globular-types.binary-globular-maps
open import globular-types.composition-structure-globular-types
open import globular-types.globular-types
open import globular-types.points-globular-types

open import wild-category-theory.maps-noncoherent-omega-semiprecategories
open import wild-category-theory.noncoherent-omega-semiprecategories
```

</details>

## Idea

Given a morphism `f : 𝒞₁ x y` in a
[noncoherent ω-semiprecategory](wild-category-theory.noncoherent-omega-semiprecategories.md)
with the structure of a [point](globular-types.points-globular-types.md), then
we have a
{{#concept "postcomposition map" Disambiguation="noncoherent ω-semiprecategory"}}
on hom-ω-semicategories

```text
  - ∘ f : 𝒞₁ z x → 𝒞₁ z y
```

for every object `z`.

## Definitions

### The precomposition globular map

```agda
module _
  {l1 l2 : Level} (𝒞 : Noncoherent-ω-Semiprecategory l1 l2)
  {x y : obj-Noncoherent-ω-Semiprecategory 𝒞}
  (f :
    point-Globular-Type (hom-globular-type-Noncoherent-ω-Semiprecategory 𝒞 x y))
  where

  postcomp-globular-map-hom-Noncoherent-ω-Semiprecategory :
    (z : obj-Noncoherent-ω-Semiprecategory 𝒞) →
    map-Noncoherent-ω-Semiprecategory
      ( hom-noncoherent-ω-semiprecategory-Noncoherent-ω-Semiprecategory 𝒞 z x)
      ( hom-noncoherent-ω-semiprecategory-Noncoherent-ω-Semiprecategory 𝒞 z y)
  postcomp-globular-map-hom-Noncoherent-ω-Semiprecategory z =
    ev-left-binary-globular-map
      ( comp-binary-globular-map-hom-Noncoherent-ω-Semiprecategory 𝒞)
      ( f)
```
