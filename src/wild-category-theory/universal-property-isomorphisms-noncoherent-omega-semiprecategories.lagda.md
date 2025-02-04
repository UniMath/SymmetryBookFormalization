# The universal property of isomorphisms in noncoherent ω-semiprecategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.universal-property-isomorphisms-noncoherent-omega-semiprecategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import globular-types.binary-globular-maps
open import globular-types.composition-structure-globular-types
open import globular-types.globular-equivalences
open import globular-types.globular-types
open import globular-types.points-globular-types

open import wild-category-theory.maps-noncoherent-omega-semiprecategories
open import wild-category-theory.noncoherent-omega-semiprecategories
open import wild-category-theory.postcomposition-morphisms-noncoherent-omega-semiprecategories
open import wild-category-theory.precomposition-morphisms-noncoherent-omega-semiprecategories
```

</details>

## Idea

Given a morphism `f : 𝒞₁ x y` in a
[noncoherent ω-semiprecategory](wild-category-theory.noncoherent-omega-semiprecategories.md)
with the structure of a [point](globular-types.points-globular-types.md), then
`f` satisfies the
{{#concept "universal property of isomorphisms" Disambiguation="in a noncoherent ω-semiprecategory"}}
if
[precomposition](wild-category-theory.precomposition-morphisms-noncoherent-omega-semiprecategories.md)
and
[postcomposition](wild-category-theory.postcomposition-morphisms-noncoherent-omega-semiprecategories.md)
by `f` is a [globular equivalence](globular-types.globular-equivalences.md) for
every object `z`.

## Definitions

### The universal property of isomorphisms

```agda
module _
  {l1 l2 : Level} {𝒞 : Noncoherent-ω-Semiprecategory l1 l2}
  {x y : obj-Noncoherent-ω-Semiprecategory 𝒞}
  (f :
    point-Globular-Type (hom-globular-type-Noncoherent-ω-Semiprecategory 𝒞 x y))
  where

  universal-property-iso-Noncoherent-ω-Semiprecategory : UU (l1 ⊔ l2)
  universal-property-iso-Noncoherent-ω-Semiprecategory =
    ( (z : obj-Noncoherent-ω-Semiprecategory 𝒞) →
      is-equiv-globular-map
        ( precomp-globular-map-hom-Noncoherent-ω-Semiprecategory 𝒞 f z)) ×
    ( (z : obj-Noncoherent-ω-Semiprecategory 𝒞) →
      is-equiv-globular-map
        ( postcomp-globular-map-hom-Noncoherent-ω-Semiprecategory 𝒞 f z))
```
