# Neutral points in noncoherent ω-semiprecategories

```agda
{-# OPTIONS --guardedness --allow-unsolved-metas #-}

module wild-category-theory.neutral-morphisms-noncoherent-omega-semiprecategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import globular-types.binary-globular-maps
open import globular-types.composition-structure-globular-types
open import globular-types.globular-equivalences
open import globular-types.globular-maps
open import globular-types.globular-types
open import globular-types.homotopies-globular-maps
open import globular-types.points-globular-types

open import wild-category-theory.maps-noncoherent-omega-semiprecategories
open import wild-category-theory.noncoherent-omega-semiprecategories
open import wild-category-theory.postcomposition-morphisms-noncoherent-omega-semiprecategories
open import wild-category-theory.precomposition-morphisms-noncoherent-omega-semiprecategories
```

</details>

## Idea

We say a point `x` in a
[noncoherent ω-semiprecategory](wild-category-theory.noncoherent-omega-semiprecategories.md)
`𝒞` is
{{#concept "neutral" Disambiguation="point in a noncoherent ω-semiprecategory" Agda=is-neutral-point-Noncoherent-ω-Semiprecategory}}
if the precomposition and postcomposition globular maps at the distinguished
endomorphism `f : 𝒞₁ x x` are homotopic to identity maps.

## Definitions

### Right neutral points

```agda
is-right-neutral-point-Noncoherent-ω-Semiprecategory :
    {l1 l2 : Level} (𝒞 : Noncoherent-ω-Semiprecategory l1 l2)
    (x : point-Globular-Type (globular-type-Noncoherent-ω-Semiprecategory 𝒞)) →
    UU (l1 ⊔ l2)
is-right-neutral-point-Noncoherent-ω-Semiprecategory 𝒞 x =
  (z : obj-Noncoherent-ω-Semiprecategory 𝒞) →
  htpy-globular-map
    ( precomp-globular-map-hom-Noncoherent-ω-Semiprecategory 𝒞
        ( 1-cell-point-point-Globular-Type x)
        ( z))
    ( id-globular-map
      ( hom-globular-type-Noncoherent-ω-Semiprecategory 𝒞
        ( 0-cell-point-Globular-Type x)
        ( z)))
```

### Left neutral points

```agda
is-left-neutral-point-Noncoherent-ω-Semiprecategory :
    {l1 l2 : Level} (𝒞 : Noncoherent-ω-Semiprecategory l1 l2)
    (x : point-Globular-Type (globular-type-Noncoherent-ω-Semiprecategory 𝒞)) →
    UU (l1 ⊔ l2)
is-left-neutral-point-Noncoherent-ω-Semiprecategory 𝒞 x =
  (z : obj-Noncoherent-ω-Semiprecategory 𝒞) →
  htpy-globular-map
    ( postcomp-globular-map-hom-Noncoherent-ω-Semiprecategory 𝒞
        ( 1-cell-point-point-Globular-Type x)
        ( z))
    ( id-globular-map
      ( hom-globular-type-Noncoherent-ω-Semiprecategory 𝒞
        ( z)
        ( 0-cell-point-Globular-Type x)))
```

### Right neutral points

```agda
is-neutral-point-Noncoherent-ω-Semiprecategory :
    {l1 l2 : Level} (𝒞 : Noncoherent-ω-Semiprecategory l1 l2)
    (x : point-Globular-Type (globular-type-Noncoherent-ω-Semiprecategory 𝒞)) →
    UU (l1 ⊔ l2)
is-neutral-point-Noncoherent-ω-Semiprecategory 𝒞 x =
  ( is-right-neutral-point-Noncoherent-ω-Semiprecategory 𝒞 x) ×
  ( is-left-neutral-point-Noncoherent-ω-Semiprecategory 𝒞 x)
```
