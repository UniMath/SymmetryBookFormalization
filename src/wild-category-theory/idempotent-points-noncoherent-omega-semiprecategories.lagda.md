# Idempotent points in noncoherent ω-semiprecategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.idempotent-points-noncoherent-omega-semiprecategories where
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
open import globular-types.globular-types
open import globular-types.points-globular-types

open import wild-category-theory.maps-noncoherent-omega-semiprecategories
open import wild-category-theory.noncoherent-omega-semiprecategories
open import wild-category-theory.postcomposition-morphisms-noncoherent-omega-semiprecategories
open import wild-category-theory.precomposition-morphisms-noncoherent-omega-semiprecategories
```

</details>

## Idea

We say a [point](globular-types.points-globular-types.md) `x` in a
[noncoherent ω-semiprecategory](wild-category-theory.noncoherent-omega-semiprecategories.md)
`𝒞` is
{{#concept "idempotent" Disambiguation="point in a noncoherent ω-semiprecategory" Agda=is-idempotent-obj-Noncoherent-ω-Semiprecategory}}
if the equipped endomorphism `f : 𝒞₁ x x` satisfies the law `f ∘ f = f`, and is
again idempotent as a point of the hom-ω-semiprecategory.

## Definitions

### Idempotent points

```agda
record
  is-idempotent-point-Noncoherent-ω-Semiprecategory
    {l1 l2 : Level} (𝒞 : Noncoherent-ω-Semiprecategory l1 l2)
    (x : point-Globular-Type (globular-type-Noncoherent-ω-Semiprecategory 𝒞)) :
    UU l2
  where
  coinductive
  field
    is-idempotent-endo-Noncoherent-ω-Semiprecategory :
      comp-hom-Noncoherent-ω-Semiprecategory 𝒞
        ( 1-cell-point-Globular-Type
          ( globular-type-Noncoherent-ω-Semiprecategory 𝒞)
          ( x))
        ( 1-cell-point-Globular-Type
          ( globular-type-Noncoherent-ω-Semiprecategory 𝒞)
          ( x)) ＝
      1-cell-point-Globular-Type
        ( globular-type-Noncoherent-ω-Semiprecategory 𝒞)
        ( x)

    is-idempotent-hom-point-point-Noncoherent-ω-Semiprecategory :
      is-idempotent-point-Noncoherent-ω-Semiprecategory
        ( hom-noncoherent-ω-semiprecategory-Noncoherent-ω-Semiprecategory 𝒞
          ( 0-cell-point-Globular-Type x)
          ( 0-cell-point-Globular-Type x))
        ( 1-cell-point-point-Globular-Type x)
```
