# Retractions in precategories

```agda
module category-theory.retractions-in-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

Consider a morphism `f : A → B` in a [precategory](category-theory.precategories.md) `𝒞`. A {{#concept "retraction" Disambiguation="morphism in a precategory" Agda=retraction-hom-Precategory}} of `f` consists of a morphism `g : B → A` equipped with an [identification](foundation-core.identifications.md)

```text
  g ∘ f ＝ id.
```

## Definitions

### The predicate on morphisms in a precategory of being a retraction

```agda
module _
  {l1 l2 : Level} (𝒞 : Precategory l1 l2)
  {A B : obj-Precategory 𝒞} (f : hom-Precategory 𝒞 A B)
  where

  is-retraction-hom-Precategory : hom-Precategory 𝒞 B A → UU l2
  is-retraction-hom-Precategory g =
    comp-hom-Precategory 𝒞 g f ＝ id-hom-Precategory 𝒞
```

### Retractions of a morphism in a precategory

```agda
module _
  {l1 l2 : Level} (𝒞 : Precategory l1 l2)
  {A B : obj-Precategory 𝒞} (f : hom-Precategory 𝒞 A B)
  where

  retraction-hom-Precategory : UU l2
  retraction-hom-Precategory =
    Σ (hom-Precategory 𝒞 B A) (is-retraction-hom-Precategory 𝒞 f)

  module _
    (r : retraction-hom-Precategory)
    where

    hom-retraction-hom-Precategory : hom-Precategory 𝒞 B A
    hom-retraction-hom-Precategory = pr1 r

    is-retraction-retraction-hom-Precategory :
      is-retraction-hom-Precategory 𝒞 f hom-retraction-hom-Precategory
    is-retraction-retraction-hom-Precategory = pr2 r
```
