# Retractions in categories

```agda
module category-theory.retractions-in-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.retractions-in-precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

Consider a morphism `f : A → B` in a [category](category-theory.categories.md) `𝒞`. A {{#concept "retraction" Disambiguation="morphism in a category" Agda=retraction-hom-Category}} of `f` consists of a morphism `g : B → A` equipped with an [identification](foundation-core.identifications.md)

```text
  g ∘ f ＝ id.
```

## Definitions

### The predicate on morphisms in a category of being a retraction

```agda
module _
  {l1 l2 : Level} (𝒞 : Category l1 l2)
  {A B : obj-Category 𝒞} (f : hom-Category 𝒞 A B)
  where

  is-retraction-hom-Category : hom-Category 𝒞 B A → UU l2
  is-retraction-hom-Category =
    is-retraction-hom-Precategory (precategory-Category 𝒞) f
```

### Retractions of a morphism in a category

```agda
module _
  {l1 l2 : Level} (𝒞 : Category l1 l2)
  {A B : obj-Category 𝒞} (f : hom-Category 𝒞 A B)
  where

  retraction-hom-Category : UU l2
  retraction-hom-Category =
    retraction-hom-Precategory (precategory-Category 𝒞) f

  module _
    (r : retraction-hom-Category)
    where

    hom-retraction-hom-Category : hom-Category 𝒞 B A
    hom-retraction-hom-Category =
      hom-retraction-hom-Precategory (precategory-Category 𝒞) f r

    is-retraction-retraction-hom-Category :
      is-retraction-hom-Category 𝒞 f hom-retraction-hom-Category
    is-retraction-retraction-hom-Category =
      is-retraction-retraction-hom-Precategory (precategory-Category 𝒞) f r
```
