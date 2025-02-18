# Sections in categories

```agda
module category-theory.sections-in-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories
open import category-theory.sections-in-precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

Consider a morphism `f : A → B` in a [category](category-theory.categories.md) `𝒞`. A {{#concept "section" Disambiguation="morphism in a category" Agda=section-hom-Category}} of `f` consists of a morphism `g : B → A` equipped with an [identification](foundation-core.identifications.md)

```text
  f ∘ g ＝ id.
```

## Definitions

### The predicate on morphisms in a category of being a section

```agda
module _
  {l1 l2 : Level} (𝒞 : Category l1 l2)
  {A B : obj-Category 𝒞} (f : hom-Category 𝒞 A B)
  where

  is-section-hom-Category : hom-Category 𝒞 B A → UU l2
  is-section-hom-Category =
    is-section-hom-Precategory (precategory-Category 𝒞) f
```

### Sections of a morphism in a category

```agda
module _
  {l1 l2 : Level} (𝒞 : Category l1 l2)
  {A B : obj-Category 𝒞} (f : hom-Category 𝒞 A B)
  where

  section-hom-Category : UU l2
  section-hom-Category =
    section-hom-Precategory (precategory-Category 𝒞) f

  module _
    (r : section-hom-Category)
    where

    hom-section-hom-Category : hom-Category 𝒞 B A
    hom-section-hom-Category =
      hom-section-hom-Precategory (precategory-Category 𝒞) f r

    is-section-section-hom-Category :
      is-section-hom-Category 𝒞 f hom-section-hom-Category
    is-section-section-hom-Category =
      is-section-section-hom-Precategory (precategory-Category 𝒞) f r
```
