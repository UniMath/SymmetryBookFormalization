# Sections in large categories

```agda
module category-theory.sections-in-large-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-categories
open import category-theory.sections-in-large-precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

Consider a morphism `f : A → B` in a [large category](category-theory.large-categories.md) `𝒞`. A {{#concept "section" Disambiguation="morphism in a large category" Agda=section-hom-Large-Category}} of `f` consists of a morphism `g : B → A` equipped with an [identification](foundation-core.identifications.md)

```text
  f ∘ g ＝ id.
```

## Definitions

### The predicate on morphisms in a large category of being a section

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (𝒞 : Large-Category α β)
  {l1 l2 : Level} {A : obj-Large-Category 𝒞 l1}
  {B : obj-Large-Category 𝒞 l2} (f : hom-Large-Category 𝒞 A B)
  where

  is-section-hom-Large-Category :
    hom-Large-Category 𝒞 B A → UU (β l2 l2)
  is-section-hom-Large-Category =
    is-section-hom-Large-Precategory (large-precategory-Large-Category 𝒞) f
```

### Sections of a morphism in a large category

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (𝒞 : Large-Category α β)
  {l1 l2 : Level} {A : obj-Large-Category 𝒞 l1}
  {B : obj-Large-Category 𝒞 l2} (f : hom-Large-Category 𝒞 A B)
  where

  section-hom-Large-Category : UU (β l2 l1 ⊔ β l2 l2)
  section-hom-Large-Category =
    section-hom-Large-Precategory (large-precategory-Large-Category 𝒞) f

  module _
    (r : section-hom-Large-Category)
    where

    hom-section-hom-Large-Category : hom-Large-Category 𝒞 B A
    hom-section-hom-Large-Category =
      hom-section-hom-Large-Precategory
        ( large-precategory-Large-Category 𝒞)
        ( f)
        ( r)

    is-section-section-hom-Large-Category :
      is-section-hom-Large-Category 𝒞 f
        ( hom-section-hom-Large-Category)
    is-section-section-hom-Large-Category =
      is-section-section-hom-Large-Precategory
        ( large-precategory-Large-Category 𝒞)
        ( f)
        ( r)
```

