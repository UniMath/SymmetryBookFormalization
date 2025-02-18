# Retractions in large categories

```agda
module category-theory.retractions-in-large-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-categories
open import category-theory.retractions-in-large-precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

Consider a morphism `f : A → B` in a [large category](category-theory.large-categories.md) `𝒞`. A {{#concept "retraction" Disambiguation="morphism in a large category" Agda=retraction-hom-Large-Category}} of `f` consists of a morphism `g : B → A` equipped with an [identification](foundation-core.identifications.md)

```text
  g ∘ f ＝ id.
```

## Definitions

### The predicate on morphisms in a large category of being a retraction

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (𝒞 : Large-Category α β)
  {l1 l2 : Level} {A : obj-Large-Category 𝒞 l1}
  {B : obj-Large-Category 𝒞 l2} (f : hom-Large-Category 𝒞 A B)
  where

  is-retraction-hom-Large-Category :
    hom-Large-Category 𝒞 B A → UU (β l1 l1)
  is-retraction-hom-Large-Category =
    is-retraction-hom-Large-Precategory (large-precategory-Large-Category 𝒞) f
```

### Retractions of a morphism in a large category

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (𝒞 : Large-Category α β)
  {l1 l2 : Level} {A : obj-Large-Category 𝒞 l1}
  {B : obj-Large-Category 𝒞 l2} (f : hom-Large-Category 𝒞 A B)
  where

  retraction-hom-Large-Category : UU (β l1 l1 ⊔ β l2 l1)
  retraction-hom-Large-Category =
    retraction-hom-Large-Precategory (large-precategory-Large-Category 𝒞) f

  module _
    (r : retraction-hom-Large-Category)
    where

    hom-retraction-hom-Large-Category : hom-Large-Category 𝒞 B A
    hom-retraction-hom-Large-Category =
      hom-retraction-hom-Large-Precategory
        ( large-precategory-Large-Category 𝒞)
        ( f)
        ( r)

    is-retraction-retraction-hom-Large-Category :
      is-retraction-hom-Large-Category 𝒞 f
        ( hom-retraction-hom-Large-Category)
    is-retraction-retraction-hom-Large-Category =
      is-retraction-retraction-hom-Large-Precategory
        ( large-precategory-Large-Category 𝒞)
        ( f)
        ( r)
```

