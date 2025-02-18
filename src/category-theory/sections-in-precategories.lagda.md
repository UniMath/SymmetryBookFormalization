# Sections in precategories

```agda
module category-theory.sections-in-precategories where
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

Consider a morphism `f : A → B` in a [precategory](category-theory.precategories.md) `𝒞`. A {{#concept "section" Disambiguation="morphism in a precategory" Agda=section-hom-Precategory}} of `f` consists of a morphism `g : B → A` equipped with an [identification](foundation-core.identifications.md)

```text
  f ∘ g ＝ id.
```

## Definitions

### The predicate on morphisms in a precategory of being a section

```agda
module _
  {l1 l2 : Level} (𝒞 : Precategory l1 l2)
  {A B : obj-Precategory 𝒞} (f : hom-Precategory 𝒞 A B)
  where

  is-section-hom-Precategory : hom-Precategory 𝒞 B A → UU l2
  is-section-hom-Precategory g =
    comp-hom-Precategory 𝒞 f g ＝ id-hom-Precategory 𝒞
```

### Sections of a morphism in a precategory

```agda
module _
  {l1 l2 : Level} (𝒞 : Precategory l1 l2)
  {A B : obj-Precategory 𝒞} (f : hom-Precategory 𝒞 A B)
  where

  section-hom-Precategory : UU l2
  section-hom-Precategory =
    Σ (hom-Precategory 𝒞 B A) (is-section-hom-Precategory 𝒞 f)

  module _
    (s : section-hom-Precategory)
    where

    hom-section-hom-Precategory : hom-Precategory 𝒞 B A
    hom-section-hom-Precategory = pr1 s

    is-section-section-hom-Precategory :
      is-section-hom-Precategory 𝒞 f hom-section-hom-Precategory
    is-section-section-hom-Precategory = pr2 s
```
