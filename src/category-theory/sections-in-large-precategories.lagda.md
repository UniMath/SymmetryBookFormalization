# Sections in large precategories

```agda
module category-theory.sections-in-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.large-precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

Consider a morphism `f : A → B` in a [large precategory](category-theory.large-precategories.md) `𝒞`. A {{#concept "section" Disambiguation="morphism in a large precategory" Agda=section-hom-Large-Precategory}} of `f` consists of a morphism `g : B → A` equipped with an [identification](foundation-core.identifications.md)

```text
  f ∘ g ＝ id.
```

## Definitions

### The predicate on morphisms in a large precategory of being a section

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (𝒞 : Large-Precategory α β)
  {l1 l2 : Level} {A : obj-Large-Precategory 𝒞 l1}
  {B : obj-Large-Precategory 𝒞 l2} (f : hom-Large-Precategory 𝒞 A B)
  where

  is-section-hom-Large-Precategory :
    hom-Large-Precategory 𝒞 B A → UU (β l2 l2)
  is-section-hom-Large-Precategory g =
    comp-hom-Large-Precategory 𝒞 f g ＝ id-hom-Large-Precategory 𝒞
```

### Sections of a morphism in a large precategory

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (𝒞 : Large-Precategory α β)
  {l1 l2 : Level} {A : obj-Large-Precategory 𝒞 l1}
  {B : obj-Large-Precategory 𝒞 l2} (f : hom-Large-Precategory 𝒞 A B)
  where

  section-hom-Large-Precategory : UU (β l2 l1 ⊔ β l2 l2)
  section-hom-Large-Precategory =
    Σ (hom-Large-Precategory 𝒞 B A) (is-section-hom-Large-Precategory 𝒞 f)

  module _
    (r : section-hom-Large-Precategory)
    where

    hom-section-hom-Large-Precategory : hom-Large-Precategory 𝒞 B A
    hom-section-hom-Large-Precategory = pr1 r

    is-section-section-hom-Large-Precategory :
      is-section-hom-Large-Precategory 𝒞 f
        ( hom-section-hom-Large-Precategory)
    is-section-section-hom-Large-Precategory = pr2 r
```

