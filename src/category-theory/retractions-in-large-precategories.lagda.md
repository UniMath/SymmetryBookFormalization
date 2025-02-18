# Retractions in large precategories

```agda
module category-theory.retractions-in-large-precategories where
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

Consider a morphism `f : A → B` in a [large precategory](category-theory.large-precategories.md) `𝒞`. A {{#concept "retraction" Disambiguation="morphism in a large precategory" Agda=retraction-hom-Large-Precategory}} of `f` consists of a morphism `g : B → A` equipped with an [identification](foundation-core.identifications.md)

```text
  g ∘ f ＝ id.
```

## Definitions

### The predicate on morphisms in a large precategory of being a retraction

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (𝒞 : Large-Precategory α β)
  {l1 l2 : Level} {A : obj-Large-Precategory 𝒞 l1}
  {B : obj-Large-Precategory 𝒞 l2} (f : hom-Large-Precategory 𝒞 A B)
  where

  is-retraction-hom-Large-Precategory :
    hom-Large-Precategory 𝒞 B A → UU (β l1 l1)
  is-retraction-hom-Large-Precategory g =
    comp-hom-Large-Precategory 𝒞 g f ＝ id-hom-Large-Precategory 𝒞
```

### Retractions of a morphism in a large precategory

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (𝒞 : Large-Precategory α β)
  {l1 l2 : Level} {A : obj-Large-Precategory 𝒞 l1}
  {B : obj-Large-Precategory 𝒞 l2} (f : hom-Large-Precategory 𝒞 A B)
  where

  retraction-hom-Large-Precategory : UU (β l1 l1 ⊔ β l2 l1)
  retraction-hom-Large-Precategory =
    Σ (hom-Large-Precategory 𝒞 B A) (is-retraction-hom-Large-Precategory 𝒞 f)

  module _
    (r : retraction-hom-Large-Precategory)
    where

    hom-retraction-hom-Large-Precategory : hom-Large-Precategory 𝒞 B A
    hom-retraction-hom-Large-Precategory = pr1 r

    is-retraction-retraction-hom-Large-Precategory :
      is-retraction-hom-Large-Precategory 𝒞 f
        ( hom-retraction-hom-Large-Precategory)
    is-retraction-retraction-hom-Large-Precategory = pr2 r
```

