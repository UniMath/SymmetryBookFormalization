# Invertible Morphisms in precategories

```agda
module category-theory.invertible-morphisms-in-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories
open import category-theory.retractions-in-precategories
open import category-theory.sections-in-precategories

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A morphism `f : x → y` in a [precategory](category-theory.precategories.md) `C` is said to be
{{#concept "invertible" Disambiguation="morphism in a precategory" Agda=is-invertible-hom-Precategory}}
if there is a morphism `g : y → x` which is both a [section](category-theory.sections-in-precategories.md) of `f` and a [retraction](category-theory.retractions-in-precategories.md) of `f`. In other words, `f` is invertible if there is a morphism `g` equipped with [identifications](foundation-core.identity-types.md) `f ∘ g ＝ id` and `g ∘ f ＝ id`.

## Definitions

### The predicate of being an inverse of a morphism in a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  {x y : obj-Precategory C} {f : hom-Precategory C x y}
  where

  is-inverse-hom-Precategory : (g : hom-Precategory C y x) → UU l2
  is-inverse-hom-Precategory g =
    is-section-hom-Precategory C f g × is-retraction-hom-Precategory C f g
```

### The predicate of being an invertible morphism in a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  {x y : obj-Precategory C} (f : hom-Precategory C x y)
  where

  is-invertible-hom-Precategory : UU l2
  is-invertible-hom-Precategory =
    Σ ( hom-Precategory C y x)
      ( λ g →
        ( is-section-hom-Precategory C f g) ×
        ( is-retraction-hom-Precategory C f g))

module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  {x y : obj-Precategory C} {f : hom-Precategory C x y}
  (H : is-invertible-hom-Precategory C f)
  where

  hom-inv-is-invertible-hom-Precategory : hom-Precategory C y x
  hom-inv-is-invertible-hom-Precategory = pr1 H

  is-section-hom-inv-is-invertible-hom-Precategory :
    is-section-hom-Precategory C f hom-inv-is-invertible-hom-Precategory
  is-section-hom-inv-is-invertible-hom-Precategory = pr1 (pr2 H)

  section-is-invertible-hom-Precategory :
    section-hom-Precategory C f
  pr1 section-is-invertible-hom-Precategory =
    hom-inv-is-invertible-hom-Precategory
  pr2 section-is-invertible-hom-Precategory =
    is-section-hom-inv-is-invertible-hom-Precategory

  is-retraction-hom-inv-is-invertible-hom-Precategory :
    is-retraction-hom-Precategory C f hom-inv-is-invertible-hom-Precategory
  is-retraction-hom-inv-is-invertible-hom-Precategory = pr2 (pr2 H)

  retraction-is-invertible-hom-Precategory :
    retraction-hom-Precategory C f
  pr1 retraction-is-invertible-hom-Precategory =
    hom-inv-is-invertible-hom-Precategory
  pr2 retraction-is-invertible-hom-Precategory =
    is-retraction-hom-inv-is-invertible-hom-Precategory

  is-inverse-hom-inv-is-invertible-hom-Precategory :
    is-inverse-hom-Precategory C hom-inv-is-invertible-hom-Precategory
  pr1 is-inverse-hom-inv-is-invertible-hom-Precategory =
    is-section-hom-inv-is-invertible-hom-Precategory
  pr2 is-inverse-hom-inv-is-invertible-hom-Precategory =
    is-retraction-hom-inv-is-invertible-hom-Precategory
```

### Invertible morphisms in a precategory

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  (x y : obj-Precategory C)
  where

  invertible-hom-Precategory : UU l2
  invertible-hom-Precategory =
    Σ (hom-Precategory C x y) (is-invertible-hom-Precategory C)

module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  (f : invertible-hom-Precategory C x y)
  where

  hom-invertible-hom-Precategory : hom-Precategory C x y
  hom-invertible-hom-Precategory = pr1 f

  is-invertible-hom-iso-Precategory :
    is-invertible-hom-Precategory C hom-invertible-hom-Precategory
  is-invertible-hom-iso-Precategory = pr2 f

  hom-inv-invertible-hom-Precategory : hom-Precategory C y x
  hom-inv-invertible-hom-Precategory =
    hom-inv-is-invertible-hom-Precategory C
      ( is-invertible-hom-iso-Precategory)

  is-section-hom-inv-invertible-hom-Precategory :
    is-section-hom-Precategory C
      ( hom-invertible-hom-Precategory)
      ( hom-inv-invertible-hom-Precategory)
  is-section-hom-inv-invertible-hom-Precategory =
    is-section-hom-inv-is-invertible-hom-Precategory C
      ( is-invertible-hom-iso-Precategory)

  is-retraction-hom-inv-invertible-hom-Precategory :
    is-retraction-hom-Precategory C
      ( hom-invertible-hom-Precategory)
      ( hom-inv-invertible-hom-Precategory)
  is-retraction-hom-inv-invertible-hom-Precategory =
    is-retraction-hom-inv-is-invertible-hom-Precategory C
      ( is-invertible-hom-iso-Precategory)
```

## Examples

### The invertible identity morphisms

For any object `x` of a precategory `C`, the identity morphism `id : hom x x` is an invertible morphism
from `x` to `x` since `id ∘ id = id`, i.e., the identity morphism is its own inverse.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) {x : obj-Precategory C}
  where

  is-invertible-hom-id-hom-Precategory :
    is-invertible-hom-Precategory C (id-hom-Precategory C {x})
  pr1 is-invertible-hom-id-hom-Precategory = id-hom-Precategory C
  pr1 (pr2 is-invertible-hom-id-hom-Precategory) =
    left-unit-law-comp-hom-Precategory C (id-hom-Precategory C)
  pr2 (pr2 is-invertible-hom-id-hom-Precategory) =
    right-unit-law-comp-hom-Precategory C (id-hom-Precategory C)

  id-invertible-hom-Precategory : invertible-hom-Precategory C x x
  pr1 id-invertible-hom-Precategory = id-hom-Precategory C
  pr2 id-invertible-hom-Precategory = is-invertible-hom-id-hom-Precategory
```

### Identifications induce invertible morphisms

For any two objects `x` and `y` of a precategory `C`, there a map

```text
  x ＝ y → invertible-hom-Precategory C x y.
```

We construct this map by observing that we already have a map

```text
  hom-eq-Precategory : x ＝ y → hom-Precategory C x y
```

satisfying `hom-eq-Precategory refl ≐ id-hom-Precategory`. Since the identity morphism is invertible, it follows by identification elimination that all morphisms of the form `hom-eq-Precategory p` are invertible.

Note that we could have defined the map

```text
  invertible-hom-eq-Precategory : x ＝ y → invertible-hom-Precategory C x y.
```

directly by identification elimination. However, with our current definition it follows that the underlying map of `invertible-hom-eq-Precategory p` always computes to `hom-eq-Precategory p`, which could sometimes be useful to know.

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  where

  invertible-hom-eq-Precategory :
    (x y : obj-Precategory C) → x ＝ y → invertible-hom-Precategory C x y
  pr1 (invertible-hom-eq-Precategory x y p) =
    hom-eq-Precategory C x y p
  pr2 (invertible-hom-eq-Precategory x .x refl) =
    is-invertible-hom-id-hom-Precategory C

  compute-hom-invertible-hom-eq-Precategory :
    {x y : obj-Precategory C} (p : x ＝ y) →
    hom-eq-Precategory C x y p ＝
    hom-invertible-hom-Precategory C (invertible-hom-eq-Precategory x y p)
  compute-hom-invertible-hom-eq-Precategory p = refl
```

## Properties

### Being an invertible morphism is a proposition

Let `f : hom x y` and suppose `g g' : hom y x` are both inverses of `f`.
It is enough to show that `g = g'` since being a section and being a retraction
is always a [proposition](foundation-core.propositions.md).
Using that `g` and `g'` are both inverses of `f` we have the following chain of identifications:

```text
  g ＝ g ∘ id
    ＝ g ∘ (f ∘ g')
    ＝ (g ∘ f) ∘ g'
    ＝ id ∘ g'
    ＝ g'.
```

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  where

  all-elements-equal-is-invertible-hom-Precategory :
    (f : hom-Precategory C x y)
    (H K : is-invertible-hom-Precategory C f) → H ＝ K
  all-elements-equal-is-invertible-hom-Precategory f
    (g , p , q) (g' , p' , q') =
    eq-type-subtype
      ( λ g →
        product-Prop
          ( Id-Prop
            ( hom-set-Precategory C y y)
            ( comp-hom-Precategory C f g)
            ( id-hom-Precategory C))
          ( Id-Prop
            ( hom-set-Precategory C x x)
            ( comp-hom-Precategory C g f)
            ( id-hom-Precategory C)))
      ( ( inv (right-unit-law-comp-hom-Precategory C g)) ∙
        ( ap ( comp-hom-Precategory C g) (inv p')) ∙
        ( inv (associative-comp-hom-Precategory C g f g')) ∙
        ( ap ( comp-hom-Precategory' C g') q) ∙
        ( left-unit-law-comp-hom-Precategory C g'))

  is-prop-is-invertible-hom-Precategory :
    (f : hom-Precategory C x y) →
    is-prop (is-invertible-hom-Precategory C f)
  is-prop-is-invertible-hom-Precategory f =
    is-prop-all-elements-equal
      ( all-elements-equal-is-invertible-hom-Precategory f)

  is-invertible-hom-prop-Precategory :
    (f : hom-Precategory C x y) → Prop l2
  pr1 (is-invertible-hom-prop-Precategory f) =
    is-invertible-hom-Precategory C f
  pr2 (is-invertible-hom-prop-Precategory f) =
    is-prop-is-invertible-hom-Precategory f
```

### Equality of invertible morphism is equality of their underlying morphisms

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  where

  eq-invertible-hom-eq-hom-Precategory :
    (f g : invertible-hom-Precategory C x y) →
    hom-invertible-hom-Precategory C f ＝ hom-invertible-hom-Precategory C g →
    f ＝ g
  eq-invertible-hom-eq-hom-Precategory f g =
    eq-type-subtype (is-invertible-hom-prop-Precategory C)
```

### The type of invertible morphisms form a set

The type of invertible morphisms between objects `x y : A` is a
[subtype](foundation-core.subtypes.md) of the [foundation-core.sets.md)
`hom x y` since being an invertible morphism is a proposition.

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  where

  is-set-invertible-hom-Precategory : is-set (invertible-hom-Precategory C x y)
  is-set-invertible-hom-Precategory =
    is-set-type-subtype
      ( is-invertible-hom-prop-Precategory C)
      ( is-set-hom-Precategory C x y)

  invertible-hom-set-Precategory : Set l2
  pr1 invertible-hom-set-Precategory = invertible-hom-Precategory C x y
  pr2 invertible-hom-set-Precategory = is-set-invertible-hom-Precategory
```

### Invertible morphisms are closed under composition

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y z : obj-Precategory C}
  {g : hom-Precategory C y z}
  {f : hom-Precategory C x y}
  where

  hom-comp-is-invertible-hom-Precategory :
    is-invertible-hom-Precategory C g →
    is-invertible-hom-Precategory C f →
    hom-Precategory C z x
  hom-comp-is-invertible-hom-Precategory q p =
    comp-hom-Precategory C
      ( hom-inv-is-invertible-hom-Precategory C p)
      ( hom-inv-is-invertible-hom-Precategory C q)

  is-section-comp-is-invertible-hom-Precategory :
    (q : is-invertible-hom-Precategory C g)
    (p : is-invertible-hom-Precategory C f) →
    comp-hom-Precategory C
      ( comp-hom-Precategory C g f)
      ( hom-comp-is-invertible-hom-Precategory q p) ＝
    id-hom-Precategory C
  is-section-comp-is-invertible-hom-Precategory q p =
    ( associative-comp-hom-Precategory C g f _) ∙
    ( ap
      ( comp-hom-Precategory C g)
      ( ( inv
          ( associative-comp-hom-Precategory C f
            ( hom-inv-is-invertible-hom-Precategory C p)
            ( hom-inv-is-invertible-hom-Precategory C q))) ∙
        ( ap
          ( λ h →
            comp-hom-Precategory C h
              ( hom-inv-is-invertible-hom-Precategory C q))
          ( is-section-hom-inv-is-invertible-hom-Precategory C p) ∙
          ( left-unit-law-comp-hom-Precategory C
            ( hom-inv-is-invertible-hom-Precategory C q))))) ∙
    ( is-section-hom-inv-is-invertible-hom-Precategory C q)

  is-retraction-comp-is-invertible-hom-Precategory :
    (q : is-invertible-hom-Precategory C g)
    (p : is-invertible-hom-Precategory C f) →
    ( comp-hom-Precategory C
      ( hom-comp-is-invertible-hom-Precategory q p)
      ( comp-hom-Precategory C g f)) ＝
    ( id-hom-Precategory C)
  is-retraction-comp-is-invertible-hom-Precategory q p =
    ( associative-comp-hom-Precategory C
      ( hom-inv-is-invertible-hom-Precategory C p)
      ( hom-inv-is-invertible-hom-Precategory C q)
      ( comp-hom-Precategory C g f)) ∙
    ( ap
      ( comp-hom-Precategory
        ( C)
        ( hom-inv-is-invertible-hom-Precategory C p))
      ( ( inv
          ( associative-comp-hom-Precategory C
            ( hom-inv-is-invertible-hom-Precategory C q)
            ( g)
            ( f))) ∙
        ( ap
            ( λ h → comp-hom-Precategory C h f)
            ( is-retraction-hom-inv-is-invertible-hom-Precategory C q)) ∙
        ( left-unit-law-comp-hom-Precategory C f))) ∙
    ( is-retraction-hom-inv-is-invertible-hom-Precategory C p)

  is-invertible-hom-comp-is-invertible-hom-Precategory :
    is-invertible-hom-Precategory C g → is-invertible-hom-Precategory C f →
    is-invertible-hom-Precategory C (comp-hom-Precategory C g f)
  pr1 (is-invertible-hom-comp-is-invertible-hom-Precategory q p) =
    hom-comp-is-invertible-hom-Precategory q p
  pr1 (pr2 (is-invertible-hom-comp-is-invertible-hom-Precategory q p)) =
    is-section-comp-is-invertible-hom-Precategory q p
  pr2 (pr2 (is-invertible-hom-comp-is-invertible-hom-Precategory q p)) =
    is-retraction-comp-is-invertible-hom-Precategory q p
```

### The composition operation on invertible morphisms

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y z : obj-Precategory C}
  (g : invertible-hom-Precategory C y z)
  (f : invertible-hom-Precategory C x y)
  where

  hom-comp-invertible-hom-Precategory :
    hom-Precategory C x z
  hom-comp-invertible-hom-Precategory =
    comp-hom-Precategory C
      ( hom-invertible-hom-Precategory C g)
      ( hom-invertible-hom-Precategory C f)

  is-invertible-hom-comp-invertible-hom-Precategory :
    is-invertible-hom-Precategory C hom-comp-invertible-hom-Precategory
  is-invertible-hom-comp-invertible-hom-Precategory =
    is-invertible-hom-comp-is-invertible-hom-Precategory C
      ( is-invertible-hom-iso-Precategory C g)
      ( is-invertible-hom-iso-Precategory C f)

  comp-invertible-hom-Precategory : invertible-hom-Precategory C x z
  pr1 comp-invertible-hom-Precategory =
    hom-comp-invertible-hom-Precategory
  pr2 comp-invertible-hom-Precategory =
    is-invertible-hom-comp-invertible-hom-Precategory

  hom-inv-comp-invertible-hom-Precategory : hom-Precategory C z x
  hom-inv-comp-invertible-hom-Precategory =
    hom-inv-invertible-hom-Precategory C comp-invertible-hom-Precategory

  is-section-inv-comp-invertible-hom-Precategory :
    ( comp-hom-Precategory C
      ( hom-comp-invertible-hom-Precategory)
      ( hom-inv-comp-invertible-hom-Precategory)) ＝
    ( id-hom-Precategory C)
  is-section-inv-comp-invertible-hom-Precategory =
    is-section-hom-inv-invertible-hom-Precategory C
      ( comp-invertible-hom-Precategory)

  is-retraction-inv-comp-invertible-hom-Precategory :
    ( comp-hom-Precategory C
      ( hom-inv-comp-invertible-hom-Precategory)
      ( hom-comp-invertible-hom-Precategory)) ＝
    ( id-hom-Precategory C)
  is-retraction-inv-comp-invertible-hom-Precategory =
    is-retraction-hom-inv-invertible-hom-Precategory C
      ( comp-invertible-hom-Precategory)
```

### Inverses of invertible morphisms are invertible morphisms

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  {f : hom-Precategory C x y}
  where

  is-invertible-hom-inv-is-invertible-hom-Precategory :
    (p : is-invertible-hom-Precategory C f) →
    is-invertible-hom-Precategory C
      ( hom-inv-invertible-hom-Precategory C (f , p))
  pr1 (is-invertible-hom-inv-is-invertible-hom-Precategory p) = f
  pr1 (pr2 (is-invertible-hom-inv-is-invertible-hom-Precategory p)) =
    is-retraction-hom-inv-is-invertible-hom-Precategory C p
  pr2 (pr2 (is-invertible-hom-inv-is-invertible-hom-Precategory p)) =
    is-section-hom-inv-is-invertible-hom-Precategory C p
```

### Inverses of invertible morphisms

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  where

  inv-invertible-hom-Precategory :
    invertible-hom-Precategory C x y → invertible-hom-Precategory C y x
  pr1 (inv-invertible-hom-Precategory f) =
    hom-inv-invertible-hom-Precategory C f
  pr2 (inv-invertible-hom-Precategory f) =
    is-invertible-hom-inv-is-invertible-hom-Precategory C
      ( is-invertible-hom-iso-Precategory C f)

  is-invertible-hom-inv-invertible-hom-Precategory :
    (f : invertible-hom-Precategory C x y) →
    is-invertible-hom-Precategory C (hom-inv-invertible-hom-Precategory C f)
  is-invertible-hom-inv-invertible-hom-Precategory f =
    is-invertible-hom-iso-Precategory C (inv-invertible-hom-Precategory f)
```

### Groupoid laws of invertible morphisms in precategories

#### Composition of invertible morphisms satisfies the unit laws

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  (f : invertible-hom-Precategory C x y)
  where

  left-unit-law-comp-invertible-hom-Precategory :
    comp-invertible-hom-Precategory C (id-invertible-hom-Precategory C) f ＝ f
  left-unit-law-comp-invertible-hom-Precategory =
    eq-invertible-hom-eq-hom-Precategory C
      ( comp-invertible-hom-Precategory C (id-invertible-hom-Precategory C) f)
      ( f)
      ( left-unit-law-comp-hom-Precategory C
        ( hom-invertible-hom-Precategory C f))

  right-unit-law-comp-invertible-hom-Precategory :
    comp-invertible-hom-Precategory C f (id-invertible-hom-Precategory C) ＝ f
  right-unit-law-comp-invertible-hom-Precategory =
    eq-invertible-hom-eq-hom-Precategory C
      ( comp-invertible-hom-Precategory C f (id-invertible-hom-Precategory C))
      ( f)
      ( right-unit-law-comp-hom-Precategory C
        ( hom-invertible-hom-Precategory C f))
```

#### Composition of invertible morphisms is associative

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y z w : obj-Precategory C}
  (h : invertible-hom-Precategory C z w)
  (g : invertible-hom-Precategory C y z)
  (f : invertible-hom-Precategory C x y)
  where

  associative-comp-invertible-hom-Precategory :
    ( comp-invertible-hom-Precategory C
      ( comp-invertible-hom-Precategory C h g)
      ( f)) ＝
    ( comp-invertible-hom-Precategory C
      ( h)
      ( comp-invertible-hom-Precategory C g f))
  associative-comp-invertible-hom-Precategory =
    eq-invertible-hom-eq-hom-Precategory C
      ( comp-invertible-hom-Precategory C
        ( comp-invertible-hom-Precategory C h g)
        ( f))
      ( comp-invertible-hom-Precategory C
        ( h)
        ( comp-invertible-hom-Precategory C g f))
      ( associative-comp-hom-Precategory C
        ( hom-invertible-hom-Precategory C h)
        ( hom-invertible-hom-Precategory C g)
        ( hom-invertible-hom-Precategory C f))
```

#### Composition of invertible morphisms satisfies inverse laws

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  (f : invertible-hom-Precategory C x y)
  where

  left-inverse-law-comp-invertible-hom-Precategory :
    ( comp-invertible-hom-Precategory C
      ( inv-invertible-hom-Precategory C f)
      ( f)) ＝
    ( id-invertible-hom-Precategory C)
  left-inverse-law-comp-invertible-hom-Precategory =
    eq-invertible-hom-eq-hom-Precategory C
      ( comp-invertible-hom-Precategory C
        ( inv-invertible-hom-Precategory C f)
        ( f))
      ( id-invertible-hom-Precategory C)
      ( is-retraction-hom-inv-invertible-hom-Precategory C f)

  right-inverse-law-comp-invertible-hom-Precategory :
    ( comp-invertible-hom-Precategory C
      ( f)
      ( inv-invertible-hom-Precategory C f)) ＝
    ( id-invertible-hom-Precategory C)
  right-inverse-law-comp-invertible-hom-Precategory =
    eq-invertible-hom-eq-hom-Precategory C
      ( comp-invertible-hom-Precategory C f
        ( inv-invertible-hom-Precategory C f))
      ( id-invertible-hom-Precategory C)
      ( is-section-hom-inv-invertible-hom-Precategory C f)
```

### The inverse operation is a fibered involution on invertible morphisms

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  where

  is-fibered-involution-inv-invertible-hom-Precategory :
    {x y : obj-Precategory C} →
    inv-invertible-hom-Precategory C {y} {x} ∘
    inv-invertible-hom-Precategory C {x} {y} ~
    id
  is-fibered-involution-inv-invertible-hom-Precategory f = refl

  is-equiv-inv-invertible-hom-Precategory :
    {x y : obj-Precategory C} →
    is-equiv (inv-invertible-hom-Precategory C {x} {y})
  is-equiv-inv-invertible-hom-Precategory =
    is-equiv-is-invertible
      ( inv-invertible-hom-Precategory C)
      ( is-fibered-involution-inv-invertible-hom-Precategory)
      ( is-fibered-involution-inv-invertible-hom-Precategory)

  equiv-inv-invertible-hom-Precategory :
    {x y : obj-Precategory C} →
    invertible-hom-Precategory C x y ≃ invertible-hom-Precategory C y x
  pr1 equiv-inv-invertible-hom-Precategory =
    inv-invertible-hom-Precategory C
  pr2 equiv-inv-invertible-hom-Precategory =
    is-equiv-inv-invertible-hom-Precategory
```

### A morphism `f` is invertible if and only if precomposition by `f` is an equivalence

**Proof:** If `f` is invertible with inverse `f⁻¹`, then precomposing with
`f⁻¹` is an inverse of precomposing with `f`. The only interesting direction is
therefore the converse.

Suppose that precomposing with `f` is an equivalence, for any object `z`. Then

```text
  - ∘ f : hom y x → hom x x
```

is an equivalence. In particular, there is a unique morphism `g : y → x` such
that `g ∘ f ＝ id`. Thus we have a retraction of `f`. To see that `g` is also a
section, note that the map

```text
  - ∘ f : hom y y → hom x y
```

is an equivalence. In particular, it is injective. Therefore it suffices to show
that `(f ∘ g) ∘ f ＝ id ∘ f`. To see this, we calculate

```text
  (f ∘ g) ∘ f ＝ f ∘ (g ∘ f) ＝ f ∘ id ＝ f ＝ id ∘ f.
```

This completes the proof.

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  {f : hom-Precategory C x y}
  (H : (z : obj-Precategory C) → is-equiv (precomp-hom-Precategory C f z))
  where

  hom-inv-is-invertible-hom-is-equiv-precomp-hom-Precategory :
    hom-Precategory C y x
  hom-inv-is-invertible-hom-is-equiv-precomp-hom-Precategory =
    map-inv-is-equiv (H x) (id-hom-Precategory C)

  is-retraction-hom-inv-is-invertible-hom-is-equiv-precomp-hom-Precategory :
    is-retraction-hom-Precategory C f
      ( hom-inv-is-invertible-hom-is-equiv-precomp-hom-Precategory)
  is-retraction-hom-inv-is-invertible-hom-is-equiv-precomp-hom-Precategory =
    is-section-map-inv-is-equiv (H x) (id-hom-Precategory C)

  is-section-hom-inv-is-invertible-hom-is-equiv-precomp-hom-Precategory :
    is-section-hom-Precategory C f
      ( hom-inv-is-invertible-hom-is-equiv-precomp-hom-Precategory)
  is-section-hom-inv-is-invertible-hom-is-equiv-precomp-hom-Precategory =
    is-injective-is-equiv
      ( H y)
      ( ( associative-comp-hom-Precategory C
          ( f)
          ( hom-inv-is-invertible-hom-is-equiv-precomp-hom-Precategory)
          ( f)) ∙
        ( ap
          ( comp-hom-Precategory C f)
          ( is-retraction-hom-inv-is-invertible-hom-is-equiv-precomp-hom-Precategory)) ∙
        ( right-unit-law-comp-hom-Precategory C f) ∙
        ( inv (left-unit-law-comp-hom-Precategory C f)))

  is-invertible-hom-is-equiv-precomp-hom-Precategory :
    is-invertible-hom-Precategory C f
  pr1 is-invertible-hom-is-equiv-precomp-hom-Precategory =
    hom-inv-is-invertible-hom-is-equiv-precomp-hom-Precategory
  pr1 (pr2 is-invertible-hom-is-equiv-precomp-hom-Precategory) =
    is-section-hom-inv-is-invertible-hom-is-equiv-precomp-hom-Precategory
  pr2 (pr2 is-invertible-hom-is-equiv-precomp-hom-Precategory) =
    is-retraction-hom-inv-is-invertible-hom-is-equiv-precomp-hom-Precategory

module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  {f : hom-Precategory C x y}
  (is-invertible-hom-f : is-invertible-hom-Precategory C f)
  (z : obj-Precategory C)
  where

  map-inv-precomp-hom-is-invertible-hom-Precategory :
    hom-Precategory C x z → hom-Precategory C y z
  map-inv-precomp-hom-is-invertible-hom-Precategory =
    precomp-hom-Precategory C
      ( hom-inv-is-invertible-hom-Precategory C is-invertible-hom-f)
      ( z)

  is-section-map-inv-precomp-hom-is-invertible-hom-Precategory :
    is-section
      ( precomp-hom-Precategory C f z)
      ( map-inv-precomp-hom-is-invertible-hom-Precategory)
  is-section-map-inv-precomp-hom-is-invertible-hom-Precategory g =
    ( associative-comp-hom-Precategory C
      ( g)
      ( hom-inv-is-invertible-hom-Precategory C is-invertible-hom-f)
      ( f)) ∙
    ( ap
      ( comp-hom-Precategory C g)
      ( is-retraction-hom-inv-is-invertible-hom-Precategory C
        ( is-invertible-hom-f))) ∙
    ( right-unit-law-comp-hom-Precategory C g)

  is-retraction-map-inv-precomp-hom-is-invertible-hom-Precategory :
    is-retraction
      ( precomp-hom-Precategory C f z)
      ( map-inv-precomp-hom-is-invertible-hom-Precategory)
  is-retraction-map-inv-precomp-hom-is-invertible-hom-Precategory g =
    ( associative-comp-hom-Precategory C
      ( g)
      ( f)
      ( hom-inv-is-invertible-hom-Precategory C is-invertible-hom-f)) ∙
    ( ap
      ( comp-hom-Precategory C g)
      ( is-section-hom-inv-is-invertible-hom-Precategory C
        ( is-invertible-hom-f))) ∙
    ( right-unit-law-comp-hom-Precategory C g)

  is-equiv-precomp-hom-is-invertible-hom-Precategory :
    is-equiv (precomp-hom-Precategory C f z)
  is-equiv-precomp-hom-is-invertible-hom-Precategory =
    is-equiv-is-invertible
      ( map-inv-precomp-hom-is-invertible-hom-Precategory)
      ( is-section-map-inv-precomp-hom-is-invertible-hom-Precategory)
      ( is-retraction-map-inv-precomp-hom-is-invertible-hom-Precategory)

  equiv-precomp-hom-is-invertible-hom-Precategory :
    hom-Precategory C y z ≃ hom-Precategory C x z
  pr1 equiv-precomp-hom-is-invertible-hom-Precategory =
    precomp-hom-Precategory C f z
  pr2 equiv-precomp-hom-is-invertible-hom-Precategory =
    is-equiv-precomp-hom-is-invertible-hom-Precategory

module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  (f : invertible-hom-Precategory C x y)
  (z : obj-Precategory C)
  where

  is-equiv-precomp-hom-invertible-hom-Precategory :
    is-equiv (precomp-hom-Precategory C (hom-invertible-hom-Precategory C f) z)
  is-equiv-precomp-hom-invertible-hom-Precategory =
    is-equiv-precomp-hom-is-invertible-hom-Precategory C
      ( is-invertible-hom-iso-Precategory C f)
      ( z)

  equiv-precomp-hom-invertible-hom-Precategory :
    hom-Precategory C y z ≃ hom-Precategory C x z
  equiv-precomp-hom-invertible-hom-Precategory =
    equiv-precomp-hom-is-invertible-hom-Precategory C
      ( is-invertible-hom-iso-Precategory C f)
      ( z)
```

### A morphism `f` is invertible if and only if postcomposition by `f` is an equivalence

**Proof:** If `f` is invertible with inverse `f⁻¹`, then postcomposing with
`f⁻¹` is an inverse of postcomposing with `f`. The only interesting direction is
therefore the converse.

Suppose that postcomposing with `f` is an equivalence, for any object `z`. Then

```text
  f ∘ - : hom y x → hom y y
```

is an equivalence. In particular, there is a unique morphism `g : y → x` such
that `f ∘ g ＝ id`. Thus we have a section of `f`. To see that `g` is also a
retraction, note that the map

```text
  f ∘ - : hom x x → hom x y
```

is an equivalence. In particular, it is injective. Therefore it suffices to show
that `f ∘ (g ∘ f) ＝ f ∘ id`. To see this, we calculate

```text
  f ∘ (g ∘ f) ＝ (f ∘ g) ∘ f ＝ id ∘ f ＝ f ＝ f ∘ id.
```

This completes the proof.

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  {f : hom-Precategory C x y}
  (H : (z : obj-Precategory C) → is-equiv (postcomp-hom-Precategory C f z))
  where

  hom-inv-is-invertible-hom-is-equiv-postcomp-hom-Precategory :
    hom-Precategory C y x
  hom-inv-is-invertible-hom-is-equiv-postcomp-hom-Precategory =
    map-inv-is-equiv (H y) (id-hom-Precategory C)

  is-section-hom-inv-is-invertible-hom-is-equiv-postcomp-hom-Precategory :
    is-section-hom-Precategory C f
      ( hom-inv-is-invertible-hom-is-equiv-postcomp-hom-Precategory)
  is-section-hom-inv-is-invertible-hom-is-equiv-postcomp-hom-Precategory =
    is-section-map-inv-is-equiv (H y) (id-hom-Precategory C)

  is-retraction-hom-inv-is-invertible-hom-is-equiv-postcomp-hom-Precategory :
    is-retraction-hom-Precategory C f
      ( hom-inv-is-invertible-hom-is-equiv-postcomp-hom-Precategory)
  is-retraction-hom-inv-is-invertible-hom-is-equiv-postcomp-hom-Precategory =
    is-injective-is-equiv
      ( H x)
      ( ( inv
          ( associative-comp-hom-Precategory C
            ( f)
            ( hom-inv-is-invertible-hom-is-equiv-postcomp-hom-Precategory)
            ( f))) ∙
        ( ap
          ( comp-hom-Precategory' C f)
          ( is-section-hom-inv-is-invertible-hom-is-equiv-postcomp-hom-Precategory)) ∙
        ( left-unit-law-comp-hom-Precategory C f) ∙
        ( inv (right-unit-law-comp-hom-Precategory C f)))

  is-invertible-hom-is-equiv-postcomp-hom-Precategory :
    is-invertible-hom-Precategory C f
  pr1 is-invertible-hom-is-equiv-postcomp-hom-Precategory =
    hom-inv-is-invertible-hom-is-equiv-postcomp-hom-Precategory
  pr1 (pr2 is-invertible-hom-is-equiv-postcomp-hom-Precategory) =
    is-section-hom-inv-is-invertible-hom-is-equiv-postcomp-hom-Precategory
  pr2 (pr2 is-invertible-hom-is-equiv-postcomp-hom-Precategory) =
    is-retraction-hom-inv-is-invertible-hom-is-equiv-postcomp-hom-Precategory

module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  {f : hom-Precategory C x y}
  (is-invertible-hom-f : is-invertible-hom-Precategory C f)
  (z : obj-Precategory C)
  where

  map-inv-postcomp-hom-is-invertible-hom-Precategory :
    hom-Precategory C z y → hom-Precategory C z x
  map-inv-postcomp-hom-is-invertible-hom-Precategory =
    postcomp-hom-Precategory C
      ( hom-inv-is-invertible-hom-Precategory C is-invertible-hom-f)
      ( z)

  is-section-map-inv-postcomp-hom-is-invertible-hom-Precategory :
    is-section
      ( postcomp-hom-Precategory C f z)
      ( map-inv-postcomp-hom-is-invertible-hom-Precategory)
  is-section-map-inv-postcomp-hom-is-invertible-hom-Precategory g =
    ( inv
      ( associative-comp-hom-Precategory C
        ( f)
        ( hom-inv-is-invertible-hom-Precategory C is-invertible-hom-f)
        ( g))) ∙
    ( ap
      ( comp-hom-Precategory' C g)
      ( is-section-hom-inv-is-invertible-hom-Precategory C
        ( is-invertible-hom-f))) ∙
    ( left-unit-law-comp-hom-Precategory C g)

  is-retraction-map-inv-postcomp-hom-is-invertible-hom-Precategory :
    is-retraction
      ( postcomp-hom-Precategory C f z)
      ( map-inv-postcomp-hom-is-invertible-hom-Precategory)
  is-retraction-map-inv-postcomp-hom-is-invertible-hom-Precategory g =
    ( inv
      ( associative-comp-hom-Precategory C
        ( hom-inv-is-invertible-hom-Precategory C is-invertible-hom-f)
        ( f)
        ( g))) ∙
    ( ap
      ( comp-hom-Precategory' C g)
      ( is-retraction-hom-inv-is-invertible-hom-Precategory C
        ( is-invertible-hom-f))) ∙
    ( left-unit-law-comp-hom-Precategory C g)

  is-equiv-postcomp-hom-is-invertible-hom-Precategory :
    is-equiv (postcomp-hom-Precategory C f z)
  is-equiv-postcomp-hom-is-invertible-hom-Precategory =
    is-equiv-is-invertible
      ( map-inv-postcomp-hom-is-invertible-hom-Precategory)
      ( is-section-map-inv-postcomp-hom-is-invertible-hom-Precategory)
      ( is-retraction-map-inv-postcomp-hom-is-invertible-hom-Precategory)

  equiv-postcomp-hom-is-invertible-hom-Precategory :
    hom-Precategory C z x ≃ hom-Precategory C z y
  pr1 equiv-postcomp-hom-is-invertible-hom-Precategory =
    postcomp-hom-Precategory C f z
  pr2 equiv-postcomp-hom-is-invertible-hom-Precategory =
    is-equiv-postcomp-hom-is-invertible-hom-Precategory

module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  (f : invertible-hom-Precategory C x y)
  (z : obj-Precategory C)
  where

  is-equiv-postcomp-hom-invertible-hom-Precategory :
    is-equiv (postcomp-hom-Precategory C (hom-invertible-hom-Precategory C f) z)
  is-equiv-postcomp-hom-invertible-hom-Precategory =
    is-equiv-postcomp-hom-is-invertible-hom-Precategory C
      ( is-invertible-hom-iso-Precategory C f)
      ( z)

  equiv-postcomp-hom-invertible-hom-Precategory :
    hom-Precategory C z x ≃ hom-Precategory C z y
  equiv-postcomp-hom-invertible-hom-Precategory =
    equiv-postcomp-hom-is-invertible-hom-Precategory C
      ( is-invertible-hom-iso-Precategory C f)
      ( z)
```

### When `hom x y` is a proposition, The type of invertible morphisms from `x` to `y` is a proposition

The type of invertible morphisms between objects `x y : A` is a subtype of `hom x y`, so
when this type is a proposition, then the type of invertible morphisms from `x` to `y`
form a proposition.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  where

  is-prop-invertible-hom-is-prop-hom-Precategory :
    is-prop (hom-Precategory C x y) → is-prop (invertible-hom-Precategory C x y)
  is-prop-invertible-hom-is-prop-hom-Precategory =
    is-prop-type-subtype (is-invertible-hom-prop-Precategory C)

  invertible-hom-prop-is-prop-hom-Precategory :
    is-prop (hom-Precategory C x y) → Prop l2
  pr1 (invertible-hom-prop-is-prop-hom-Precategory is-prop-hom-C-x-y) =
    invertible-hom-Precategory C x y
  pr2 (invertible-hom-prop-is-prop-hom-Precategory is-prop-hom-C-x-y) =
    is-prop-invertible-hom-is-prop-hom-Precategory is-prop-hom-C-x-y
```

### When `hom x y` and `hom y x` are propositions, it suffices to provide a morphism in each direction to construct an invertible morphism

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  {x y : obj-Precategory C}
  where

  is-invertible-hom-is-prop-hom-Precategory' :
    is-prop (hom-Precategory C x x) →
    is-prop (hom-Precategory C y y) →
    (f : hom-Precategory C x y) →
    hom-Precategory C y x →
    is-invertible-hom-Precategory C f
  is-invertible-hom-is-prop-hom-Precategory' H K f g =
    (g , eq-is-prop K , eq-is-prop H)

  invertible-hom-is-prop-hom-Precategory' :
    is-prop (hom-Precategory C x x) →
    is-prop (hom-Precategory C y y) →
    hom-Precategory C x y →
    hom-Precategory C y x →
    invertible-hom-Precategory C x y
  pr1 (invertible-hom-is-prop-hom-Precategory' _ _ f g) = f
  pr2 (invertible-hom-is-prop-hom-Precategory' H K f g) =
    is-invertible-hom-is-prop-hom-Precategory' H K f g

  is-invertible-hom-is-prop-hom-Precategory :
    ((x' y' : obj-Precategory C) → is-prop (hom-Precategory C x' y')) →
    (f : hom-Precategory C x y) → hom-Precategory C y x →
    is-invertible-hom-Precategory C f
  is-invertible-hom-is-prop-hom-Precategory H =
    is-invertible-hom-is-prop-hom-Precategory' (H x x) (H y y)

  invertible-hom-is-prop-hom-Precategory :
    ((x' y' : obj-Precategory C) → is-prop (hom-Precategory C x' y')) →
    hom-Precategory C x y →
    hom-Precategory C y x →
    invertible-hom-Precategory C x y
  invertible-hom-is-prop-hom-Precategory H =
    invertible-hom-is-prop-hom-Precategory' (H x x) (H y y)
```

### Functoriality of `invertible-hom-eq`

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  {x y z : obj-Precategory C}
  where

  preserves-concat-invertible-hom-eq-Precategory :
    (p : x ＝ y) (q : y ＝ z) →
    invertible-hom-eq-Precategory C x z (p ∙ q) ＝
    comp-invertible-hom-Precategory C
      ( invertible-hom-eq-Precategory C y z q)
      ( invertible-hom-eq-Precategory C x y p)
  preserves-concat-invertible-hom-eq-Precategory refl q =
    inv
      ( right-unit-law-comp-invertible-hom-Precategory C
        ( invertible-hom-eq-Precategory C y z q))
```
