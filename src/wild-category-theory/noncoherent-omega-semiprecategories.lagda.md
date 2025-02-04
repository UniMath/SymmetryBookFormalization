# Noncoherent ω-semiprecategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.noncoherent-omega-semiprecategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import globular-types.binary-globular-maps
open import globular-types.composition-structure-globular-types
open import globular-types.globular-types
```

</details>

## Idea

A
{{#concept "noncoherent ω-semiprecategory" Agda=Noncoherent-ω-Semiprecategory}}
`𝒞` is a [globular type](globular-types.globular-types.md) `G`
[equipped](foundation.structure.md) with a
[composition structure](globular-types.composition-structure-globular-types.md).
It comes equipped with a type of objects `𝒞₀` such that for every pair of
objects `x y : 𝒞₀` there is a type of _morphisms_ `𝒞₁ x y`, in fact, a
noncoherent ω-semiprecategory of morphisms. For every pair of morphisms
`g : 𝒞₁ y z` and `f : 𝒞₁ x y` there is a morphism `g ∘ f : 𝒞₁ x z`, and a
noncoherent ω-semiprecategory also comes equipped with horizontal composition
operations on its higher morphisms.

## Definitions

### Noncoherent ω-semiprecategories

```agda
Noncoherent-ω-Semiprecategory : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Noncoherent-ω-Semiprecategory l1 l2 =
  Σ (Globular-Type l1 l2) (composition-Globular-Type)
```

```agda
module _
  {l1 l2 : Level} (𝒞 : Noncoherent-ω-Semiprecategory l1 l2)
  where

  globular-type-Noncoherent-ω-Semiprecategory : Globular-Type l1 l2
  globular-type-Noncoherent-ω-Semiprecategory = pr1 𝒞

  obj-Noncoherent-ω-Semiprecategory : UU l1
  obj-Noncoherent-ω-Semiprecategory =
    0-cell-Globular-Type globular-type-Noncoherent-ω-Semiprecategory
```

Morphisms in a noncoherent ω-semiprecategory:

```agda
  hom-globular-type-Noncoherent-ω-Semiprecategory :
    (x y : obj-Noncoherent-ω-Semiprecategory) → Globular-Type l2 l2
  hom-globular-type-Noncoherent-ω-Semiprecategory =
    1-cell-globular-type-Globular-Type
      globular-type-Noncoherent-ω-Semiprecategory

  hom-Noncoherent-ω-Semiprecategory :
    (x y : obj-Noncoherent-ω-Semiprecategory) → UU l2
  hom-Noncoherent-ω-Semiprecategory =
    1-cell-Globular-Type globular-type-Noncoherent-ω-Semiprecategory
```

Composition in a noncoherent ω-semiprecategory:

```agda
  composition-Noncoherent-ω-Semiprecategory :
    composition-Globular-Type globular-type-Noncoherent-ω-Semiprecategory
  composition-Noncoherent-ω-Semiprecategory = pr2 𝒞

  comp-binary-globular-map-hom-Noncoherent-ω-Semiprecategory :
    {x y z : obj-Noncoherent-ω-Semiprecategory} →
    binary-globular-map
      ( hom-globular-type-Noncoherent-ω-Semiprecategory y z)
      ( hom-globular-type-Noncoherent-ω-Semiprecategory x y)
      ( hom-globular-type-Noncoherent-ω-Semiprecategory x z)
  comp-binary-globular-map-hom-Noncoherent-ω-Semiprecategory =
    comp-binary-globular-map-composition-Globular-Type
      composition-Noncoherent-ω-Semiprecategory

  comp-hom-Noncoherent-ω-Semiprecategory :
    {x y z : obj-Noncoherent-ω-Semiprecategory} →
    hom-Noncoherent-ω-Semiprecategory y z →
    hom-Noncoherent-ω-Semiprecategory x y →
    hom-Noncoherent-ω-Semiprecategory x z
  comp-hom-Noncoherent-ω-Semiprecategory =
    comp-1-cell-composition-Globular-Type
      composition-Noncoherent-ω-Semiprecategory

  composition-hom-Noncoherent-ω-Semiprecategory :
    {x y : obj-Noncoherent-ω-Semiprecategory} →
    composition-Globular-Type
      ( hom-globular-type-Noncoherent-ω-Semiprecategory x y)
  composition-hom-Noncoherent-ω-Semiprecategory =
    composition-1-cell-globular-type-Globular-Type
      composition-Noncoherent-ω-Semiprecategory
```

The noncoherent ω-semiprecategory of morphisms between two objects in a
noncoherent ω-semiprecategory:

```agda
  hom-noncoherent-ω-semiprecategory-Noncoherent-ω-Semiprecategory :
    (x y : obj-Noncoherent-ω-Semiprecategory) →
    Noncoherent-ω-Semiprecategory l2 l2
  hom-noncoherent-ω-semiprecategory-Noncoherent-ω-Semiprecategory x y =
    hom-globular-type-Noncoherent-ω-Semiprecategory x y ,
    composition-hom-Noncoherent-ω-Semiprecategory
```

2-Morphisms in a noncoherent ω-semiprecategory:

```agda
  2-hom-globular-type-Noncoherent-ω-Semiprecategory :
    {x y : obj-Noncoherent-ω-Semiprecategory}
    (f g : hom-Noncoherent-ω-Semiprecategory x y) → Globular-Type l2 l2
  2-hom-globular-type-Noncoherent-ω-Semiprecategory =
    2-cell-globular-type-Globular-Type
      globular-type-Noncoherent-ω-Semiprecategory

  2-hom-Noncoherent-ω-Semiprecategory :
    {x y : obj-Noncoherent-ω-Semiprecategory}
    (f g : hom-Noncoherent-ω-Semiprecategory x y) → UU l2
  2-hom-Noncoherent-ω-Semiprecategory =
    2-cell-Globular-Type globular-type-Noncoherent-ω-Semiprecategory

  comp-2-hom-Noncoherent-ω-Semiprecategory :
    {x y : obj-Noncoherent-ω-Semiprecategory}
    {f g h : hom-Noncoherent-ω-Semiprecategory x y} →
    2-hom-Noncoherent-ω-Semiprecategory g h →
    2-hom-Noncoherent-ω-Semiprecategory f g →
    2-hom-Noncoherent-ω-Semiprecategory f h
  comp-2-hom-Noncoherent-ω-Semiprecategory =
    comp-2-cell-composition-Globular-Type
      composition-Noncoherent-ω-Semiprecategory

  composition-2-hom-Noncoherent-ω-Semiprecategory :
    {x y : obj-Noncoherent-ω-Semiprecategory}
    {f g : hom-Noncoherent-ω-Semiprecategory x y} →
    composition-Globular-Type
      ( 2-hom-globular-type-Noncoherent-ω-Semiprecategory f g)
  composition-2-hom-Noncoherent-ω-Semiprecategory =
    composition-1-cell-globular-type-Globular-Type
      composition-hom-Noncoherent-ω-Semiprecategory

  2-hom-noncoherent-ω-semiprecategory-Noncoherent-ω-Semiprecategory :
    {x y : obj-Noncoherent-ω-Semiprecategory}
    (f g : hom-Noncoherent-ω-Semiprecategory x y) →
    Noncoherent-ω-Semiprecategory l2 l2
  2-hom-noncoherent-ω-semiprecategory-Noncoherent-ω-Semiprecategory f g =
    2-hom-globular-type-Noncoherent-ω-Semiprecategory f g ,
    composition-2-hom-Noncoherent-ω-Semiprecategory

  horizontal-comp-2-hom-Noncoherent-ω-Semiprecategory :
    {x y z : obj-Noncoherent-ω-Semiprecategory} →
    {g g' : hom-Noncoherent-ω-Semiprecategory y z}
    {f f' : hom-Noncoherent-ω-Semiprecategory x y} →
    2-hom-Noncoherent-ω-Semiprecategory g g' →
    2-hom-Noncoherent-ω-Semiprecategory f f' →
    2-hom-Noncoherent-ω-Semiprecategory
      ( comp-hom-Noncoherent-ω-Semiprecategory g f)
      ( comp-hom-Noncoherent-ω-Semiprecategory g' f')
  horizontal-comp-2-hom-Noncoherent-ω-Semiprecategory =
    horizontal-comp-2-cell-composition-Globular-Type
      composition-Noncoherent-ω-Semiprecategory
```

Higher morphisms in a noncoherent ω-semiprecategory:

```agda
  3-hom-globular-type-Noncoherent-ω-Semiprecategory :
    {x y : obj-Noncoherent-ω-Semiprecategory}
    {f g : hom-Noncoherent-ω-Semiprecategory x y}
    (α β : 2-hom-Noncoherent-ω-Semiprecategory f g) → Globular-Type l2 l2
  3-hom-globular-type-Noncoherent-ω-Semiprecategory =
    3-cell-globular-type-Globular-Type
      globular-type-Noncoherent-ω-Semiprecategory

  3-hom-Noncoherent-ω-Semiprecategory :
    {x y : obj-Noncoherent-ω-Semiprecategory}
    {f g : hom-Noncoherent-ω-Semiprecategory x y}
    (α β : 2-hom-Noncoherent-ω-Semiprecategory f g) → UU l2
  3-hom-Noncoherent-ω-Semiprecategory =
    3-cell-Globular-Type globular-type-Noncoherent-ω-Semiprecategory

  comp-3-hom-Noncoherent-ω-Semiprecategory :
    {x y : obj-Noncoherent-ω-Semiprecategory}
    {f g : hom-Noncoherent-ω-Semiprecategory x y}
    {α β γ : 2-hom-Noncoherent-ω-Semiprecategory f g} →
    3-hom-Noncoherent-ω-Semiprecategory β γ →
    3-hom-Noncoherent-ω-Semiprecategory α β →
    3-hom-Noncoherent-ω-Semiprecategory α γ
  comp-3-hom-Noncoherent-ω-Semiprecategory =
    comp-3-cell-composition-Globular-Type
      composition-Noncoherent-ω-Semiprecategory

  horizontal-comp-3-hom-Noncoherent-ω-Semiprecategory :
    {x y z : obj-Noncoherent-ω-Semiprecategory}
    {g g' : hom-Noncoherent-ω-Semiprecategory y z}
    {f f' : hom-Noncoherent-ω-Semiprecategory x y}
    {α α' : 2-hom-Noncoherent-ω-Semiprecategory g g'}
    {β β' : 2-hom-Noncoherent-ω-Semiprecategory f f'} →
    3-hom-Noncoherent-ω-Semiprecategory α α' →
    3-hom-Noncoherent-ω-Semiprecategory β β' →
    3-hom-Noncoherent-ω-Semiprecategory
      ( horizontal-comp-2-hom-Noncoherent-ω-Semiprecategory α β)
      ( horizontal-comp-2-hom-Noncoherent-ω-Semiprecategory α' β')
  horizontal-comp-3-hom-Noncoherent-ω-Semiprecategory =
    horizontal-comp-3-cell-composition-Globular-Type'
      composition-Noncoherent-ω-Semiprecategory

  4-hom-globular-type-Noncoherent-ω-Semiprecategory :
    {x y : obj-Noncoherent-ω-Semiprecategory}
    {f g : hom-Noncoherent-ω-Semiprecategory x y}
    {α β : 2-hom-Noncoherent-ω-Semiprecategory f g}
    (H K : 3-hom-Noncoherent-ω-Semiprecategory α β) → Globular-Type l2 l2
  4-hom-globular-type-Noncoherent-ω-Semiprecategory =
    4-cell-globular-type-Globular-Type
      globular-type-Noncoherent-ω-Semiprecategory

  4-hom-Noncoherent-ω-Semiprecategory :
    {x y : obj-Noncoherent-ω-Semiprecategory}
    {f g : hom-Noncoherent-ω-Semiprecategory x y}
    {α β : 2-hom-Noncoherent-ω-Semiprecategory f g}
    (H K : 3-hom-Noncoherent-ω-Semiprecategory α β) → UU l2
  4-hom-Noncoherent-ω-Semiprecategory =
    4-cell-Globular-Type globular-type-Noncoherent-ω-Semiprecategory
```
