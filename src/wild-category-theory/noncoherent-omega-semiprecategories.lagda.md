# Noncoherent ω-semiprecategories

```agda
{-# OPTIONS --guardedness #-}

module wild-category-theory.noncoherent-omega-semiprecategories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import globular-types.globular-types
open import globular-types.composition-structure-globular-types
open import foundation.universe-levels

```

</details>

## Idea

A
{{#concept "noncoherent ω-semiprecategory" Agda=Noncoherent-ω-Semiprecategory}}
`𝒞` is a [globular type](globular-types.globular-types.md) `G`
[equipped](foundation.structure.md) with a
[composition structure](globular-types.composition-structure-globular-types.md).

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
  hom-noncoherent-semiprecategory-Noncoherent-ω-Semiprecategory :
    (x y : obj-Noncoherent-ω-Semiprecategory) →
    Noncoherent-ω-Semiprecategory l2 l2
  hom-noncoherent-semiprecategory-Noncoherent-ω-Semiprecategory x y =
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

  2-hom-noncoherent-semiprecategory-Noncoherent-ω-Semiprecategory :
    {x y : obj-Noncoherent-ω-Semiprecategory}
    (f g : hom-Noncoherent-ω-Semiprecategory x y) →
    Noncoherent-ω-Semiprecategory l2 l2
  2-hom-noncoherent-semiprecategory-Noncoherent-ω-Semiprecategory f g =
    2-hom-globular-type-Noncoherent-ω-Semiprecategory f g ,
    composition-2-hom-Noncoherent-ω-Semiprecategory
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
