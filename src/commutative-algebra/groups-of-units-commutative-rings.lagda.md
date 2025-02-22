# The group of multiplicative units of a commutative ring

```agda
module commutative-algebra.groups-of-units-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategories

open import commutative-algebra.commutative-rings
open import commutative-algebra.homomorphisms-commutative-rings
open import commutative-algebra.invertible-elements-commutative-rings
open import commutative-algebra.precategory-of-commutative-rings

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.category-of-abelian-groups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-monoids
open import group-theory.monoids
open import group-theory.semigroups
open import group-theory.submonoids

open import ring-theory.groups-of-units-rings
```

</details>

## Idea

The
{{#concept "group of units" Disambiguation="commutative ring" WD="unit" WDID=Q118084}}
of a [commutative ring](commutative-algebra.commutative-rings.md) `A` is the
[abelian group](group-theory.abelian-groups.md) consisting of all the
[invertible elements](commutative-algebra.invertible-elements-commutative-rings.md)
in `A`. Equivalently, the group of units of `A` is the
[core](group-theory.cores-monoids.md) of the multiplicative
[monoid](group-theory.monoids.md) of `A`.

## Definitions

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  subtype-group-of-units-Commutative-Ring :
    type-Commutative-Ring A → Prop l
  subtype-group-of-units-Commutative-Ring =
    subtype-group-of-units-Ring (ring-Commutative-Ring A)

  submonoid-group-of-units-Commutative-Ring :
    Submonoid l (multiplicative-monoid-Commutative-Ring A)
  submonoid-group-of-units-Commutative-Ring =
    submonoid-group-of-units-Ring (ring-Commutative-Ring A)

  monoid-group-of-units-Commutative-Ring : Monoid l
  monoid-group-of-units-Commutative-Ring =
    monoid-group-of-units-Ring (ring-Commutative-Ring A)

  semigroup-group-of-units-Commutative-Ring : Semigroup l
  semigroup-group-of-units-Commutative-Ring =
    semigroup-group-of-units-Ring (ring-Commutative-Ring A)

  type-group-of-units-Commutative-Ring : UU l
  type-group-of-units-Commutative-Ring =
    type-group-of-units-Ring (ring-Commutative-Ring A)

  mul-group-of-units-Commutative-Ring :
    (x y : type-group-of-units-Commutative-Ring) →
    type-group-of-units-Commutative-Ring
  mul-group-of-units-Commutative-Ring =
    mul-group-of-units-Ring (ring-Commutative-Ring A)

  associative-mul-group-of-units-Commutative-Ring :
    (x y z : type-group-of-units-Commutative-Ring) →
    mul-group-of-units-Commutative-Ring
      ( mul-group-of-units-Commutative-Ring x y)
      ( z) ＝
    mul-group-of-units-Commutative-Ring x
      ( mul-group-of-units-Commutative-Ring y z)
  associative-mul-group-of-units-Commutative-Ring =
    associative-mul-group-of-units-Ring (ring-Commutative-Ring A)

  unit-group-of-units-Commutative-Ring :
    type-group-of-units-Commutative-Ring
  unit-group-of-units-Commutative-Ring =
    unit-group-of-units-Ring (ring-Commutative-Ring A)

  left-unit-law-mul-group-of-units-Commutative-Ring :
    (x : type-group-of-units-Commutative-Ring) →
    mul-group-of-units-Commutative-Ring
      ( unit-group-of-units-Commutative-Ring)
      ( x) ＝
    x
  left-unit-law-mul-group-of-units-Commutative-Ring =
    left-unit-law-mul-group-of-units-Ring (ring-Commutative-Ring A)

  right-unit-law-mul-group-of-units-Commutative-Ring :
    (x : type-group-of-units-Commutative-Ring) →
    mul-group-of-units-Commutative-Ring
      ( x)
      ( unit-group-of-units-Commutative-Ring) ＝
    x
  right-unit-law-mul-group-of-units-Commutative-Ring =
    right-unit-law-mul-group-of-units-Ring (ring-Commutative-Ring A)

  is-unital-group-of-units-Commutative-Ring :
    is-unital-Semigroup semigroup-group-of-units-Commutative-Ring
  is-unital-group-of-units-Commutative-Ring =
    is-unital-group-of-units-Ring (ring-Commutative-Ring A)

  inv-group-of-units-Commutative-Ring :
    type-group-of-units-Commutative-Ring →
    type-group-of-units-Commutative-Ring
  inv-group-of-units-Commutative-Ring =
    inv-group-of-units-Ring (ring-Commutative-Ring A)

  left-inverse-law-mul-group-of-units-Commutative-Ring :
    (x : type-group-of-units-Commutative-Ring) →
    mul-group-of-units-Commutative-Ring
      ( inv-group-of-units-Commutative-Ring x)
      ( x) ＝
    unit-group-of-units-Commutative-Ring
  left-inverse-law-mul-group-of-units-Commutative-Ring =
    left-inverse-law-mul-group-of-units-Ring (ring-Commutative-Ring A)

  right-inverse-law-mul-group-of-units-Commutative-Ring :
    (x : type-group-of-units-Commutative-Ring) →
    mul-group-of-units-Commutative-Ring
      ( x)
      ( inv-group-of-units-Commutative-Ring x) ＝
    unit-group-of-units-Commutative-Ring
  right-inverse-law-mul-group-of-units-Commutative-Ring =
    right-inverse-law-mul-group-of-units-Ring
      ( ring-Commutative-Ring A)

  commutative-mul-group-of-units-Commutative-Ring :
    (x y : type-group-of-units-Commutative-Ring) →
    mul-group-of-units-Commutative-Ring x y ＝
    mul-group-of-units-Commutative-Ring y x
  commutative-mul-group-of-units-Commutative-Ring x y =
    eq-type-subtype
      ( subtype-group-of-units-Commutative-Ring)
      ( commutative-mul-Commutative-Ring A (pr1 x) (pr1 y))

  is-group-group-of-units-Commutative-Ring' :
    is-group-is-unital-Semigroup
      ( semigroup-group-of-units-Commutative-Ring)
      ( is-unital-group-of-units-Commutative-Ring)
  is-group-group-of-units-Commutative-Ring' =
    is-group-group-of-units-Ring' (ring-Commutative-Ring A)

  is-group-group-of-units-Commutative-Ring :
    is-group-Semigroup semigroup-group-of-units-Commutative-Ring
  is-group-group-of-units-Commutative-Ring =
    is-group-group-of-units-Ring (ring-Commutative-Ring A)

  group-of-units-Commutative-Ring : Group l
  group-of-units-Commutative-Ring =
    group-of-units-Ring (ring-Commutative-Ring A)

  abelian-group-of-units-Commutative-Ring : Ab l
  pr1 abelian-group-of-units-Commutative-Ring =
    group-of-units-Commutative-Ring
  pr2 abelian-group-of-units-Commutative-Ring =
    commutative-mul-group-of-units-Commutative-Ring

  inclusion-group-of-units-Commutative-Ring :
    type-group-of-units-Commutative-Ring → type-Commutative-Ring A
  inclusion-group-of-units-Commutative-Ring =
    inclusion-group-of-units-Ring (ring-Commutative-Ring A)

  is-invertible-element-inclusion-group-of-units-Commutative-Ring :
    (x : type-group-of-units-Commutative-Ring) →
    is-invertible-element-Commutative-Ring A
      ( inclusion-group-of-units-Commutative-Ring x)
  is-invertible-element-inclusion-group-of-units-Commutative-Ring =
    is-invertible-element-inclusion-group-of-units-Ring
      ( ring-Commutative-Ring A)

  preserves-mul-inclusion-group-of-units-Commutative-Ring :
    {x y : type-group-of-units-Commutative-Ring} →
    inclusion-group-of-units-Commutative-Ring
      ( mul-group-of-units-Commutative-Ring x y) ＝
    mul-Commutative-Ring A
      ( inclusion-group-of-units-Commutative-Ring x)
      ( inclusion-group-of-units-Commutative-Ring y)
  preserves-mul-inclusion-group-of-units-Commutative-Ring {x} {y} =
    preserves-mul-inclusion-group-of-units-Ring
      ( ring-Commutative-Ring A)
      { x}
      { y}

  hom-inclusion-group-of-units-Commutative-Ring :
    hom-Monoid monoid-group-of-units-Commutative-Ring
      ( multiplicative-monoid-Commutative-Ring A)
  hom-inclusion-group-of-units-Commutative-Ring =
    hom-inclusion-group-of-units-Ring (ring-Commutative-Ring A)
```

## Properties

### The group of units of a commutative ring is a functor from commutative rings to abelian groups

#### The functorial action of `group-of-units-Commutative-Ring`

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (B : Commutative-Ring l2)
  (f : hom-Commutative-Ring A B)
  where

  map-group-of-units-hom-Commutative-Ring :
    type-group-of-units-Commutative-Ring A →
    type-group-of-units-Commutative-Ring B
  map-group-of-units-hom-Commutative-Ring =
    map-group-of-units-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( f)

  preserves-mul-hom-group-of-units-hom-Commutative-Ring :
    {x y : type-group-of-units-Commutative-Ring A} →
    map-group-of-units-hom-Commutative-Ring
      ( mul-group-of-units-Commutative-Ring A x y) ＝
    mul-group-of-units-Commutative-Ring B
      ( map-group-of-units-hom-Commutative-Ring x)
      ( map-group-of-units-hom-Commutative-Ring y)
  preserves-mul-hom-group-of-units-hom-Commutative-Ring =
    preserves-mul-hom-group-of-units-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( f)

  hom-group-of-units-hom-Commutative-Ring :
    hom-Group
      ( group-of-units-Commutative-Ring A)
      ( group-of-units-Commutative-Ring B)
  hom-group-of-units-hom-Commutative-Ring =
    hom-group-of-units-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( f)

  preserves-unit-hom-group-of-units-hom-Commutative-Ring :
    map-group-of-units-hom-Commutative-Ring
      ( unit-group-of-units-Commutative-Ring A) ＝
    unit-group-of-units-Commutative-Ring B
  preserves-unit-hom-group-of-units-hom-Commutative-Ring =
    preserves-unit-hom-group-of-units-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( f)

  preserves-inv-hom-group-of-units-hom-Commutative-Ring :
    {x : type-group-of-units-Commutative-Ring A} →
    map-group-of-units-hom-Commutative-Ring
      ( inv-group-of-units-Commutative-Ring A x) ＝
    inv-group-of-units-Commutative-Ring B
      ( map-group-of-units-hom-Commutative-Ring x)
  preserves-inv-hom-group-of-units-hom-Commutative-Ring =
    preserves-inv-hom-group-of-units-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( f)
```

#### The functorial laws of `group-of-units-Commutative-Ring`

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  preserves-id-hom-group-of-units-hom-Commutative-Ring :
    hom-group-of-units-hom-Commutative-Ring A A (id-hom-Commutative-Ring A) ＝
    id-hom-Group (group-of-units-Commutative-Ring A)
  preserves-id-hom-group-of-units-hom-Commutative-Ring =
    preserves-id-hom-group-of-units-hom-Ring (ring-Commutative-Ring A)

module _
  {l1 l2 l3 : Level}
  (A : Commutative-Ring l1) (B : Commutative-Ring l2) (C : Commutative-Ring l3)
  where

  preserves-comp-hom-group-of-units-hom-Commutative-Ring :
    (g : hom-Commutative-Ring B C) (f : hom-Commutative-Ring A B) →
    hom-group-of-units-hom-Commutative-Ring A C
      ( comp-hom-Commutative-Ring A B C g f) ＝
    comp-hom-Group
      ( group-of-units-Commutative-Ring A)
      ( group-of-units-Commutative-Ring B)
      ( group-of-units-Commutative-Ring C)
      ( hom-group-of-units-hom-Commutative-Ring B C g)
      ( hom-group-of-units-hom-Commutative-Ring A B f)
  preserves-comp-hom-group-of-units-hom-Commutative-Ring g f =
    preserves-comp-hom-group-of-units-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( ring-Commutative-Ring C)
      ( g)
      ( f)
```

#### The functor `group-of-units-Commutative-Ring`

```agda
group-of-units-commutative-ring-functor-Large-Precategory :
  functor-Large-Precategory (λ l → l)
    ( Commutative-Ring-Large-Precategory)
    ( Ab-Large-Precategory)
obj-functor-Large-Precategory
  group-of-units-commutative-ring-functor-Large-Precategory =
  abelian-group-of-units-Commutative-Ring
hom-functor-Large-Precategory
  group-of-units-commutative-ring-functor-Large-Precategory {X = A} {Y = B} =
  hom-group-of-units-hom-Commutative-Ring A B
preserves-comp-functor-Large-Precategory
  group-of-units-commutative-ring-functor-Large-Precategory
  {X = A}
  {Y = B}
  {Z = C} =
  preserves-comp-hom-group-of-units-hom-Commutative-Ring A B C
preserves-id-functor-Large-Precategory
  group-of-units-commutative-ring-functor-Large-Precategory {X = A} =
  preserves-id-hom-group-of-units-hom-Commutative-Ring A
```

### Negatives of units

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  neg-group-of-units-Commutative-Ring :
    type-group-of-units-Commutative-Ring A →
    type-group-of-units-Commutative-Ring A
  neg-group-of-units-Commutative-Ring =
    neg-group-of-units-Ring (ring-Commutative-Ring A)

  neg-unit-group-of-units-Commutative-Ring :
    type-group-of-units-Commutative-Ring A
  neg-unit-group-of-units-Commutative-Ring =
    neg-unit-group-of-units-Ring (ring-Commutative-Ring A)
```
