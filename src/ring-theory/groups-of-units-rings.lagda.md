# The group of multiplicative units of a ring

```agda
module ring-theory.groups-of-units-rings where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.cores-monoids
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-monoids
open import group-theory.monoids
open import group-theory.precategory-of-groups
open import group-theory.semigroups
open import group-theory.submonoids

open import ring-theory.homomorphisms-rings
open import ring-theory.invertible-elements-rings
open import ring-theory.precategory-of-rings
open import ring-theory.rings
```

</details>

## Idea

The {{#concept "group of units" Disambiguation="ring" WD="unit" WDID=Q118084}}
of a [ring](ring-theory.rings.md) `R` is the [group](group-theory.groups.md)
consisting of all the
[invertible elements](ring-theory.invertible-elements-rings.md) in `R`.
Equivalently, the group of units of `R` is the
[core](group-theory.cores-monoids.md) of the multiplicative
[monoid](group-theory.monoids.md) of `R`.

## Definitions

### The group of units of a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  subtype-group-of-units-Ring : type-Ring R → Prop l
  subtype-group-of-units-Ring = is-invertible-element-prop-Ring R

  submonoid-group-of-units-Ring : Submonoid l (multiplicative-monoid-Ring R)
  submonoid-group-of-units-Ring =
    submonoid-core-Monoid (multiplicative-monoid-Ring R)

  monoid-group-of-units-Ring : Monoid l
  monoid-group-of-units-Ring =
    monoid-core-Monoid (multiplicative-monoid-Ring R)

  semigroup-group-of-units-Ring : Semigroup l
  semigroup-group-of-units-Ring =
    semigroup-core-Monoid (multiplicative-monoid-Ring R)

  type-group-of-units-Ring : UU l
  type-group-of-units-Ring =
    type-core-Monoid (multiplicative-monoid-Ring R)

  mul-group-of-units-Ring :
    (x y : type-group-of-units-Ring) → type-group-of-units-Ring
  mul-group-of-units-Ring =
    mul-core-Monoid (multiplicative-monoid-Ring R)

  associative-mul-group-of-units-Ring :
    (x y z : type-group-of-units-Ring) →
    mul-group-of-units-Ring (mul-group-of-units-Ring x y) z ＝
    mul-group-of-units-Ring x (mul-group-of-units-Ring y z)
  associative-mul-group-of-units-Ring =
    associative-mul-core-Monoid (multiplicative-monoid-Ring R)

  unit-group-of-units-Ring : type-group-of-units-Ring
  unit-group-of-units-Ring =
    unit-core-Monoid (multiplicative-monoid-Ring R)

  left-unit-law-mul-group-of-units-Ring :
    (x : type-group-of-units-Ring) →
    mul-group-of-units-Ring unit-group-of-units-Ring x ＝ x
  left-unit-law-mul-group-of-units-Ring =
    left-unit-law-mul-core-Monoid (multiplicative-monoid-Ring R)

  right-unit-law-mul-group-of-units-Ring :
    (x : type-group-of-units-Ring) →
    mul-group-of-units-Ring x unit-group-of-units-Ring ＝ x
  right-unit-law-mul-group-of-units-Ring =
    right-unit-law-mul-core-Monoid (multiplicative-monoid-Ring R)

  is-unital-group-of-units-Ring :
    is-unital-Semigroup semigroup-group-of-units-Ring
  is-unital-group-of-units-Ring =
    is-unital-core-Monoid (multiplicative-monoid-Ring R)

  inv-group-of-units-Ring : type-group-of-units-Ring → type-group-of-units-Ring
  inv-group-of-units-Ring =
    inv-core-Monoid (multiplicative-monoid-Ring R)

  left-inverse-law-mul-group-of-units-Ring :
    (x : type-group-of-units-Ring) →
    mul-group-of-units-Ring (inv-group-of-units-Ring x) x ＝
    unit-group-of-units-Ring
  left-inverse-law-mul-group-of-units-Ring =
    left-inverse-law-mul-core-Monoid (multiplicative-monoid-Ring R)

  right-inverse-law-mul-group-of-units-Ring :
    (x : type-group-of-units-Ring) →
    mul-group-of-units-Ring x (inv-group-of-units-Ring x) ＝
    unit-group-of-units-Ring
  right-inverse-law-mul-group-of-units-Ring =
    right-inverse-law-mul-core-Monoid (multiplicative-monoid-Ring R)

  is-group-group-of-units-Ring' :
    is-group-is-unital-Semigroup
      ( semigroup-group-of-units-Ring)
      ( is-unital-group-of-units-Ring)
  is-group-group-of-units-Ring' =
    is-group-core-Monoid' (multiplicative-monoid-Ring R)

  is-group-group-of-units-Ring :
    is-group-Semigroup semigroup-group-of-units-Ring
  is-group-group-of-units-Ring =
    is-group-core-Monoid (multiplicative-monoid-Ring R)

  group-of-units-Ring : Group l
  group-of-units-Ring = core-Monoid (multiplicative-monoid-Ring R)

  inclusion-group-of-units-Ring :
    type-group-of-units-Ring → type-Ring R
  inclusion-group-of-units-Ring =
    inclusion-core-Monoid (multiplicative-monoid-Ring R)

  is-invertible-element-inclusion-group-of-units-Ring :
    (x : type-group-of-units-Ring) →
    is-invertible-element-Ring R
      ( inclusion-group-of-units-Ring x)
  is-invertible-element-inclusion-group-of-units-Ring =
    is-in-subtype-inclusion-subtype subtype-group-of-units-Ring

  preserves-mul-inclusion-group-of-units-Ring :
    {x y : type-group-of-units-Ring} →
    inclusion-group-of-units-Ring (mul-group-of-units-Ring x y) ＝
    mul-Ring R
      ( inclusion-group-of-units-Ring x)
      ( inclusion-group-of-units-Ring y)
  preserves-mul-inclusion-group-of-units-Ring {x} {y} =
    preserves-mul-inclusion-core-Monoid (multiplicative-monoid-Ring R) {x} {y}

  hom-inclusion-group-of-units-Ring :
    hom-Monoid monoid-group-of-units-Ring (multiplicative-monoid-Ring R)
  hom-inclusion-group-of-units-Ring =
    hom-inclusion-core-Monoid (multiplicative-monoid-Ring R)
```

## Properties

### The group of units of a ring is a functor from rings to groups

#### The functorial action of `group-of-units-Ring`

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (f : hom-Ring R S)
  where

  map-group-of-units-hom-Ring :
    type-group-of-units-Ring R → type-group-of-units-Ring S
  map-group-of-units-hom-Ring =
    map-core-hom-Monoid
      ( multiplicative-monoid-Ring R)
      ( multiplicative-monoid-Ring S)
      ( hom-multiplicative-monoid-hom-Ring R S f)

  preserves-mul-hom-group-of-units-hom-Ring :
    {x y : type-group-of-units-Ring R} →
    map-group-of-units-hom-Ring (mul-group-of-units-Ring R x y) ＝
    mul-group-of-units-Ring S
      ( map-group-of-units-hom-Ring x)
      ( map-group-of-units-hom-Ring y)
  preserves-mul-hom-group-of-units-hom-Ring =
    preserves-mul-hom-core-hom-Monoid
      ( multiplicative-monoid-Ring R)
      ( multiplicative-monoid-Ring S)
      ( hom-multiplicative-monoid-hom-Ring R S f)

  hom-group-of-units-hom-Ring :
    hom-Group (group-of-units-Ring R) (group-of-units-Ring S)
  hom-group-of-units-hom-Ring =
    hom-core-hom-Monoid
      ( multiplicative-monoid-Ring R)
      ( multiplicative-monoid-Ring S)
      ( hom-multiplicative-monoid-hom-Ring R S f)

  preserves-unit-hom-group-of-units-hom-Ring :
    map-group-of-units-hom-Ring (unit-group-of-units-Ring R) ＝
    unit-group-of-units-Ring S
  preserves-unit-hom-group-of-units-hom-Ring =
    preserves-unit-hom-core-hom-Monoid
      ( multiplicative-monoid-Ring R)
      ( multiplicative-monoid-Ring S)
      ( hom-multiplicative-monoid-hom-Ring R S f)

  preserves-inv-hom-group-of-units-hom-Ring :
    {x : type-group-of-units-Ring R} →
    map-group-of-units-hom-Ring (inv-group-of-units-Ring R x) ＝
    inv-group-of-units-Ring S (map-group-of-units-hom-Ring x)
  preserves-inv-hom-group-of-units-hom-Ring =
    preserves-inv-hom-core-hom-Monoid
      ( multiplicative-monoid-Ring R)
      ( multiplicative-monoid-Ring S)
      ( hom-multiplicative-monoid-hom-Ring R S f)
```

#### The functorial laws of the group-of-units functor

```agda
module _
  {l : Level} (R : Ring l)
  where

  preserves-id-hom-group-of-units-hom-Ring :
    hom-group-of-units-hom-Ring R R (id-hom-Ring R) ＝
    id-hom-Group (group-of-units-Ring R)
  preserves-id-hom-group-of-units-hom-Ring =
    preserves-id-hom-core-hom-Monoid (multiplicative-monoid-Ring R)

module _
  {l1 l2 l3 : Level} (R : Ring l1) (S : Ring l2) (T : Ring l3)
  where

  preserves-comp-hom-group-of-units-hom-Ring :
    (g : hom-Ring S T) (f : hom-Ring R S) →
    hom-group-of-units-hom-Ring R T (comp-hom-Ring R S T g f) ＝
    comp-hom-Group
      ( group-of-units-Ring R)
      ( group-of-units-Ring S)
      ( group-of-units-Ring T)
      ( hom-group-of-units-hom-Ring S T g)
      ( hom-group-of-units-hom-Ring R S f)
  preserves-comp-hom-group-of-units-hom-Ring g f =
    preserves-comp-hom-core-hom-Monoid
      ( multiplicative-monoid-Ring R)
      ( multiplicative-monoid-Ring S)
      ( multiplicative-monoid-Ring T)
      ( hom-multiplicative-monoid-hom-Ring S T g)
      ( hom-multiplicative-monoid-hom-Ring R S f)
```

#### The group-of-units functor

```agda
group-of-units-ring-functor-Large-Precategory :
  functor-Large-Precategory
    ( λ l → l)
    ( Ring-Large-Precategory)
    ( Group-Large-Precategory)
obj-functor-Large-Precategory
  group-of-units-ring-functor-Large-Precategory =
  group-of-units-Ring
hom-functor-Large-Precategory
  group-of-units-ring-functor-Large-Precategory {X = R} {Y = S} =
  hom-group-of-units-hom-Ring R S
preserves-comp-functor-Large-Precategory
  group-of-units-ring-functor-Large-Precategory {X = R} {Y = S} {Z = T} =
  preserves-comp-hom-group-of-units-hom-Ring R S T
preserves-id-functor-Large-Precategory
  group-of-units-ring-functor-Large-Precategory {X = R} =
  preserves-id-hom-group-of-units-hom-Ring R
```

### Negatives of units

```agda
module _
  {l : Level} (R : Ring l)
  where

  neg-group-of-units-Ring :
    type-group-of-units-Ring R → type-group-of-units-Ring R
  pr1 (neg-group-of-units-Ring (x , H)) = neg-Ring R x
  pr2 (neg-group-of-units-Ring (x , H)) = is-invertible-element-neg-Ring R x H

  neg-unit-group-of-units-Ring :
    type-group-of-units-Ring R
  neg-unit-group-of-units-Ring =
    neg-group-of-units-Ring (unit-group-of-units-Ring R)
```
