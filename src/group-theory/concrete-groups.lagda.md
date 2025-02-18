# Concrete groups

```agda
module group-theory.concrete-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.1-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.monoids
open import group-theory.opposite-groups
open import group-theory.opposite-semigroups
open import group-theory.semigroups

open import higher-group-theory.higher-groups

open import structured-types.pointed-types
```

</details>

## Idea

A {{#concept "concrete group" WD="group" WDID=Q83478 Agda=Concrete-Group}} is a
[pointed](structured-types.pointed-types.md)
[connected](foundation.0-connected-types.md)
[1-type](foundation-core.1-types.md).

## Definitions

### Concrete groups

```agda
Concrete-Group : (l : Level) → UU (lsuc l)
Concrete-Group l = Σ (∞-Group l) (λ G → is-set (type-∞-Group G))

module _
  {l : Level} (G : Concrete-Group l)
  where

  ∞-group-Concrete-Group : ∞-Group l
  ∞-group-Concrete-Group = pr1 G

  classifying-pointed-type-Concrete-Group : Pointed-Type l
  classifying-pointed-type-Concrete-Group =
    classifying-pointed-type-∞-Group ∞-group-Concrete-Group

  classifying-type-Concrete-Group : UU l
  classifying-type-Concrete-Group =
    classifying-type-∞-Group ∞-group-Concrete-Group

  shape-Concrete-Group : classifying-type-Concrete-Group
  shape-Concrete-Group =
    shape-∞-Group ∞-group-Concrete-Group

  is-0-connected-classifying-type-Concrete-Group :
    is-0-connected classifying-type-Concrete-Group
  is-0-connected-classifying-type-Concrete-Group =
    is-0-connected-classifying-type-∞-Group ∞-group-Concrete-Group

  mere-eq-classifying-type-Concrete-Group :
    (X Y : classifying-type-Concrete-Group) → mere-eq X Y
  mere-eq-classifying-type-Concrete-Group =
    mere-eq-classifying-type-∞-Group ∞-group-Concrete-Group

  elim-prop-classifying-type-Concrete-Group :
    {l2 : Level} (P : classifying-type-Concrete-Group → Prop l2) →
    type-Prop (P shape-Concrete-Group) →
    ((X : classifying-type-Concrete-Group) → type-Prop (P X))
  elim-prop-classifying-type-Concrete-Group =
    elim-prop-classifying-type-∞-Group ∞-group-Concrete-Group

  type-Concrete-Group : UU l
  type-Concrete-Group = type-∞-Group ∞-group-Concrete-Group

  is-set-type-Concrete-Group : is-set type-Concrete-Group
  is-set-type-Concrete-Group = pr2 G

  set-Concrete-Group : Set l
  pr1 set-Concrete-Group = type-Concrete-Group
  pr2 set-Concrete-Group = is-set-type-Concrete-Group

  abstract
    is-1-type-classifying-type-Concrete-Group :
      is-trunc one-𝕋 classifying-type-Concrete-Group
    is-1-type-classifying-type-Concrete-Group X Y =
      apply-universal-property-trunc-Prop
        ( mere-eq-classifying-type-Concrete-Group shape-Concrete-Group X)
        ( is-set-Prop (X ＝ Y))
        ( λ where
          refl →
            apply-universal-property-trunc-Prop
              ( mere-eq-classifying-type-Concrete-Group shape-Concrete-Group Y)
              ( is-set-Prop (shape-Concrete-Group ＝ Y))
              ( λ where refl → is-set-type-Concrete-Group))

  classifying-1-type-Concrete-Group : Truncated-Type l one-𝕋
  pr1 classifying-1-type-Concrete-Group = classifying-type-Concrete-Group
  pr2 classifying-1-type-Concrete-Group =
    is-1-type-classifying-type-Concrete-Group

  Id-BG-Set :
    (X Y : classifying-type-Concrete-Group) → Set l
  Id-BG-Set X Y = Id-Set classifying-1-type-Concrete-Group X Y
```

### The abstract group associated to a concrete group

```agda
module _
  {l : Level} (G : Concrete-Group l)
  where

  unit-Concrete-Group : type-Concrete-Group G
  unit-Concrete-Group = unit-∞-Group (∞-group-Concrete-Group G)

  mul-Concrete-Group : (x y : type-Concrete-Group G) → type-Concrete-Group G
  mul-Concrete-Group = mul-∞-Group (∞-group-Concrete-Group G)

  mul-Concrete-Group' : (x y : type-Concrete-Group G) → type-Concrete-Group G
  mul-Concrete-Group' x y = mul-Concrete-Group y x

  associative-mul-Concrete-Group :
    (x y z : type-Concrete-Group G) →
    ( mul-Concrete-Group (mul-Concrete-Group x y) z) ＝
    ( mul-Concrete-Group x (mul-Concrete-Group y z))
  associative-mul-Concrete-Group =
    associative-mul-∞-Group (∞-group-Concrete-Group G)

  left-unit-law-mul-Concrete-Group :
    (x : type-Concrete-Group G) → mul-Concrete-Group unit-Concrete-Group x ＝ x
  left-unit-law-mul-Concrete-Group =
    left-unit-law-mul-∞-Group (∞-group-Concrete-Group G)

  right-unit-law-mul-Concrete-Group :
    (y : type-Concrete-Group G) → mul-Concrete-Group y unit-Concrete-Group ＝ y
  right-unit-law-mul-Concrete-Group =
    right-unit-law-mul-∞-Group (∞-group-Concrete-Group G)

  coherence-unit-laws-mul-Concrete-Group :
    left-unit-law-mul-Concrete-Group unit-Concrete-Group ＝
    right-unit-law-mul-Concrete-Group unit-Concrete-Group
  coherence-unit-laws-mul-Concrete-Group =
    coherence-unit-laws-mul-∞-Group (∞-group-Concrete-Group G)

  inv-Concrete-Group : type-Concrete-Group G → type-Concrete-Group G
  inv-Concrete-Group = inv-∞-Group (∞-group-Concrete-Group G)

  left-inverse-law-mul-Concrete-Group :
    (x : type-Concrete-Group G) →
    mul-Concrete-Group (inv-Concrete-Group x) x ＝ unit-Concrete-Group
  left-inverse-law-mul-Concrete-Group =
    left-inverse-law-mul-∞-Group (∞-group-Concrete-Group G)

  right-inverse-law-mul-Concrete-Group :
    (x : type-Concrete-Group G) →
    mul-Concrete-Group x (inv-Concrete-Group x) ＝ unit-Concrete-Group
  right-inverse-law-mul-Concrete-Group =
    right-inverse-law-mul-∞-Group (∞-group-Concrete-Group G)

  has-associative-mul-Concrete-Group :
    has-associative-mul-Set (set-Concrete-Group G)
  pr1 has-associative-mul-Concrete-Group = mul-Concrete-Group
  pr2 has-associative-mul-Concrete-Group = associative-mul-Concrete-Group

  semigroup-Concrete-Group : Semigroup l
  pr1 semigroup-Concrete-Group = set-Concrete-Group G
  pr2 semigroup-Concrete-Group = has-associative-mul-Concrete-Group

  is-unital-Concrete-Group : is-unital-Semigroup semigroup-Concrete-Group
  pr1 is-unital-Concrete-Group = unit-Concrete-Group
  pr1 (pr2 is-unital-Concrete-Group) = left-unit-law-mul-Concrete-Group
  pr2 (pr2 is-unital-Concrete-Group) = right-unit-law-mul-Concrete-Group

  monoid-Concrete-Group : Monoid l
  pr1 monoid-Concrete-Group = semigroup-Concrete-Group
  pr2 monoid-Concrete-Group = is-unital-Concrete-Group

  is-group-Concrete-Group' :
    is-group-is-unital-Semigroup
      ( semigroup-Concrete-Group)
      ( is-unital-Concrete-Group)
  pr1 is-group-Concrete-Group' = inv-Concrete-Group
  pr1 (pr2 is-group-Concrete-Group') = left-inverse-law-mul-Concrete-Group
  pr2 (pr2 is-group-Concrete-Group') = right-inverse-law-mul-Concrete-Group

  is-group-Concrete-Group : is-group-Semigroup semigroup-Concrete-Group
  pr1 is-group-Concrete-Group = is-unital-Concrete-Group
  pr2 is-group-Concrete-Group = is-group-Concrete-Group'

  group-Concrete-Group : Group l
  pr1 group-Concrete-Group = semigroup-Concrete-Group
  pr2 group-Concrete-Group = is-group-Concrete-Group

  monoid-Concrete-Group : Monoid l
  monoid-Concrete-Group = monoid-Group group-Concrete-Group
```

### The opposite abstract group associated to a concrete group

```agda
module _
  {l : Level} (G : Concrete-Group l)
  where

  op-semigroup-Concrete-Group : Semigroup l
  op-semigroup-Concrete-Group = op-Semigroup (semigroup-Concrete-Group G)

  is-unital-op-semigroup-Concrete-Group :
    is-unital-Semigroup op-semigroup-Concrete-Group
  is-unital-op-semigroup-Concrete-Group =
    is-unital-op-Group (group-Concrete-Group G)

  is-group-op-Concrete-Group : is-group-Semigroup op-semigroup-Concrete-Group
  is-group-op-Concrete-Group = is-group-op-Group (group-Concrete-Group G)

  op-group-Concrete-Group : Group l
  op-group-Concrete-Group = op-Group (group-Concrete-Group G)
```
