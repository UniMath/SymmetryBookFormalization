# Full ideals of rings

```agda
module ring-theory.full-ideals-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.full-subtypes
open import foundation.propositions
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import order-theory.top-elements-large-posets

open import ring-theory.ideals-rings
open import ring-theory.left-ideals-rings
open import ring-theory.poset-of-ideals-rings
open import ring-theory.right-ideals-rings
open import ring-theory.rings
open import ring-theory.subsets-rings
```

</details>

## Idea

A **full ideal** in a [ring](ring-theory.rings.md) `R` is an
[ideal](ring-theory.ideals-rings.md) that contains every element of `R`.

## Definitions

### The predicate of being a full ideal

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  where

  is-full-ideal-Ring-Prop : Prop (l1 ⊔ l2)
  is-full-ideal-Ring-Prop =
    Π-Prop (type-Ring R) (λ x → subset-ideal-Ring R I x)

  is-full-ideal-Ring : UU (l1 ⊔ l2)
  is-full-ideal-Ring = type-Prop is-full-ideal-Ring-Prop

  is-prop-is-full-ideal-Ring : is-prop is-full-ideal-Ring
  is-prop-is-full-ideal-Ring =
    is-prop-type-Prop is-full-ideal-Ring-Prop
```

### The (standard) full ideal

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  subset-full-ideal-Ring : subset-Ring lzero R
  subset-full-ideal-Ring = full-subtype lzero (type-Ring R)

  is-in-full-ideal-Ring : type-Ring R → UU lzero
  is-in-full-ideal-Ring = is-in-subtype subset-full-ideal-Ring

  contains-zero-full-ideal-Ring :
    contains-zero-subset-Ring R subset-full-ideal-Ring
  contains-zero-full-ideal-Ring = raise-star

  is-closed-under-addition-full-ideal-Ring :
    is-closed-under-addition-subset-Ring R subset-full-ideal-Ring
  is-closed-under-addition-full-ideal-Ring H K = raise-star

  is-closed-under-negatives-full-ideal-Ring :
    is-closed-under-negatives-subset-Ring R subset-full-ideal-Ring
  is-closed-under-negatives-full-ideal-Ring H = raise-star

  is-additive-subgroup-full-ideal-Ring :
    is-additive-subgroup-subset-Ring R subset-full-ideal-Ring
  pr1 is-additive-subgroup-full-ideal-Ring =
    contains-zero-full-ideal-Ring
  pr1 (pr2 is-additive-subgroup-full-ideal-Ring) {x} {y} =
    is-closed-under-addition-full-ideal-Ring {x} {y}
  pr2 (pr2 is-additive-subgroup-full-ideal-Ring) {x} =
    is-closed-under-negatives-full-ideal-Ring {x}

  is-closed-under-left-multiplication-full-ideal-Ring :
    is-closed-under-left-multiplication-subset-Ring R subset-full-ideal-Ring
  is-closed-under-left-multiplication-full-ideal-Ring x y H = raise-star

  is-closed-under-right-multiplication-full-ideal-Ring :
    is-closed-under-right-multiplication-subset-Ring R subset-full-ideal-Ring
  is-closed-under-right-multiplication-full-ideal-Ring x y H = raise-star

  is-left-ideal-full-ideal-Ring :
    is-left-ideal-subset-Ring R subset-full-ideal-Ring
  pr1 (pr1 is-left-ideal-full-ideal-Ring) =
    contains-zero-full-ideal-Ring
  pr2 (pr1 is-left-ideal-full-ideal-Ring) {x} {y} =
    is-closed-under-addition-full-ideal-Ring {x} {y}
  pr2 is-left-ideal-full-ideal-Ring =
    is-closed-under-left-multiplication-full-ideal-Ring

  full-left-ideal-Ring : left-ideal-Ring lzero R
  pr1 full-left-ideal-Ring = subset-full-ideal-Ring
  pr2 full-left-ideal-Ring = is-left-ideal-full-ideal-Ring

  is-right-ideal-full-ideal-Ring :
    is-right-ideal-subset-Ring R subset-full-ideal-Ring
  pr1 is-right-ideal-full-ideal-Ring =
    is-additive-subgroup-full-ideal-Ring
  pr2 is-right-ideal-full-ideal-Ring =
    is-closed-under-right-multiplication-full-ideal-Ring

  full-right-ideal-Ring : right-ideal-Ring lzero R
  pr1 full-right-ideal-Ring = subset-full-ideal-Ring
  pr2 full-right-ideal-Ring = is-right-ideal-full-ideal-Ring

  is-ideal-full-ideal-Ring : is-ideal-subset-Ring R subset-full-ideal-Ring
  pr1 is-ideal-full-ideal-Ring =
    is-additive-subgroup-full-ideal-Ring
  pr1 (pr2 is-ideal-full-ideal-Ring) =
    is-closed-under-left-multiplication-full-ideal-Ring
  pr2 (pr2 is-ideal-full-ideal-Ring) =
    is-closed-under-right-multiplication-full-ideal-Ring

  full-ideal-Ring : ideal-Ring lzero R
  pr1 full-ideal-Ring = subset-full-ideal-Ring
  pr2 full-ideal-Ring = is-ideal-full-ideal-Ring

  is-full-full-ideal-Ring : is-full-ideal-Ring R full-ideal-Ring
  is-full-full-ideal-Ring x = raise-star
```

## Properties

### Any ideal is full if and only if it contains `1`

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  where

  is-full-contains-one-ideal-Ring :
    is-in-ideal-Ring R I (one-Ring R) → is-full-ideal-Ring R I
  is-full-contains-one-ideal-Ring H x =
    is-closed-under-eq-ideal-Ring R I
      ( is-closed-under-left-multiplication-ideal-Ring R I x (one-Ring R) H)
      ( right-unit-law-mul-Ring R x)

  contains-one-is-full-ideal-Ring :
    is-full-ideal-Ring R I → is-in-ideal-Ring R I (one-Ring R)
  contains-one-is-full-ideal-Ring H = H (one-Ring R)
```

### Any ideal is full if and only if it is a top element in the large poset of ideals

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  where

  is-full-is-top-element-ideal-Ring :
    is-top-element-Large-Poset (ideal-Ring-Large-Poset R) I →
    is-full-ideal-Ring R I
  is-full-is-top-element-ideal-Ring H x =
    H (full-ideal-Ring R) x (is-full-full-ideal-Ring R x)

  is-top-element-is-full-ideal-Ring :
    is-full-ideal-Ring R I →
    is-top-element-Large-Poset (ideal-Ring-Large-Poset R) I
  is-top-element-is-full-ideal-Ring H I x K = H x

module _
  {l1 : Level} (R : Ring l1)
  where

  is-top-element-full-ideal-Ring :
    is-top-element-Large-Poset (ideal-Ring-Large-Poset R) (full-ideal-Ring R)
  is-top-element-full-ideal-Ring =
    is-top-element-is-full-ideal-Ring R
      ( full-ideal-Ring R)
      ( is-full-full-ideal-Ring R)

  has-top-element-ideal-Ring :
    has-top-element-Large-Poset (ideal-Ring-Large-Poset R)
  top-has-top-element-Large-Poset
    has-top-element-ideal-Ring =
    full-ideal-Ring R
  is-top-element-top-has-top-element-Large-Poset
    has-top-element-ideal-Ring =
    is-top-element-full-ideal-Ring
```
