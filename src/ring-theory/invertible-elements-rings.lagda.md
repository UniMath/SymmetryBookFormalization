# Invertible elements in rings

```agda
module ring-theory.invertible-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.invertible-elements-monoids

open import ring-theory.rings
```

</details>

## Idea

**Invertible elements** in a [ring](ring-theory.rings.md) are elements that have
a two-sided multiplicative inverse. Such elements are also called the
**(multiplicative) units** of the ring.

The [set](foundation.sets.md) of units of any ring forms a
[group](group-theory.groups.md), called the
[group of units](ring-theory.groups-of-units-rings.md). The group of units of a
ring is constructed in
[`ring-theory.groups-of-units-rings`](ring-theory.groups-of-units-rings.md).

## Definitions

### Left invertible elements of rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-left-inverse-element-Ring : (x y : type-Ring R) → UU l
  is-left-inverse-element-Ring =
    is-left-inverse-element-Monoid (multiplicative-monoid-Ring R)

  is-left-invertible-element-Ring : type-Ring R → UU l
  is-left-invertible-element-Ring =
    is-left-invertible-element-Monoid (multiplicative-monoid-Ring R)

module _
  {l : Level} (R : Ring l) {x : type-Ring R}
  where

  retraction-is-left-invertible-element-Ring :
    is-left-invertible-element-Ring R x → type-Ring R
  retraction-is-left-invertible-element-Ring =
    retraction-is-left-invertible-element-Monoid
      ( multiplicative-monoid-Ring R)

  is-left-inverse-retraction-is-left-invertible-element-Ring :
    (H : is-left-invertible-element-Ring R x) →
    is-left-inverse-element-Ring R x
      ( retraction-is-left-invertible-element-Ring H)
  is-left-inverse-retraction-is-left-invertible-element-Ring =
    is-left-inverse-retraction-is-left-invertible-element-Monoid
      ( multiplicative-monoid-Ring R)
```

### Right invertible elements of rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-right-inverse-element-Ring : (x y : type-Ring R) → UU l
  is-right-inverse-element-Ring =
    is-right-inverse-element-Monoid (multiplicative-monoid-Ring R)

  is-right-invertible-element-Ring : type-Ring R → UU l
  is-right-invertible-element-Ring =
    is-right-invertible-element-Monoid (multiplicative-monoid-Ring R)

module _
  {l : Level} (R : Ring l) {x : type-Ring R}
  where

  section-is-right-invertible-element-Ring :
    is-right-invertible-element-Ring R x → type-Ring R
  section-is-right-invertible-element-Ring =
    section-is-right-invertible-element-Monoid (multiplicative-monoid-Ring R)

  is-right-inverse-section-is-right-invertible-element-Ring :
    (H : is-right-invertible-element-Ring R x) →
    is-right-inverse-element-Ring R x
      ( section-is-right-invertible-element-Ring H)
  is-right-inverse-section-is-right-invertible-element-Ring =
    is-right-inverse-section-is-right-invertible-element-Monoid
      ( multiplicative-monoid-Ring R)
```

### Invertible elements of rings

```agda
module _
  {l : Level} (R : Ring l) (x : type-Ring R)
  where

  is-inverse-element-Ring : type-Ring R → UU l
  is-inverse-element-Ring =
    is-inverse-element-Monoid (multiplicative-monoid-Ring R) x

  is-invertible-element-Ring : UU l
  is-invertible-element-Ring =
    is-invertible-element-Monoid (multiplicative-monoid-Ring R) x

module _
  {l : Level} (R : Ring l) {x : type-Ring R}
  where

  inv-is-invertible-element-Ring :
    is-invertible-element-Ring R x → type-Ring R
  inv-is-invertible-element-Ring =
    inv-is-invertible-element-Monoid (multiplicative-monoid-Ring R)

  is-right-inverse-inv-is-invertible-element-Ring :
    (H : is-invertible-element-Ring R x) →
    is-right-inverse-element-Ring R x (inv-is-invertible-element-Ring H)
  is-right-inverse-inv-is-invertible-element-Ring =
    is-right-inverse-inv-is-invertible-element-Monoid
      ( multiplicative-monoid-Ring R)

  is-left-inverse-inv-is-invertible-element-Ring :
    (H : is-invertible-element-Ring R x) →
    is-left-inverse-element-Ring R x (inv-is-invertible-element-Ring H)
  is-left-inverse-inv-is-invertible-element-Ring =
    is-left-inverse-inv-is-invertible-element-Monoid
      ( multiplicative-monoid-Ring R)
```

## Properties

### Being an invertible element is a property

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-prop-is-invertible-element-Ring :
    (x : type-Ring R) → is-prop (is-invertible-element-Ring R x)
  is-prop-is-invertible-element-Ring =
    is-prop-is-invertible-element-Monoid
      ( multiplicative-monoid-Ring R)

  is-invertible-element-prop-Ring : type-Ring R → Prop l
  is-invertible-element-prop-Ring =
    is-invertible-element-prop-Monoid
      ( multiplicative-monoid-Ring R)
```

### Inverses are left/right inverses

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-left-invertible-is-invertible-element-Ring :
    (x : type-Ring R) →
    is-invertible-element-Ring R x → is-left-invertible-element-Ring R x
  is-left-invertible-is-invertible-element-Ring =
    is-left-invertible-is-invertible-element-Monoid
      ( multiplicative-monoid-Ring R)

  is-right-invertible-is-invertible-element-Ring :
    (x : type-Ring R) →
    is-invertible-element-Ring R x → is-right-invertible-element-Ring R x
  is-right-invertible-is-invertible-element-Ring =
    is-right-invertible-is-invertible-element-Monoid
      ( multiplicative-monoid-Ring R)
```

### The inverse invertible element

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-right-invertible-left-inverse-Ring :
    (x : type-Ring R) (H : is-left-invertible-element-Ring R x) →
    is-right-invertible-element-Ring R
      ( retraction-is-left-invertible-element-Ring R H)
  is-right-invertible-left-inverse-Ring =
    is-right-invertible-left-inverse-Monoid
      ( multiplicative-monoid-Ring R)

  is-left-invertible-right-inverse-Ring :
    (x : type-Ring R) (H : is-right-invertible-element-Ring R x) →
    is-left-invertible-element-Ring R
      ( section-is-right-invertible-element-Ring R H)
  is-left-invertible-right-inverse-Ring =
    is-left-invertible-right-inverse-Monoid
      ( multiplicative-monoid-Ring R)

  is-invertible-element-inverse-Ring :
    (x : type-Ring R) (H : is-invertible-element-Ring R x) →
    is-invertible-element-Ring R
      ( inv-is-invertible-element-Ring R H)
  is-invertible-element-inverse-Ring =
    is-invertible-element-inverse-Monoid
      ( multiplicative-monoid-Ring R)
```

### Any invertible element of a ring has a contractible type of right inverses

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-contr-is-right-invertible-element-Ring :
    (x : type-Ring R) → is-invertible-element-Ring R x →
    is-contr (is-right-invertible-element-Ring R x)
  is-contr-is-right-invertible-element-Ring =
    is-contr-is-right-invertible-element-Monoid
      ( multiplicative-monoid-Ring R)
```

### Any invertible element of a ring has a contractible type of left inverses

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-contr-is-left-invertible-Ring :
    (x : type-Ring R) → is-invertible-element-Ring R x →
    is-contr (is-left-invertible-element-Ring R x)
  is-contr-is-left-invertible-Ring =
    is-contr-is-left-invertible-Monoid
      ( multiplicative-monoid-Ring R)
```

### The unit of a ring is invertible

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-left-invertible-element-one-Ring :
    is-left-invertible-element-Ring R (one-Ring R)
  is-left-invertible-element-one-Ring =
    is-left-invertible-element-unit-Monoid
      ( multiplicative-monoid-Ring R)

  is-right-invertible-element-one-Ring :
    is-right-invertible-element-Ring R (one-Ring R)
  is-right-invertible-element-one-Ring =
    is-right-invertible-element-unit-Monoid
      ( multiplicative-monoid-Ring R)

  is-invertible-element-one-Ring :
    is-invertible-element-Ring R (one-Ring R)
  is-invertible-element-one-Ring =
    is-invertible-element-unit-Monoid
      ( multiplicative-monoid-Ring R)

  is-invertible-element-is-one-Ring :
    (x : type-Ring R) → one-Ring R ＝ x →
    is-invertible-element-Ring R x
  is-invertible-element-is-one-Ring =
    is-invertible-element-is-unit-Monoid
      ( multiplicative-monoid-Ring R)
```

### If two of the three elements `x`, `y`, and `xy` are invertible, then so is the third

#### Invertible elements are closed under multiplication

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-left-invertible-element-mul-Ring :
    (x y : type-Ring R) →
    is-left-invertible-element-Ring R x →
    is-left-invertible-element-Ring R y →
    is-left-invertible-element-Ring R (mul-Ring R x y)
  is-left-invertible-element-mul-Ring =
    is-left-invertible-element-mul-Monoid
      ( multiplicative-monoid-Ring R)

  is-right-invertible-element-mul-Ring :
    (x y : type-Ring R) →
    is-right-invertible-element-Ring R x →
    is-right-invertible-element-Ring R y →
    is-right-invertible-element-Ring R (mul-Ring R x y)
  is-right-invertible-element-mul-Ring =
    is-right-invertible-element-mul-Monoid
      ( multiplicative-monoid-Ring R)

  is-invertible-element-mul-Ring :
    (x y : type-Ring R) →
    is-invertible-element-Ring R x →
    is-invertible-element-Ring R y →
    is-invertible-element-Ring R (mul-Ring R x y)
  is-invertible-element-mul-Ring =
    is-invertible-element-mul-Monoid
      ( multiplicative-monoid-Ring R)
```

#### If `y` and `xy` are invertible, then so is `x`

```agda
module _
  {l : Level} (R : Ring l) (x y : type-Ring R)
  where

  is-invertible-element-left-factor-Ring :
    is-invertible-element-Ring R y →
    is-invertible-element-Ring R (mul-Ring R x y) →
    is-invertible-element-Ring R x
  is-invertible-element-left-factor-Ring =
    is-invertible-element-left-factor-Monoid
      ( multiplicative-monoid-Ring R)
      ( x)
      ( y)
```

#### If `x` and `xy` are invertible, then so is `y`

```agda
module _
  {l : Level} (R : Ring l) (x y : type-Ring R)
  where

  is-invertible-element-right-factor-Ring :
    is-invertible-element-Ring R x →
    is-invertible-element-Ring R (mul-Ring R x y) →
    is-invertible-element-Ring R y
  is-invertible-element-right-factor-Ring =
    is-invertible-element-right-factor-Monoid
      ( multiplicative-monoid-Ring R)
      ( x)
      ( y)
```

### Invertible elements are closed under negatives

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-invertible-element-neg-Ring :
    (x : type-Ring R) →
    is-invertible-element-Ring R x →
    is-invertible-element-Ring R (neg-Ring R x)
  is-invertible-element-neg-Ring x =
    map-Σ _
      ( neg-Ring R)
      ( λ y →
        map-product
          ( mul-neg-Ring R x y ∙_)
          ( mul-neg-Ring R y x ∙_))

  is-invertible-element-neg-Ring' :
    (x : type-Ring R) →
    is-invertible-element-Ring R (neg-Ring R x) →
    is-invertible-element-Ring R x
  is-invertible-element-neg-Ring' x H =
    tr
      ( is-invertible-element-Ring R)
      ( neg-neg-Ring R x)
      ( is-invertible-element-neg-Ring (neg-Ring R x) H)
```

### The inverse of an invertible element is invertible

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-invertible-element-inv-is-invertible-element-Ring :
    {x : type-Ring R} (H : is-invertible-element-Ring R x) →
    is-invertible-element-Ring R (inv-is-invertible-element-Ring R H)
  is-invertible-element-inv-is-invertible-element-Ring =
    is-invertible-element-inv-is-invertible-element-Monoid
      ( multiplicative-monoid-Ring R)
```

### An element is invertible if and only if multiplying by it is an equivalence

#### An element `x` is invertible if and only if `z ↦ xz` is an equivalence

```agda
module _
  {l : Level} (R : Ring l) {x : type-Ring R}
  where

  inv-is-invertible-element-is-equiv-mul-Ring :
    is-equiv (mul-Ring R x) → type-Ring R
  inv-is-invertible-element-is-equiv-mul-Ring =
    inv-is-invertible-element-is-equiv-mul-Monoid
      ( multiplicative-monoid-Ring R)

  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Ring :
    (H : is-equiv (mul-Ring R x)) →
    mul-Ring R x (inv-is-invertible-element-is-equiv-mul-Ring H) ＝
    one-Ring R
  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Ring =
    is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid
      ( multiplicative-monoid-Ring R)

  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Ring :
    (H : is-equiv (mul-Ring R x)) →
    mul-Ring R (inv-is-invertible-element-is-equiv-mul-Ring H) x ＝
    one-Ring R
  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Ring =
    is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid
      ( multiplicative-monoid-Ring R)

  is-invertible-element-is-equiv-mul-Ring :
    is-equiv (mul-Ring R x) → is-invertible-element-Ring R x
  is-invertible-element-is-equiv-mul-Ring =
    is-invertible-element-is-equiv-mul-Monoid
      ( multiplicative-monoid-Ring R)

  left-div-is-invertible-element-Ring :
    is-invertible-element-Ring R x → type-Ring R → type-Ring R
  left-div-is-invertible-element-Ring =
    left-div-is-invertible-element-Monoid
      ( multiplicative-monoid-Ring R)

  is-section-left-div-is-invertible-element-Ring :
    (H : is-invertible-element-Ring R x) →
    mul-Ring R x ∘ left-div-is-invertible-element-Ring H ~ id
  is-section-left-div-is-invertible-element-Ring =
    is-section-left-div-is-invertible-element-Monoid
      ( multiplicative-monoid-Ring R)

  is-retraction-left-div-is-invertible-element-Ring :
    (H : is-invertible-element-Ring R x) →
    left-div-is-invertible-element-Ring H ∘ mul-Ring R x ~ id
  is-retraction-left-div-is-invertible-element-Ring =
    is-retraction-left-div-is-invertible-element-Monoid
      ( multiplicative-monoid-Ring R)

  is-equiv-mul-is-invertible-element-Ring :
    is-invertible-element-Ring R x → is-equiv (mul-Ring R x)
  is-equiv-mul-is-invertible-element-Ring =
    is-equiv-mul-is-invertible-element-Monoid
      ( multiplicative-monoid-Ring R)
```

#### An element `x` is invertible if and only if `z ↦ zx` is an equivalence

```agda
module _
  {l : Level} (R : Ring l) {x : type-Ring R}
  where

  inv-is-invertible-element-is-equiv-mul-Ring' :
    is-equiv (mul-Ring' R x) → type-Ring R
  inv-is-invertible-element-is-equiv-mul-Ring' =
    inv-is-invertible-element-is-equiv-mul-Monoid'
      ( multiplicative-monoid-Ring R)

  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Ring' :
    (H : is-equiv (mul-Ring' R x)) →
    mul-Ring R (inv-is-invertible-element-is-equiv-mul-Ring' H) x ＝
    one-Ring R
  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Ring' =
    is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid'
      ( multiplicative-monoid-Ring R)

  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Ring' :
    (H : is-equiv (mul-Ring' R x)) →
    mul-Ring R x (inv-is-invertible-element-is-equiv-mul-Ring' H) ＝
    one-Ring R
  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Ring' =
    is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid'
      ( multiplicative-monoid-Ring R)

  is-invertible-element-is-equiv-mul-Ring' :
    is-equiv (mul-Ring' R x) → is-invertible-element-Ring R x
  is-invertible-element-is-equiv-mul-Ring' =
    is-invertible-element-is-equiv-mul-Monoid'
      ( multiplicative-monoid-Ring R)

  right-div-is-invertible-element-Ring :
    is-invertible-element-Ring R x → type-Ring R → type-Ring R
  right-div-is-invertible-element-Ring =
    right-div-is-invertible-element-Monoid
      ( multiplicative-monoid-Ring R)

  is-section-right-div-is-invertible-element-Ring :
    (H : is-invertible-element-Ring R x) →
    mul-Ring' R x ∘ right-div-is-invertible-element-Ring H ~ id
  is-section-right-div-is-invertible-element-Ring =
    is-section-right-div-is-invertible-element-Monoid
      ( multiplicative-monoid-Ring R)

  is-retraction-right-div-is-invertible-element-Ring :
    (H : is-invertible-element-Ring R x) →
    right-div-is-invertible-element-Ring H ∘ mul-Ring' R x ~ id
  is-retraction-right-div-is-invertible-element-Ring =
    is-retraction-right-div-is-invertible-element-Monoid
      ( multiplicative-monoid-Ring R)

  is-equiv-mul-is-invertible-element-Ring' :
    is-invertible-element-Ring R x → is-equiv (mul-Ring' R x)
  is-equiv-mul-is-invertible-element-Ring' =
    is-equiv-mul-is-invertible-element-Monoid'
      ( multiplicative-monoid-Ring R)
```

## See also

- The group of multiplicative units of a ring is defined in
  [`ring-theory.groups-of-units-rings`](ring-theory.groups-of-units-rings.md).
