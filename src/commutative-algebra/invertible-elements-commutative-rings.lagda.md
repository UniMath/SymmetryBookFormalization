# Invertible elements in commutative rings

```agda
module commutative-algebra.invertible-elements-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import ring-theory.invertible-elements-rings
```

</details>

## Idea

An element of a [commutative ring](commutative-algebra.commutative-rings.md)
`A`is said to be **invertible** if it has a two-sided inverse. However, since
multiplication in commutative rings is commutative, any element is already
invertible as soon as it has either a left or a right inverse. The invertible
elements of a commutative ring `A` are also called the **(multiplicative)
units** of `A`.

The [abelian group](group-theory.abelian-groups.md) of multiplicative units is
constructed in
[`commutative-algebra.groups-of-units-commutative-rings`](commutative-algebra.groups-of-units-commutative-rings.md).

## Definitions

### Left invertible elements of commutative rings

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  is-left-inverse-element-Commutative-Ring :
    (x y : type-Commutative-Ring A) → UU l
  is-left-inverse-element-Commutative-Ring =
    is-left-inverse-element-Ring (ring-Commutative-Ring A)

  is-left-invertible-element-Commutative-Ring : type-Commutative-Ring A → UU l
  is-left-invertible-element-Commutative-Ring =
    is-left-invertible-element-Ring (ring-Commutative-Ring A)

module _
  {l : Level} (A : Commutative-Ring l) {x : type-Commutative-Ring A}
  where

  retraction-is-left-invertible-element-Commutative-Ring :
    is-left-invertible-element-Commutative-Ring A x → type-Commutative-Ring A
  retraction-is-left-invertible-element-Commutative-Ring =
    retraction-is-left-invertible-element-Ring
      ( ring-Commutative-Ring A)

  is-left-inverse-retraction-is-left-invertible-element-Commutative-Ring :
    (H : is-left-invertible-element-Commutative-Ring A x) →
    is-left-inverse-element-Commutative-Ring A x
      ( retraction-is-left-invertible-element-Commutative-Ring H)
  is-left-inverse-retraction-is-left-invertible-element-Commutative-Ring =
    is-left-inverse-retraction-is-left-invertible-element-Ring
      ( ring-Commutative-Ring A)
```

### Right invertible elements of commutative rings

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  is-right-inverse-element-Commutative-Ring :
    (x y : type-Commutative-Ring A) → UU l
  is-right-inverse-element-Commutative-Ring =
    is-right-inverse-element-Ring (ring-Commutative-Ring A)

  is-right-invertible-element-Commutative-Ring : type-Commutative-Ring A → UU l
  is-right-invertible-element-Commutative-Ring =
    is-right-invertible-element-Ring (ring-Commutative-Ring A)

module _
  {l : Level} (A : Commutative-Ring l) {x : type-Commutative-Ring A}
  where

  section-is-right-invertible-element-Commutative-Ring :
    is-right-invertible-element-Commutative-Ring A x → type-Commutative-Ring A
  section-is-right-invertible-element-Commutative-Ring =
    section-is-right-invertible-element-Ring (ring-Commutative-Ring A)

  is-right-inverse-section-is-right-invertible-element-Commutative-Ring :
    (H : is-right-invertible-element-Commutative-Ring A x) →
    is-right-inverse-element-Commutative-Ring A x
      ( section-is-right-invertible-element-Commutative-Ring H)
  is-right-inverse-section-is-right-invertible-element-Commutative-Ring =
    is-right-inverse-section-is-right-invertible-element-Ring
      ( ring-Commutative-Ring A)
```

### Invertible elements of commutative rings

```agda
module _
  {l : Level} (A : Commutative-Ring l) (x : type-Commutative-Ring A)
  where

  is-inverse-element-Commutative-Ring : type-Commutative-Ring A → UU l
  is-inverse-element-Commutative-Ring =
    is-inverse-element-Ring (ring-Commutative-Ring A) x

  is-invertible-element-Commutative-Ring : UU l
  is-invertible-element-Commutative-Ring =
    is-invertible-element-Ring (ring-Commutative-Ring A) x

module _
  {l : Level} (A : Commutative-Ring l) {x : type-Commutative-Ring A}
  where

  inv-is-invertible-element-Commutative-Ring :
    is-invertible-element-Commutative-Ring A x → type-Commutative-Ring A
  inv-is-invertible-element-Commutative-Ring =
    inv-is-invertible-element-Ring (ring-Commutative-Ring A)

  is-right-inverse-inv-is-invertible-element-Commutative-Ring :
    (H : is-invertible-element-Commutative-Ring A x) →
    is-right-inverse-element-Commutative-Ring A x
      ( inv-is-invertible-element-Commutative-Ring H)
  is-right-inverse-inv-is-invertible-element-Commutative-Ring =
    is-right-inverse-inv-is-invertible-element-Ring
      ( ring-Commutative-Ring A)

  is-left-inverse-inv-is-invertible-element-Commutative-Ring :
    (H : is-invertible-element-Commutative-Ring A x) →
    is-left-inverse-element-Commutative-Ring A x
      ( inv-is-invertible-element-Commutative-Ring H)
  is-left-inverse-inv-is-invertible-element-Commutative-Ring =
    is-left-inverse-inv-is-invertible-element-Ring
      ( ring-Commutative-Ring A)

  is-invertible-is-left-invertible-element-Commutative-Ring :
    is-left-invertible-element-Commutative-Ring A x →
    is-invertible-element-Commutative-Ring A x
  pr1 (is-invertible-is-left-invertible-element-Commutative-Ring H) =
    retraction-is-left-invertible-element-Commutative-Ring A H
  pr1 (pr2 (is-invertible-is-left-invertible-element-Commutative-Ring H)) =
    commutative-mul-Commutative-Ring A _ _ ∙
    is-left-inverse-retraction-is-left-invertible-element-Commutative-Ring A H
  pr2 (pr2 (is-invertible-is-left-invertible-element-Commutative-Ring H)) =
    is-left-inverse-retraction-is-left-invertible-element-Commutative-Ring A H

  is-invertible-is-right-invertible-element-Commutative-Ring :
    is-right-invertible-element-Commutative-Ring A x →
    is-invertible-element-Commutative-Ring A x
  pr1 (is-invertible-is-right-invertible-element-Commutative-Ring H) =
    section-is-right-invertible-element-Commutative-Ring A H
  pr1 (pr2 (is-invertible-is-right-invertible-element-Commutative-Ring H)) =
    is-right-inverse-section-is-right-invertible-element-Commutative-Ring A H
  pr2 (pr2 (is-invertible-is-right-invertible-element-Commutative-Ring H)) =
    commutative-mul-Commutative-Ring A _ _ ∙
    is-right-inverse-section-is-right-invertible-element-Commutative-Ring A H
```

## Properties

### Being an invertible element is a property

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  is-prop-is-invertible-element-Commutative-Ring :
    (x : type-Commutative-Ring A) →
    is-prop (is-invertible-element-Commutative-Ring A x)
  is-prop-is-invertible-element-Commutative-Ring =
    is-prop-is-invertible-element-Ring (ring-Commutative-Ring A)

  is-invertible-element-prop-Commutative-Ring : type-Commutative-Ring A → Prop l
  is-invertible-element-prop-Commutative-Ring =
    is-invertible-element-prop-Ring (ring-Commutative-Ring A)
```

### Inverses are left/right inverses

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  is-left-invertible-is-invertible-element-Commutative-Ring :
    (x : type-Commutative-Ring A) →
    is-invertible-element-Commutative-Ring A x →
    is-left-invertible-element-Commutative-Ring A x
  is-left-invertible-is-invertible-element-Commutative-Ring =
    is-left-invertible-is-invertible-element-Ring (ring-Commutative-Ring A)

  is-right-invertible-is-invertible-element-Commutative-Ring :
    (x : type-Commutative-Ring A) →
    is-invertible-element-Commutative-Ring A x →
    is-right-invertible-element-Commutative-Ring A x
  is-right-invertible-is-invertible-element-Commutative-Ring =
    is-right-invertible-is-invertible-element-Ring (ring-Commutative-Ring A)
```

### The inverse invertible element

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  is-right-invertible-left-inverse-Commutative-Ring :
    (x : type-Commutative-Ring A)
    (H : is-left-invertible-element-Commutative-Ring A x) →
    is-right-invertible-element-Commutative-Ring A
      ( retraction-is-left-invertible-element-Commutative-Ring A H)
  is-right-invertible-left-inverse-Commutative-Ring =
    is-right-invertible-left-inverse-Ring (ring-Commutative-Ring A)

  is-left-invertible-right-inverse-Commutative-Ring :
    (x : type-Commutative-Ring A)
    (H : is-right-invertible-element-Commutative-Ring A x) →
    is-left-invertible-element-Commutative-Ring A
      ( section-is-right-invertible-element-Commutative-Ring A H)
  is-left-invertible-right-inverse-Commutative-Ring =
    is-left-invertible-right-inverse-Ring (ring-Commutative-Ring A)

  is-invertible-element-inverse-Commutative-Ring :
    (x : type-Commutative-Ring A)
    (H : is-invertible-element-Commutative-Ring A x) →
    is-invertible-element-Commutative-Ring A
      ( inv-is-invertible-element-Commutative-Ring A H)
  is-invertible-element-inverse-Commutative-Ring =
    is-invertible-element-inverse-Ring (ring-Commutative-Ring A)
```

### Any invertible element of a commutative ring has a contractible type of right inverses

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  is-contr-is-right-invertible-element-Commutative-Ring :
    (x : type-Commutative-Ring A) → is-invertible-element-Commutative-Ring A x →
    is-contr (is-right-invertible-element-Commutative-Ring A x)
  is-contr-is-right-invertible-element-Commutative-Ring =
    is-contr-is-right-invertible-element-Ring (ring-Commutative-Ring A)
```

### Any invertible element of a commutative ring has a contractible type of left inverses

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  is-contr-is-left-invertible-Commutative-Ring :
    (x : type-Commutative-Ring A) → is-invertible-element-Commutative-Ring A x →
    is-contr (is-left-invertible-element-Commutative-Ring A x)
  is-contr-is-left-invertible-Commutative-Ring =
    is-contr-is-left-invertible-Ring (ring-Commutative-Ring A)
```

### The unit of a commutative ring is invertible

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  is-left-invertible-element-one-Commutative-Ring :
    is-left-invertible-element-Commutative-Ring A (one-Commutative-Ring A)
  is-left-invertible-element-one-Commutative-Ring =
    is-left-invertible-element-one-Ring (ring-Commutative-Ring A)

  is-right-invertible-element-one-Commutative-Ring :
    is-right-invertible-element-Commutative-Ring A (one-Commutative-Ring A)
  is-right-invertible-element-one-Commutative-Ring =
    is-right-invertible-element-one-Ring (ring-Commutative-Ring A)

  is-invertible-element-one-Commutative-Ring :
    is-invertible-element-Commutative-Ring A (one-Commutative-Ring A)
  is-invertible-element-one-Commutative-Ring =
    is-invertible-element-one-Ring (ring-Commutative-Ring A)

  is-invertible-element-is-one-Commutative-Ring :
    (x : type-Commutative-Ring A) → one-Commutative-Ring A ＝ x →
    is-invertible-element-Commutative-Ring A x
  is-invertible-element-is-one-Commutative-Ring =
    is-invertible-element-is-one-Ring (ring-Commutative-Ring A)
```

### A product `xy` is invertible if and only if both `x` and `y` are invertible

#### Invertible elements are closed under multiplication

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  is-left-invertible-element-mul-Commutative-Ring :
    (x y : type-Commutative-Ring A) →
    is-left-invertible-element-Commutative-Ring A x →
    is-left-invertible-element-Commutative-Ring A y →
    is-left-invertible-element-Commutative-Ring A (mul-Commutative-Ring A x y)
  is-left-invertible-element-mul-Commutative-Ring =
    is-left-invertible-element-mul-Ring (ring-Commutative-Ring A)

  is-right-invertible-element-mul-Commutative-Ring :
    (x y : type-Commutative-Ring A) →
    is-right-invertible-element-Commutative-Ring A x →
    is-right-invertible-element-Commutative-Ring A y →
    is-right-invertible-element-Commutative-Ring A (mul-Commutative-Ring A x y)
  is-right-invertible-element-mul-Commutative-Ring =
    is-right-invertible-element-mul-Ring (ring-Commutative-Ring A)

  is-invertible-element-mul-Commutative-Ring :
    (x y : type-Commutative-Ring A) →
    is-invertible-element-Commutative-Ring A x →
    is-invertible-element-Commutative-Ring A y →
    is-invertible-element-Commutative-Ring A (mul-Commutative-Ring A x y)
  is-invertible-element-mul-Commutative-Ring =
    is-invertible-element-mul-Ring (ring-Commutative-Ring A)
```

#### If `xy` is invertible then so is `x`

```agda
module _
  {l : Level} (A : Commutative-Ring l) (x y : type-Commutative-Ring A)
  where

  is-invertible-element-left-factor-Commutative-Ring :
    is-invertible-element-Commutative-Ring A (mul-Commutative-Ring A x y) →
    is-invertible-element-Commutative-Ring A x
  pr1 (is-invertible-element-left-factor-Commutative-Ring (u , p , q)) =
    mul-Commutative-Ring A y u
  pr1 (pr2 (is-invertible-element-left-factor-Commutative-Ring (u , p , q))) =
    inv (associative-mul-Commutative-Ring A x y u) ∙ p
  pr2 (pr2 (is-invertible-element-left-factor-Commutative-Ring (u , p , q))) =
    right-swap-mul-Commutative-Ring A y u x ∙
    ap (mul-Commutative-Ring' A u) (commutative-mul-Commutative-Ring A y x) ∙
    p
```

#### If `xy` is invertible then so is `y`

```agda
module _
  {l : Level} (A : Commutative-Ring l) (x y : type-Commutative-Ring A)
  where

  is-invertible-element-right-factor-Commutative-Ring :
    is-invertible-element-Commutative-Ring A (mul-Commutative-Ring A x y) →
    is-invertible-element-Commutative-Ring A y
  pr1 (is-invertible-element-right-factor-Commutative-Ring (u , p , q)) =
    mul-Commutative-Ring A u x
  pr1 (pr2 (is-invertible-element-right-factor-Commutative-Ring (u , p , q))) =
    left-swap-mul-Commutative-Ring A y u x ∙
    ap (mul-Commutative-Ring A u) (commutative-mul-Commutative-Ring A y x) ∙
    q
  pr2 (pr2 (is-invertible-element-right-factor-Commutative-Ring (u , p , q))) =
    associative-mul-Commutative-Ring A u x y ∙ q
```

### The inverse of an invertible element is invertible

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  is-invertible-element-inv-is-invertible-element-Commutative-Ring :
    {x : type-Commutative-Ring A}
    (H : is-invertible-element-Commutative-Ring A x) →
    is-invertible-element-Commutative-Ring A
      ( inv-is-invertible-element-Commutative-Ring A H)
  is-invertible-element-inv-is-invertible-element-Commutative-Ring =
    is-invertible-element-inv-is-invertible-element-Ring
      ( ring-Commutative-Ring A)
```

## See also

- The group of multiplicative units of a commutative ring is defined in
  [`commutative-algebra.groups-of-units-commutative-rings`](commutative-algebra.groups-of-units-commutative-rings.md).
