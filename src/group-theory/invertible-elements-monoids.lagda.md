# Invertible elements in monoids

```agda
module group-theory.invertible-elements-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.monoids
```

</details>

## Idea

An element `x : M` in a [monoid](group-theory.monoids.md) `M` is said to be
**left invertible** if there is an element `y : M` such that `yx ＝ e`, and it
is said to be **right invertible** if there is an element `y : M` such that
`xy ＝ e`. The element `x` is said to be **invertible** if it has a **two-sided
inverse**, i.e., if if there is an element `y : M` such that `xy = e` and
`yx = e`. Left inverses of elements are also called **retractions** and right
inverses are also called **sections**.

## Definitions

### Right invertible elements

```agda
module _
  {l : Level} (M : Monoid l) (x : type-Monoid M)
  where

  is-right-inverse-element-Monoid : type-Monoid M → UU l
  is-right-inverse-element-Monoid y = mul-Monoid M x y ＝ unit-Monoid M

  is-right-invertible-element-Monoid : UU l
  is-right-invertible-element-Monoid =
    Σ (type-Monoid M) is-right-inverse-element-Monoid

module _
  {l : Level} (M : Monoid l) {x : type-Monoid M}
  where

  section-is-right-invertible-element-Monoid :
    is-right-invertible-element-Monoid M x → type-Monoid M
  section-is-right-invertible-element-Monoid = pr1

  is-right-inverse-section-is-right-invertible-element-Monoid :
    (H : is-right-invertible-element-Monoid M x) →
    is-right-inverse-element-Monoid M x
      ( section-is-right-invertible-element-Monoid H)
  is-right-inverse-section-is-right-invertible-element-Monoid = pr2
```

### Left invertible elements

```agda
module _
  {l : Level} (M : Monoid l) (x : type-Monoid M)
  where

  is-left-inverse-element-Monoid : type-Monoid M → UU l
  is-left-inverse-element-Monoid y = mul-Monoid M y x ＝ unit-Monoid M

  is-left-invertible-element-Monoid : UU l
  is-left-invertible-element-Monoid =
    Σ (type-Monoid M) is-left-inverse-element-Monoid

module _
  {l : Level} (M : Monoid l) {x : type-Monoid M}
  where

  retraction-is-left-invertible-element-Monoid :
    is-left-invertible-element-Monoid M x → type-Monoid M
  retraction-is-left-invertible-element-Monoid = pr1

  is-left-inverse-retraction-is-left-invertible-element-Monoid :
    (H : is-left-invertible-element-Monoid M x) →
    is-left-inverse-element-Monoid M x
      ( retraction-is-left-invertible-element-Monoid H)
  is-left-inverse-retraction-is-left-invertible-element-Monoid = pr2
```

### Invertible elements

```agda
module _
  {l : Level} (M : Monoid l) (x : type-Monoid M)
  where

  is-inverse-element-Monoid : type-Monoid M → UU l
  is-inverse-element-Monoid y =
    is-right-inverse-element-Monoid M x y ×
    is-left-inverse-element-Monoid M x y

  is-invertible-element-Monoid : UU l
  is-invertible-element-Monoid =
    Σ (type-Monoid M) is-inverse-element-Monoid

module _
  {l : Level} (M : Monoid l) {x : type-Monoid M}
  where

  inv-is-invertible-element-Monoid :
    is-invertible-element-Monoid M x → type-Monoid M
  inv-is-invertible-element-Monoid = pr1

  is-right-inverse-inv-is-invertible-element-Monoid :
    (H : is-invertible-element-Monoid M x) →
    is-right-inverse-element-Monoid M x (inv-is-invertible-element-Monoid H)
  is-right-inverse-inv-is-invertible-element-Monoid H = pr1 (pr2 H)

  is-left-inverse-inv-is-invertible-element-Monoid :
    (H : is-invertible-element-Monoid M x) →
    is-left-inverse-element-Monoid M x (inv-is-invertible-element-Monoid H)
  is-left-inverse-inv-is-invertible-element-Monoid H = pr2 (pr2 H)
```

## Properties

### Being an invertible element is a property

```agda
module _
  {l : Level} (M : Monoid l)
  where

  all-elements-equal-is-invertible-element-Monoid :
    (x : type-Monoid M) → all-elements-equal (is-invertible-element-Monoid M x)
  all-elements-equal-is-invertible-element-Monoid x (y , p , q) (y' , p' , q') =
    eq-type-subtype
      ( λ z →
        product-Prop
          ( Id-Prop (set-Monoid M) (mul-Monoid M x z) (unit-Monoid M))
          ( Id-Prop (set-Monoid M) (mul-Monoid M z x) (unit-Monoid M)))
      ( ( inv (left-unit-law-mul-Monoid M y)) ∙
        ( inv (ap (λ z → mul-Monoid M z y) q')) ∙
        ( associative-mul-Monoid M y' x y) ∙
        ( ap (mul-Monoid M y') p) ∙
        ( right-unit-law-mul-Monoid M y'))

  is-prop-is-invertible-element-Monoid :
    (x : type-Monoid M) → is-prop (is-invertible-element-Monoid M x)
  is-prop-is-invertible-element-Monoid x =
    is-prop-all-elements-equal
      ( all-elements-equal-is-invertible-element-Monoid x)

  is-invertible-element-prop-Monoid : type-Monoid M → Prop l
  pr1 (is-invertible-element-prop-Monoid x) =
    is-invertible-element-Monoid M x
  pr2 (is-invertible-element-prop-Monoid x) =
    is-prop-is-invertible-element-Monoid x
```

### Inverses are left/right inverses

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-left-invertible-is-invertible-element-Monoid :
    (x : type-Monoid M) →
    is-invertible-element-Monoid M x → is-left-invertible-element-Monoid M x
  pr1 (is-left-invertible-is-invertible-element-Monoid x is-invertible-x) =
    pr1 is-invertible-x
  pr2 (is-left-invertible-is-invertible-element-Monoid x is-invertible-x) =
    pr2 (pr2 is-invertible-x)

  is-right-invertible-is-invertible-element-Monoid :
    (x : type-Monoid M) →
    is-invertible-element-Monoid M x → is-right-invertible-element-Monoid M x
  pr1 (is-right-invertible-is-invertible-element-Monoid x is-invertible-x) =
    pr1 is-invertible-x
  pr2 (is-right-invertible-is-invertible-element-Monoid x is-invertible-x) =
    pr1 (pr2 is-invertible-x)
```

### The inverse invertible element

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-right-invertible-left-inverse-Monoid :
    (x : type-Monoid M) (lx : is-left-invertible-element-Monoid M x) →
    is-right-invertible-element-Monoid M (pr1 lx)
  pr1 (is-right-invertible-left-inverse-Monoid x lx) = x
  pr2 (is-right-invertible-left-inverse-Monoid x lx) = pr2 lx

  is-left-invertible-right-inverse-Monoid :
    (x : type-Monoid M) (rx : is-right-invertible-element-Monoid M x) →
    is-left-invertible-element-Monoid M (pr1 rx)
  pr1 (is-left-invertible-right-inverse-Monoid x rx) = x
  pr2 (is-left-invertible-right-inverse-Monoid x rx) = pr2 rx

  is-invertible-element-inverse-Monoid :
    (x : type-Monoid M) (x' : is-invertible-element-Monoid M x) →
    is-invertible-element-Monoid M (pr1 x')
  pr1 (is-invertible-element-inverse-Monoid x x') = x
  pr1 (pr2 (is-invertible-element-inverse-Monoid x x')) = pr2 (pr2 x')
  pr2 (pr2 (is-invertible-element-inverse-Monoid x x')) = pr1 (pr2 x')
```

### Any invertible element of a monoid has a contractible type of right inverses

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-contr-is-right-invertible-element-Monoid :
    (x : type-Monoid M) → is-invertible-element-Monoid M x →
    is-contr (is-right-invertible-element-Monoid M x)
  pr1 (pr1 (is-contr-is-right-invertible-element-Monoid x (y , p , q))) = y
  pr2 (pr1 (is-contr-is-right-invertible-element-Monoid x (y , p , q))) = p
  pr2 (is-contr-is-right-invertible-element-Monoid x (y , p , q)) (y' , q') =
    eq-type-subtype
      ( λ u → Id-Prop (set-Monoid M) (mul-Monoid M x u) (unit-Monoid M))
      ( ( inv (right-unit-law-mul-Monoid M y)) ∙
        ( ap (mul-Monoid M y) (inv q')) ∙
        ( inv (associative-mul-Monoid M y x y')) ∙
        ( ap (mul-Monoid' M y') q) ∙
        ( left-unit-law-mul-Monoid M y'))
```

### Any invertible element of a monoid has a contractible type of left inverses

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-contr-is-left-invertible-Monoid :
    (x : type-Monoid M) → is-invertible-element-Monoid M x →
    is-contr (is-left-invertible-element-Monoid M x)
  pr1 (pr1 (is-contr-is-left-invertible-Monoid x (y , p , q))) = y
  pr2 (pr1 (is-contr-is-left-invertible-Monoid x (y , p , q))) = q
  pr2 (is-contr-is-left-invertible-Monoid x (y , p , q)) (y' , p') =
    eq-type-subtype
      ( λ u → Id-Prop (set-Monoid M) (mul-Monoid M u x) (unit-Monoid M))
      ( ( inv (left-unit-law-mul-Monoid M y)) ∙
        ( ap (mul-Monoid' M y) (inv p')) ∙
        ( associative-mul-Monoid M y' x y) ∙
        ( ap (mul-Monoid M y') p) ∙
        ( right-unit-law-mul-Monoid M y'))
```

### The unit of a monoid is invertible

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-left-invertible-element-unit-Monoid :
    is-left-invertible-element-Monoid M (unit-Monoid M)
  pr1 is-left-invertible-element-unit-Monoid = unit-Monoid M
  pr2 is-left-invertible-element-unit-Monoid =
    left-unit-law-mul-Monoid M (unit-Monoid M)

  is-right-invertible-element-unit-Monoid :
    is-right-invertible-element-Monoid M (unit-Monoid M)
  pr1 is-right-invertible-element-unit-Monoid = unit-Monoid M
  pr2 is-right-invertible-element-unit-Monoid =
    left-unit-law-mul-Monoid M (unit-Monoid M)

  is-invertible-element-unit-Monoid :
    is-invertible-element-Monoid M (unit-Monoid M)
  pr1 is-invertible-element-unit-Monoid =
    unit-Monoid M
  pr1 (pr2 is-invertible-element-unit-Monoid) =
    left-unit-law-mul-Monoid M (unit-Monoid M)
  pr2 (pr2 is-invertible-element-unit-Monoid) =
    left-unit-law-mul-Monoid M (unit-Monoid M)

  is-invertible-element-is-unit-Monoid :
    (x : type-Monoid M) → unit-Monoid M ＝ x →
    is-invertible-element-Monoid M x
  is-invertible-element-is-unit-Monoid .(unit-Monoid M) refl =
    is-invertible-element-unit-Monoid
```

### The inverse of an invertible element is invertible

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-invertible-element-inv-is-invertible-element-Monoid :
    {x : type-Monoid M} (H : is-invertible-element-Monoid M x) →
    is-invertible-element-Monoid M (inv-is-invertible-element-Monoid M H)
  pr1 (is-invertible-element-inv-is-invertible-element-Monoid {x} H) = x
  pr1 (pr2 (is-invertible-element-inv-is-invertible-element-Monoid H)) =
    is-left-inverse-inv-is-invertible-element-Monoid M H
  pr2 (pr2 (is-invertible-element-inv-is-invertible-element-Monoid H)) =
    is-right-inverse-inv-is-invertible-element-Monoid M H
```

### If two of the three elements `x`, `y`, and `xy` are invertible, then so is the third

#### Invertible elements are closed under multiplication

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-left-invertible-element-mul-Monoid :
    (x y : type-Monoid M) →
    is-left-invertible-element-Monoid M x →
    is-left-invertible-element-Monoid M y →
    is-left-invertible-element-Monoid M (mul-Monoid M x y)
  pr1 (is-left-invertible-element-mul-Monoid x y (lx , H) (ly , I)) =
    mul-Monoid M ly lx
  pr2 (is-left-invertible-element-mul-Monoid x y (lx , H) (ly , I)) =
    ( associative-mul-Monoid M ly lx (mul-Monoid M x y)) ∙
    ( ap
      ( mul-Monoid M ly)
      ( ( inv (associative-mul-Monoid M lx x y)) ∙
        ( ap (λ z → mul-Monoid M z y) H) ∙
        ( left-unit-law-mul-Monoid M y))) ∙
    ( I)

  is-right-invertible-element-mul-Monoid :
    (x y : type-Monoid M) →
    is-right-invertible-element-Monoid M x →
    is-right-invertible-element-Monoid M y →
    is-right-invertible-element-Monoid M (mul-Monoid M x y)
  pr1 (is-right-invertible-element-mul-Monoid x y (rx , H) (ry , I)) =
    mul-Monoid M ry rx
  pr2 (is-right-invertible-element-mul-Monoid x y (rx , H) (ry , I)) =
    ( associative-mul-Monoid M x y (mul-Monoid M ry rx)) ∙
    ( ap
      ( mul-Monoid M x)
      ( ( inv (associative-mul-Monoid M y ry rx)) ∙
        ( ap (λ z → mul-Monoid M z rx) I) ∙
        ( left-unit-law-mul-Monoid M rx))) ∙
    ( H)

  is-invertible-element-mul-Monoid :
    (x y : type-Monoid M) →
    is-invertible-element-Monoid M x →
    is-invertible-element-Monoid M y →
    is-invertible-element-Monoid M (mul-Monoid M x y)
  pr1 (is-invertible-element-mul-Monoid x y (x' , Lx , Rx) (y' , Ly , Ry)) =
    mul-Monoid M y' x'
  pr1 (pr2 (is-invertible-element-mul-Monoid x y H K)) =
    pr2
      ( is-right-invertible-element-mul-Monoid x y
        ( is-right-invertible-is-invertible-element-Monoid M x H)
        ( is-right-invertible-is-invertible-element-Monoid M y K))
  pr2 (pr2 (is-invertible-element-mul-Monoid x y H K)) =
    pr2
      ( is-left-invertible-element-mul-Monoid x y
        ( is-left-invertible-is-invertible-element-Monoid M x H)
        ( is-left-invertible-is-invertible-element-Monoid M y K))
```

#### If `y` and `xy` are invertible, then so is `x`

```agda
module _
  {l : Level} (M : Monoid l) (x y : type-Monoid M)
  where

  is-invertible-element-left-factor-Monoid :
    is-invertible-element-Monoid M y →
    is-invertible-element-Monoid M (mul-Monoid M x y) →
    is-invertible-element-Monoid M x
  is-invertible-element-left-factor-Monoid H@(y' , Ly , Ry) K =
    tr
      ( is-invertible-element-Monoid M)
      ( associative-mul-Monoid M x y y' ∙
        ap (mul-Monoid M x) Ly ∙
        right-unit-law-mul-Monoid M x)
      ( is-invertible-element-mul-Monoid M
        ( mul-Monoid M x y)
        ( y')
        ( K)
        ( is-invertible-element-inv-is-invertible-element-Monoid M H))
```

#### If `x` and `xy` are invertible, then so is `y`

```agda
module _
  {l : Level} (M : Monoid l) (x y : type-Monoid M)
  where

  is-invertible-element-right-factor-Monoid :
    is-invertible-element-Monoid M x →
    is-invertible-element-Monoid M (mul-Monoid M x y) →
    is-invertible-element-Monoid M y
  is-invertible-element-right-factor-Monoid H@(x' , Lx , Rx) K =
    tr
      ( is-invertible-element-Monoid M)
      ( inv (associative-mul-Monoid M x' x y) ∙
        ap (mul-Monoid' M y) Rx ∙
        left-unit-law-mul-Monoid M y)
      ( is-invertible-element-mul-Monoid M
        ( x')
        ( mul-Monoid M x y)
        ( is-invertible-element-inv-is-invertible-element-Monoid M H)
        ( K))
```

### An element is invertible if and only if multiplying by it is an equivalence

**Proof:** Suppose that the map `z ↦ xz` is an equivalence. Then there is a
unique element `y` such that `xy ＝ 1`. Thus we have a right inverse of `x`. To
see that `y` is also a left inverse of `x`, note that the map `z ↦ xz` is
injective by the assumption that it is an equivalence. Therefore it suffices to
show that `x(yx) ＝ x1`. This follows from the following calculation:

```text
  x(yx) ＝ (xy)x ＝ 1x ＝ x ＝ x1.
```

This completes the proof that if `z ↦ xz` is an equivalence, then `x` is
invertible. The converse is straightfoward.

In the following code we give the above proof, as well as the analogous proof
that `x` is invertible if `z ↦ zx` is an equivalence, and the converse of both
statements.

#### An element `x` is invertible if and only if `z ↦ xz` is an equivalence

```agda
module _
  {l : Level} (M : Monoid l) {x : type-Monoid M}
  where

  inv-is-invertible-element-is-equiv-mul-Monoid :
    is-equiv (mul-Monoid M x) → type-Monoid M
  inv-is-invertible-element-is-equiv-mul-Monoid H =
    map-inv-is-equiv H (unit-Monoid M)

  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid :
    (H : is-equiv (mul-Monoid M x)) →
    mul-Monoid M x (inv-is-invertible-element-is-equiv-mul-Monoid H) ＝
    unit-Monoid M
  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid H =
    is-section-map-inv-is-equiv H (unit-Monoid M)

  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid :
    (H : is-equiv (mul-Monoid M x)) →
    mul-Monoid M (inv-is-invertible-element-is-equiv-mul-Monoid H) x ＝
    unit-Monoid M
  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid H =
    is-injective-is-equiv H
      ( ( inv (associative-mul-Monoid M _ _ _)) ∙
        ( ap
          ( mul-Monoid' M x)
          ( is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid H)) ∙
        ( left-unit-law-mul-Monoid M x) ∙
        ( inv (right-unit-law-mul-Monoid M x)))

  is-invertible-element-is-equiv-mul-Monoid :
    is-equiv (mul-Monoid M x) → is-invertible-element-Monoid M x
  pr1 (is-invertible-element-is-equiv-mul-Monoid H) =
    inv-is-invertible-element-is-equiv-mul-Monoid H
  pr1 (pr2 (is-invertible-element-is-equiv-mul-Monoid H)) =
    is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid H
  pr2 (pr2 (is-invertible-element-is-equiv-mul-Monoid H)) =
    is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid H

  left-div-is-invertible-element-Monoid :
    is-invertible-element-Monoid M x → type-Monoid M → type-Monoid M
  left-div-is-invertible-element-Monoid H =
    mul-Monoid M (inv-is-invertible-element-Monoid M H)

  is-section-left-div-is-invertible-element-Monoid :
    (H : is-invertible-element-Monoid M x) →
    mul-Monoid M x ∘ left-div-is-invertible-element-Monoid H ~ id
  is-section-left-div-is-invertible-element-Monoid H y =
    ( inv (associative-mul-Monoid M _ _ _)) ∙
    ( ap
      ( mul-Monoid' M y)
      ( is-right-inverse-inv-is-invertible-element-Monoid M H)) ∙
    ( left-unit-law-mul-Monoid M y)

  is-retraction-left-div-is-invertible-element-Monoid :
    (H : is-invertible-element-Monoid M x) →
    left-div-is-invertible-element-Monoid H ∘ mul-Monoid M x ~ id
  is-retraction-left-div-is-invertible-element-Monoid H y =
    ( inv (associative-mul-Monoid M _ _ _)) ∙
    ( ap
      ( mul-Monoid' M y)
      ( is-left-inverse-inv-is-invertible-element-Monoid M H)) ∙
    ( left-unit-law-mul-Monoid M y)

  is-equiv-mul-is-invertible-element-Monoid :
    is-invertible-element-Monoid M x → is-equiv (mul-Monoid M x)
  is-equiv-mul-is-invertible-element-Monoid H =
    is-equiv-is-invertible
      ( left-div-is-invertible-element-Monoid H)
      ( is-section-left-div-is-invertible-element-Monoid H)
      ( is-retraction-left-div-is-invertible-element-Monoid H)
```

#### An element `x` is invertible if and only if `z ↦ zx` is an equivalence

```agda
module _
  {l : Level} (M : Monoid l) {x : type-Monoid M}
  where

  inv-is-invertible-element-is-equiv-mul-Monoid' :
    is-equiv (mul-Monoid' M x) → type-Monoid M
  inv-is-invertible-element-is-equiv-mul-Monoid' H =
    map-inv-is-equiv H (unit-Monoid M)

  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid' :
    (H : is-equiv (mul-Monoid' M x)) →
    mul-Monoid M (inv-is-invertible-element-is-equiv-mul-Monoid' H) x ＝
    unit-Monoid M
  is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid' H =
    is-section-map-inv-is-equiv H (unit-Monoid M)

  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid' :
    (H : is-equiv (mul-Monoid' M x)) →
    mul-Monoid M x (inv-is-invertible-element-is-equiv-mul-Monoid' H) ＝
    unit-Monoid M
  is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid' H =
    is-injective-is-equiv H
      ( ( associative-mul-Monoid M _ _ _) ∙
        ( ap
          ( mul-Monoid M x)
          ( is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid' H)) ∙
        ( right-unit-law-mul-Monoid M x) ∙
        ( inv (left-unit-law-mul-Monoid M x)))

  is-invertible-element-is-equiv-mul-Monoid' :
    is-equiv (mul-Monoid' M x) → is-invertible-element-Monoid M x
  pr1 (is-invertible-element-is-equiv-mul-Monoid' H) =
    inv-is-invertible-element-is-equiv-mul-Monoid' H
  pr1 (pr2 (is-invertible-element-is-equiv-mul-Monoid' H)) =
    is-right-inverse-inv-is-invertible-element-is-equiv-mul-Monoid' H
  pr2 (pr2 (is-invertible-element-is-equiv-mul-Monoid' H)) =
    is-left-inverse-inv-is-invertible-element-is-equiv-mul-Monoid' H

  right-div-is-invertible-element-Monoid :
    is-invertible-element-Monoid M x → type-Monoid M → type-Monoid M
  right-div-is-invertible-element-Monoid H =
    mul-Monoid' M (inv-is-invertible-element-Monoid M H)

  is-section-right-div-is-invertible-element-Monoid :
    (H : is-invertible-element-Monoid M x) →
    mul-Monoid' M x ∘ right-div-is-invertible-element-Monoid H ~ id
  is-section-right-div-is-invertible-element-Monoid H y =
    ( associative-mul-Monoid M _ _ _) ∙
    ( ap
      ( mul-Monoid M y)
      ( is-left-inverse-inv-is-invertible-element-Monoid M H)) ∙
    ( right-unit-law-mul-Monoid M y)

  is-retraction-right-div-is-invertible-element-Monoid :
    (H : is-invertible-element-Monoid M x) →
    right-div-is-invertible-element-Monoid H ∘ mul-Monoid' M x ~ id
  is-retraction-right-div-is-invertible-element-Monoid H y =
    ( associative-mul-Monoid M _ _ _) ∙
    ( ap
      ( mul-Monoid M y)
      ( is-right-inverse-inv-is-invertible-element-Monoid M H)) ∙
    ( right-unit-law-mul-Monoid M y)

  is-equiv-mul-is-invertible-element-Monoid' :
    is-invertible-element-Monoid M x → is-equiv (mul-Monoid' M x)
  is-equiv-mul-is-invertible-element-Monoid' H =
    is-equiv-is-invertible
      ( right-div-is-invertible-element-Monoid H)
      ( is-section-right-div-is-invertible-element-Monoid H)
      ( is-retraction-right-div-is-invertible-element-Monoid H)
```

## See also

- The core of a monoid is defined in
  [`group-theory.cores-monoids`](group-theory.cores-monoids.md).
