# Commutative monoids

```agda
module group-theory.commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.interchange-law
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.sets
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.monoids
open import group-theory.semigroups

open import structured-types.magmas
```

</details>

## Idea

A
{{#concept "commutative monoid" WDID=Q19934355 WD="commutative monoid" Agda=Commutative-Monoid}}
is a [monoid](group-theory.monoids.md) `M` in which `xy = yx` holds for all
`x y : M`.

## Definitions

### The predicate on monoids of being commutative

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-commutative-Monoid : UU l
  is-commutative-Monoid =
    (x y : type-Monoid M) → mul-Monoid M x y ＝ mul-Monoid M y x

  is-prop-is-commutative-Monoid : is-prop is-commutative-Monoid
  is-prop-is-commutative-Monoid =
    is-prop-iterated-Π 2
      ( λ x y → is-set-type-Monoid M (mul-Monoid M x y) (mul-Monoid M y x))

  is-commutative-prop-Monoid : Prop l
  is-commutative-prop-Monoid =
    ( is-commutative-Monoid , is-prop-is-commutative-Monoid)
```

### Commutative monoids

```agda
Commutative-Monoid : (l : Level) → UU (lsuc l)
Commutative-Monoid l = Σ (Monoid l) is-commutative-Monoid

module _
  {l : Level} (M : Commutative-Monoid l)
  where

  monoid-Commutative-Monoid : Monoid l
  monoid-Commutative-Monoid = pr1 M

  unital-magma-Commutative-Monoid : Unital-Magma l
  unital-magma-Commutative-Monoid =
    unital-magma-Monoid monoid-Commutative-Monoid

  semigroup-Commutative-Monoid : Semigroup l
  semigroup-Commutative-Monoid = semigroup-Monoid monoid-Commutative-Monoid

  set-Commutative-Monoid : Set l
  set-Commutative-Monoid = set-Monoid monoid-Commutative-Monoid

  type-Commutative-Monoid : UU l
  type-Commutative-Monoid = type-Monoid monoid-Commutative-Monoid

  is-set-type-Commutative-Monoid : is-set type-Commutative-Monoid
  is-set-type-Commutative-Monoid = is-set-type-Monoid monoid-Commutative-Monoid
```

### The multiplicative operation of a commutative monoid

```agda
  has-associative-mul-Commutative-Monoid :
    has-associative-mul-Set set-Commutative-Monoid
  has-associative-mul-Commutative-Monoid =
    has-associative-mul-Semigroup semigroup-Commutative-Monoid

  mul-Commutative-Monoid :
    (x y : type-Commutative-Monoid) → type-Commutative-Monoid
  mul-Commutative-Monoid = mul-Monoid monoid-Commutative-Monoid

  mul-Commutative-Monoid' :
    (x y : type-Commutative-Monoid) → type-Commutative-Monoid
  mul-Commutative-Monoid' =
    mul-Monoid' monoid-Commutative-Monoid

  ap-mul-Commutative-Monoid :
    {x x' y y' : type-Commutative-Monoid} →
    x ＝ x' → y ＝ y' →
    mul-Commutative-Monoid x y ＝ mul-Commutative-Monoid x' y'
  ap-mul-Commutative-Monoid =
    ap-mul-Monoid monoid-Commutative-Monoid

  associative-mul-Commutative-Monoid :
    (x y z : type-Commutative-Monoid) →
    ( mul-Commutative-Monoid (mul-Commutative-Monoid x y) z) ＝
    ( mul-Commutative-Monoid x (mul-Commutative-Monoid y z))
  associative-mul-Commutative-Monoid =
    associative-mul-Monoid monoid-Commutative-Monoid

  commutative-mul-Commutative-Monoid :
    (x y : type-Commutative-Monoid) →
    mul-Commutative-Monoid x y ＝ mul-Commutative-Monoid y x
  commutative-mul-Commutative-Monoid = pr2 M

  interchange-mul-mul-Commutative-Monoid :
    (x y x' y' : type-Commutative-Monoid) →
    ( mul-Commutative-Monoid
      ( mul-Commutative-Monoid x y)
      ( mul-Commutative-Monoid x' y')) ＝
    ( mul-Commutative-Monoid
      ( mul-Commutative-Monoid x x')
      ( mul-Commutative-Monoid y y'))
  interchange-mul-mul-Commutative-Monoid =
    interchange-law-commutative-and-associative
      mul-Commutative-Monoid
      commutative-mul-Commutative-Monoid
      associative-mul-Commutative-Monoid

  right-swap-mul-Commutative-Monoid :
    (x y z : type-Commutative-Monoid) →
    mul-Commutative-Monoid (mul-Commutative-Monoid x y) z ＝
    mul-Commutative-Monoid (mul-Commutative-Monoid x z) y
  right-swap-mul-Commutative-Monoid x y z =
    ( associative-mul-Commutative-Monoid x y z) ∙
    ( ap
      ( mul-Commutative-Monoid x)
      ( commutative-mul-Commutative-Monoid y z)) ∙
    ( inv (associative-mul-Commutative-Monoid x z y))

  left-swap-mul-Commutative-Monoid :
    (x y z : type-Commutative-Monoid) →
    mul-Commutative-Monoid x (mul-Commutative-Monoid y z) ＝
    mul-Commutative-Monoid y (mul-Commutative-Monoid x z)
  left-swap-mul-Commutative-Monoid x y z =
    ( inv (associative-mul-Commutative-Monoid x y z)) ∙
    ( ap
      ( mul-Commutative-Monoid' z)
      ( commutative-mul-Commutative-Monoid x y)) ∙
    ( associative-mul-Commutative-Monoid y x z)
```

### The unit element of a commutative monoid

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  has-unit-Commutative-Monoid : is-unital (mul-Commutative-Monoid M)
  has-unit-Commutative-Monoid =
    has-unit-Monoid (monoid-Commutative-Monoid M)

  unit-Commutative-Monoid : type-Commutative-Monoid M
  unit-Commutative-Monoid = unit-Monoid (monoid-Commutative-Monoid M)

  left-unit-law-mul-Commutative-Monoid :
    (x : type-Commutative-Monoid M) →
    mul-Commutative-Monoid M unit-Commutative-Monoid x ＝ x
  left-unit-law-mul-Commutative-Monoid =
    left-unit-law-mul-Monoid (monoid-Commutative-Monoid M)

  right-unit-law-mul-Commutative-Monoid :
    (x : type-Commutative-Monoid M) →
    mul-Commutative-Monoid M x unit-Commutative-Monoid ＝ x
  right-unit-law-mul-Commutative-Monoid =
    right-unit-law-mul-Monoid (monoid-Commutative-Monoid M)

  is-unit-Commutative-Monoid : type-Commutative-Monoid M → UU l
  is-unit-Commutative-Monoid x = Id x unit-Commutative-Monoid

  is-unit-prop-Commutative-Monoid : type-Commutative-Monoid M → Prop l
  is-unit-prop-Commutative-Monoid x =
    Id-Prop (set-Commutative-Monoid M) x unit-Commutative-Monoid
```
