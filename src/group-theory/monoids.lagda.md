# Monoids

```agda
module group-theory.monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.unit-type
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.semigroups

open import structured-types.magmas
open import structured-types.h-spaces
open import structured-types.wild-monoids
```

</details>

## Idea

{{#concept "Monoids" WDID=Q208237 WD="monoid" Agda=Monoid}} are
[unital](foundation.unital-binary-operations.md)
[semigroups](group-theory.semigroups.md).

## Definition

```agda
is-unital-Semigroup :
  {l : Level} → Semigroup l → UU l
is-unital-Semigroup G = is-unital (mul-Semigroup G)

Monoid :
  (l : Level) → UU (lsuc l)
Monoid l = Σ (Semigroup l) is-unital-Semigroup

module _
  {l : Level} (M : Monoid l)
  where

  semigroup-Monoid : Semigroup l
  semigroup-Monoid = pr1 M

  magma-Monoid : Magma l
  magma-Monoid = magma-Semigroup semigroup-Monoid

  is-unital-Monoid : is-unital-Semigroup semigroup-Monoid
  is-unital-Monoid = pr2 M

  type-Monoid : UU l
  type-Monoid = type-Semigroup semigroup-Monoid

  set-Monoid : Set l
  set-Monoid = set-Semigroup semigroup-Monoid

  is-set-type-Monoid : is-set type-Monoid
  is-set-type-Monoid = is-set-type-Semigroup semigroup-Monoid

  mul-Monoid : type-Monoid → type-Monoid → type-Monoid
  mul-Monoid = mul-Semigroup semigroup-Monoid

  mul-Monoid' : type-Monoid → type-Monoid → type-Monoid
  mul-Monoid' y x = mul-Monoid x y

  ap-mul-Monoid :
    {x x' y y' : type-Monoid} →
    x ＝ x' → y ＝ y' → mul-Monoid x y ＝ mul-Monoid x' y'
  ap-mul-Monoid = ap-mul-Semigroup semigroup-Monoid

  associative-mul-Monoid :
    (x y z : type-Monoid) →
    mul-Monoid (mul-Monoid x y) z ＝ mul-Monoid x (mul-Monoid y z)
  associative-mul-Monoid = associative-mul-Semigroup semigroup-Monoid

  has-unit-Monoid : is-unital mul-Monoid
  has-unit-Monoid = pr2 M

  unit-Monoid : type-Monoid
  unit-Monoid = pr1 has-unit-Monoid

  is-unit-Monoid-Prop : type-Monoid → Prop l
  is-unit-Monoid-Prop x = Id-Prop set-Monoid x unit-Monoid

  is-unit-Monoid : type-Monoid → UU l
  is-unit-Monoid x = x ＝ unit-Monoid

  left-unit-law-mul-Monoid : (x : type-Monoid) → mul-Monoid unit-Monoid x ＝ x
  left-unit-law-mul-Monoid = pr1 (pr2 has-unit-Monoid)

  right-unit-law-mul-Monoid : (x : type-Monoid) → mul-Monoid x unit-Monoid ＝ x
  right-unit-law-mul-Monoid = pr2 (pr2 has-unit-Monoid)

  unital-magma-Monoid : Unital-Magma l
  pr1 unital-magma-Monoid = magma-Monoid
  pr2 unital-magma-Monoid = has-unit-Monoid

  left-swap-mul-Monoid :
    {x y z : type-Monoid} → mul-Monoid x y ＝ mul-Monoid y x →
    mul-Monoid x (mul-Monoid y z) ＝
    mul-Monoid y (mul-Monoid x z)
  left-swap-mul-Monoid =
    left-swap-mul-Semigroup semigroup-Monoid

  right-swap-mul-Monoid :
    {x y z : type-Monoid} → mul-Monoid y z ＝ mul-Monoid z y →
    mul-Monoid (mul-Monoid x y) z ＝
    mul-Monoid (mul-Monoid x z) y
  right-swap-mul-Monoid =
    right-swap-mul-Semigroup semigroup-Monoid

  interchange-mul-mul-Monoid :
    {x y z w : type-Monoid} → mul-Monoid y z ＝ mul-Monoid z y →
    mul-Monoid (mul-Monoid x y) (mul-Monoid z w) ＝
    mul-Monoid (mul-Monoid x z) (mul-Monoid y w)
  interchange-mul-mul-Monoid =
    interchange-mul-mul-Semigroup semigroup-Monoid
```

## Properties

### For any semigroup `G`, being unital is a property

```agda
abstract
  all-elements-equal-is-unital-Semigroup :
    {l : Level} (G : Semigroup l) → all-elements-equal (is-unital-Semigroup G)
  all-elements-equal-is-unital-Semigroup
    ( X , μ , associative-μ)
    ( e , left-unit-e , right-unit-e)
    ( e' , left-unit-e' , right-unit-e') =
    eq-type-subtype
      ( λ e →
        product-Prop
          ( Π-Prop (type-Set X) (λ y → Id-Prop X (μ e y) y))
          ( Π-Prop (type-Set X) (λ x → Id-Prop X (μ x e) x)))
      ( (inv (left-unit-e' e)) ∙ (right-unit-e e'))

abstract
  is-prop-is-unital-Semigroup :
    {l : Level} (G : Semigroup l) → is-prop (is-unital-Semigroup G)
  is-prop-is-unital-Semigroup G =
    is-prop-all-elements-equal (all-elements-equal-is-unital-Semigroup G)

is-unital-prop-Semigroup : {l : Level} (G : Semigroup l) → Prop l
pr1 (is-unital-prop-Semigroup G) = is-unital-Semigroup G
pr2 (is-unital-prop-Semigroup G) = is-prop-is-unital-Semigroup G
```

### Monoids are H-spaces

```agda
h-space-Monoid : {l : Level} (M : Monoid l) → H-Space l
pr1 (pr1 (h-space-Monoid M)) = type-Monoid M
pr2 (pr1 (h-space-Monoid M)) = unit-Monoid M
pr1 (pr2 (h-space-Monoid M)) = mul-Monoid M
pr1 (pr2 (pr2 (h-space-Monoid M))) = left-unit-law-mul-Monoid M
pr1 (pr2 (pr2 (pr2 (h-space-Monoid M)))) = right-unit-law-mul-Monoid M
pr2 (pr2 (pr2 (pr2 (h-space-Monoid M)))) =
  eq-is-prop (is-set-type-Monoid M _ _)
```

### Monoids are wild monoids

```agda
wild-monoid-Monoid : {l : Level} (M : Monoid l) → Wild-Monoid l
pr1 (wild-monoid-Monoid M) = h-space-Monoid M
pr1 (pr2 (wild-monoid-Monoid M)) = associative-mul-Monoid M
pr1 (pr2 (pr2 (wild-monoid-Monoid M))) y z =
  eq-is-prop (is-set-type-Monoid M _ _)
pr1 (pr2 (pr2 (pr2 (wild-monoid-Monoid M)))) x z =
  eq-is-prop (is-set-type-Monoid M _ _)
pr1 (pr2 (pr2 (pr2 (pr2 (wild-monoid-Monoid M))))) x y =
  eq-is-prop (is-set-type-Monoid M _ _)
pr2 (pr2 (pr2 (pr2 (pr2 (wild-monoid-Monoid M))))) = star
```

## See also

- In [one object precategories](category-theory.one-object-precategories.md), we
  show that monoids are precategories whose type of objects is contractible.
