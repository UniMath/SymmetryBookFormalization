# Magmas

```agda
module structured-types.magmas where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "magma" Agda=Magma}} is a type [equipped](foundation.structure.md)
with a binary operation.

## Definition

```agda
Magma : (l : Level) → UU (lsuc l)
Magma l = Σ (UU l) (λ A → A → A → A)

module _
  {l : Level} (M : Magma l)
  where

  type-Magma : UU l
  type-Magma = pr1 M

  mul-Magma : type-Magma → type-Magma → type-Magma
  mul-Magma = pr2 M

  mul-Magma' : type-Magma → type-Magma → type-Magma
  mul-Magma' x y = mul-Magma y x
```

## Structures

### Unital magmas

```agda
is-unital-Magma : {l : Level} (M : Magma l) → UU l
is-unital-Magma M = is-unital (mul-Magma M)

Unital-Magma : (l : Level) → UU (lsuc l)
Unital-Magma l = Σ (Magma l) is-unital-Magma

module _
  {l : Level} (M : Unital-Magma l)
  where

  magma-Unital-Magma : Magma l
  magma-Unital-Magma = pr1 M

  type-Unital-Magma :
    UU l
  type-Unital-Magma =
    type-Magma magma-Unital-Magma

  mul-Unital-Magma :
    (x y : type-Unital-Magma) → type-Unital-Magma
  mul-Unital-Magma =
    mul-Magma magma-Unital-Magma

  is-unital-magma-Unital-Magma :
    is-unital-Magma magma-Unital-Magma
  is-unital-magma-Unital-Magma = pr2 M

  unit-Unital-Magma :
    type-Unital-Magma
  unit-Unital-Magma =
    pr1 is-unital-magma-Unital-Magma

  left-unit-law-mul-Unital-Magma :
    (x : type-Unital-Magma) → mul-Unital-Magma unit-Unital-Magma x ＝ x
  left-unit-law-mul-Unital-Magma =
    pr1 (pr2 is-unital-magma-Unital-Magma)

  right-unit-law-mul-Unital-Magma :
    (x : type-Unital-Magma) → mul-Unital-Magma x unit-Unital-Magma ＝ x
  right-unit-law-mul-Unital-Magma =
    pr2 (pr2 is-unital-magma-Unital-Magma)
```

### Semigroups

```agda
is-semigroup-Magma : {l : Level} → Magma l → UU l
is-semigroup-Magma M =
  (x y z : type-Magma M) →
  Id (mul-Magma M (mul-Magma M x y) z) (mul-Magma M x (mul-Magma M y z))
```

### Commutative magmas

```agda
is-commutative-Magma : {l : Level} → Magma l → UU l
is-commutative-Magma M =
  (x y : type-Magma M) → Id (mul-Magma M x y) (mul-Magma M y x)
```

### The structure of a commutative monoid on magmas

```agda
is-commutative-monoid-Magma : {l : Level} → Magma l → UU l
is-commutative-monoid-Magma M =
  ((is-semigroup-Magma M) × (is-unital-Magma M)) × (is-commutative-Magma M)

unit-is-commutative-monoid-Magma :
  {l : Level} (M : Magma l) → is-commutative-monoid-Magma M → type-Magma M
unit-is-commutative-monoid-Magma M H = pr1 (pr2 (pr1 H))
```
