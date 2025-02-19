# Subsets of semirings

```agda
module ring-theory.subsets-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.semirings
```

</details>

## Idea

A subset of a semiring is a subtype of the underlying type of a semiring

## Definition

### Subsets of semirings

```agda
subset-Semiring :
  (l : Level) {l1 : Level} (R : Semiring l1) → UU (lsuc l ⊔ l1)
subset-Semiring l R = subtype l (type-Semiring R)

is-set-subset-Semiring :
  (l : Level) {l1 : Level} (R : Semiring l1) → is-set (subset-Semiring l R)
is-set-subset-Semiring l R =
  is-set-function-type is-set-type-Prop

module _
  {l1 l2 : Level} (R : Semiring l1) (S : subset-Semiring l2 R)
  where

  is-in-subset-Semiring : type-Semiring R → UU l2
  is-in-subset-Semiring = is-in-subtype S

  is-prop-is-in-subset-Semiring :
    (x : type-Semiring R) → is-prop (is-in-subset-Semiring x)
  is-prop-is-in-subset-Semiring = is-prop-is-in-subtype S

  type-subset-Semiring : UU (l1 ⊔ l2)
  type-subset-Semiring = type-subtype S

  inclusion-subset-Semiring : type-subset-Semiring → type-Semiring R
  inclusion-subset-Semiring = inclusion-subtype S

  ap-inclusion-subset-Semiring :
    (x y : type-subset-Semiring) →
    x ＝ y → (inclusion-subset-Semiring x ＝ inclusion-subset-Semiring y)
  ap-inclusion-subset-Semiring = ap-inclusion-subtype S

  is-in-subset-inclusion-subset-Semiring :
    (x : type-subset-Semiring) →
    is-in-subset-Semiring (inclusion-subset-Semiring x)
  is-in-subset-inclusion-subset-Semiring =
    is-in-subtype-inclusion-subtype S

  is-closed-under-eq-subset-Semiring :
    {x y : type-Semiring R} →
    is-in-subset-Semiring x → (x ＝ y) → is-in-subset-Semiring y
  is-closed-under-eq-subset-Semiring =
    is-closed-under-eq-subtype S

  is-closed-under-eq-subset-Semiring' :
    {x y : type-Semiring R} →
    is-in-subset-Semiring y → (x ＝ y) → is-in-subset-Semiring x
  is-closed-under-eq-subset-Semiring' =
    is-closed-under-eq-subtype' S
```

### The condition that a subset contains zero

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : subset-Semiring l2 R)
  where

  contains-zero-subset-Semiring : UU l2
  contains-zero-subset-Semiring = is-in-subtype S (zero-Semiring R)

  is-prop-contains-zero-subset-Semiring :
    is-prop contains-zero-subset-Semiring
  is-prop-contains-zero-subset-Semiring =
    is-prop-is-in-subtype S (zero-Semiring R)
```

### The condition that a subset contains one

```agda
  contains-one-subset-Semiring : UU l2
  contains-one-subset-Semiring = is-in-subtype S (one-Semiring R)

  is-prop-contains-one-subset-Semiring :
    is-prop contains-one-subset-Semiring
  is-prop-contains-one-subset-Semiring =
    is-prop-is-in-subtype S (one-Semiring R)
```

### The condition that a subset is closed under addition

```agda
  is-closed-under-addition-subset-Semiring : UU (l1 ⊔ l2)
  is-closed-under-addition-subset-Semiring =
    {x y : type-Semiring R} →
    is-in-subtype S x → is-in-subtype S y →
    is-in-subtype S (add-Semiring R x y)

  is-prop-is-closed-under-addition-subset-Semiring :
    is-prop is-closed-under-addition-subset-Semiring
  is-prop-is-closed-under-addition-subset-Semiring =
    is-prop-implicit-Π
      ( λ x →
        is-prop-implicit-Π
          ( λ y →
            is-prop-function-type
              ( is-prop-function-type (is-prop-is-in-subtype S _))))
```

### The condition that a subset is closed under multiplication

```agda
  is-closed-under-multiplication-subset-Semiring : UU (l1 ⊔ l2)
  is-closed-under-multiplication-subset-Semiring =
    (x y : type-Semiring R) → is-in-subtype S x → is-in-subtype S y →
    is-in-subtype S (mul-Semiring R x y)

  is-prop-is-closed-under-multiplication-subset-Semiring :
    is-prop is-closed-under-multiplication-subset-Semiring
  is-prop-is-closed-under-multiplication-subset-Semiring =
    is-prop-Π
      ( λ x →
        is-prop-Π
          ( λ y →
            is-prop-function-type
              ( is-prop-function-type (is-prop-is-in-subtype S _))))
```

### The condition that a subset is closed under multiplication from the left by an arbitrary element

```agda
  is-closed-under-left-multiplication-subset-Semiring : UU (l1 ⊔ l2)
  is-closed-under-left-multiplication-subset-Semiring =
    (x y : type-Semiring R) → is-in-subtype S y →
    is-in-subtype S (mul-Semiring R x y)

  is-prop-is-closed-under-left-multiplication-subset-Semiring :
    is-prop is-closed-under-left-multiplication-subset-Semiring
  is-prop-is-closed-under-left-multiplication-subset-Semiring =
    is-prop-Π
      ( λ x →
        is-prop-Π (λ y → is-prop-function-type (is-prop-is-in-subtype S _)))

  is-closed-under-left-multiplication-prop-subset-Semiring : Prop (l1 ⊔ l2)
  pr1 is-closed-under-left-multiplication-prop-subset-Semiring =
    is-closed-under-left-multiplication-subset-Semiring
  pr2 is-closed-under-left-multiplication-prop-subset-Semiring =
    is-prop-is-closed-under-left-multiplication-subset-Semiring
```

### The condition that a subset is closed under multiplication from the right by an arbitrary element

```agda
  is-closed-under-right-multiplication-subset-Semiring : UU (l1 ⊔ l2)
  is-closed-under-right-multiplication-subset-Semiring =
    (x y : type-Semiring R) → is-in-subtype S x →
    is-in-subtype S (mul-Semiring R x y)

  is-prop-is-closed-under-right-multiplication-subset-Semiring :
    is-prop is-closed-under-right-multiplication-subset-Semiring
  is-prop-is-closed-under-right-multiplication-subset-Semiring =
    is-prop-Π
      ( λ x →
        is-prop-Π (λ y → is-prop-function-type (is-prop-is-in-subtype S _)))

  is-closed-under-right-multiplication-prop-subset-Semiring : Prop (l1 ⊔ l2)
  pr1 is-closed-under-right-multiplication-prop-subset-Semiring =
    is-closed-under-right-multiplication-subset-Semiring
  pr2 is-closed-under-right-multiplication-prop-subset-Semiring =
    is-prop-is-closed-under-right-multiplication-subset-Semiring
```

### The condition that a subset of a semiring is an additive submonoid

```agda
  is-additive-submonoid-subset-Semiring : UU (l1 ⊔ l2)
  is-additive-submonoid-subset-Semiring =
    contains-zero-subset-Semiring ×
    is-closed-under-addition-subset-Semiring

  is-prop-is-additive-submonoid-subset-Semiring :
    is-prop is-additive-submonoid-subset-Semiring
  is-prop-is-additive-submonoid-subset-Semiring =
    is-prop-product
      ( is-prop-contains-zero-subset-Semiring)
      ( is-prop-is-closed-under-addition-subset-Semiring)
```
