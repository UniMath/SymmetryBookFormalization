# Ideals of semirings

```agda
module ring-theory.ideals-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.submonoids

open import ring-theory.semirings
open import ring-theory.subsets-semirings
```

</details>

## Idea

An **ideal** (resp. a **left/right ideal**) of a semiring `R` is an additive
submodule of `R` that is closed under multiplication by elements of `R` (from
the left/right).

### Note

This is the standard definition of ideals in semirings. However, such two-sided
ideals do not correspond uniquely to congruences on `R`. If we ask in addition
that the underlying additive submodule is normal, then we get unique
correspondence to congruences. We will call such ideals **normal**.

## Definitions

### Ideals of semirings

```agda
is-ideal-subset-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (P : subset-Semiring l2 R) → UU (l1 ⊔ l2)
is-ideal-subset-Semiring R P =
  is-additive-submonoid-subset-Semiring R P ×
  ( is-closed-under-left-multiplication-subset-Semiring R P ×
    is-closed-under-right-multiplication-subset-Semiring R P)

is-prop-is-ideal-subset-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (P : subset-Semiring l2 R) →
  is-prop (is-ideal-subset-Semiring R P)
is-prop-is-ideal-subset-Semiring R P =
  is-prop-product
    ( is-prop-is-additive-submonoid-subset-Semiring R P)
    ( is-prop-product
      ( is-prop-is-closed-under-left-multiplication-subset-Semiring R P)
      ( is-prop-is-closed-under-right-multiplication-subset-Semiring R P))

ideal-Semiring :
  (l : Level) {l1 : Level} (R : Semiring l1) → UU (lsuc l ⊔ l1)
ideal-Semiring l R =
  Σ (subset-Semiring l R) (is-ideal-subset-Semiring R)

module _
  {l1 l2 : Level} (R : Semiring l1) (I : ideal-Semiring l2 R)
  where

  subset-ideal-Semiring : subset-Semiring l2 R
  subset-ideal-Semiring = pr1 I

  is-ideal-ideal-Semiring :
    is-ideal-subset-Semiring R subset-ideal-Semiring
  is-ideal-ideal-Semiring = pr2 I

  is-in-ideal-Semiring : type-Semiring R → UU l2
  is-in-ideal-Semiring =
    is-in-subset-Semiring R subset-ideal-Semiring

  is-prop-is-in-ideal-Semiring :
    (x : type-Semiring R) → is-prop (is-in-ideal-Semiring x)
  is-prop-is-in-ideal-Semiring =
    is-prop-is-in-subset-Semiring R subset-ideal-Semiring

  type-ideal-Semiring : UU (l1 ⊔ l2)
  type-ideal-Semiring =
    type-subset-Semiring R subset-ideal-Semiring

  inclusion-ideal-Semiring :
    type-ideal-Semiring → type-Semiring R
  inclusion-ideal-Semiring =
    inclusion-subset-Semiring R subset-ideal-Semiring

  ap-inclusion-ideal-Semiring :
    (x y : type-ideal-Semiring) → x ＝ y →
    inclusion-ideal-Semiring x ＝ inclusion-ideal-Semiring y
  ap-inclusion-ideal-Semiring =
    ap-inclusion-subset-Semiring R subset-ideal-Semiring

  is-in-subset-inclusion-ideal-Semiring :
    (x : type-ideal-Semiring) →
    is-in-ideal-Semiring (inclusion-ideal-Semiring x)
  is-in-subset-inclusion-ideal-Semiring =
    is-in-subset-inclusion-subset-Semiring R subset-ideal-Semiring

  is-closed-under-eq-ideal-Semiring :
    {x y : type-Semiring R} → is-in-ideal-Semiring x →
    (x ＝ y) → is-in-ideal-Semiring y
  is-closed-under-eq-ideal-Semiring =
    is-closed-under-eq-subset-Semiring R subset-ideal-Semiring

  is-closed-under-eq-ideal-Semiring' :
    {x y : type-Semiring R} → is-in-ideal-Semiring y →
    (x ＝ y) → is-in-ideal-Semiring x
  is-closed-under-eq-ideal-Semiring' =
    is-closed-under-eq-subset-Semiring' R subset-ideal-Semiring

  is-ideal-subset-ideal-Semiring :
    is-ideal-subset-Semiring R subset-ideal-Semiring
  is-ideal-subset-ideal-Semiring = pr2 I

  is-additive-submonoid-ideal-Semiring :
    is-additive-submonoid-subset-Semiring R subset-ideal-Semiring
  is-additive-submonoid-ideal-Semiring =
    pr1 is-ideal-subset-ideal-Semiring

  contains-zero-ideal-Semiring :
    is-in-ideal-Semiring (zero-Semiring R)
  contains-zero-ideal-Semiring =
    pr1 is-additive-submonoid-ideal-Semiring

  is-closed-under-addition-ideal-Semiring :
    is-closed-under-addition-subset-Semiring R subset-ideal-Semiring
  is-closed-under-addition-ideal-Semiring =
    pr2 is-additive-submonoid-ideal-Semiring

  is-closed-under-left-multiplication-ideal-Semiring :
    is-closed-under-left-multiplication-subset-Semiring R subset-ideal-Semiring
  is-closed-under-left-multiplication-ideal-Semiring =
    pr1 (pr2 is-ideal-subset-ideal-Semiring)

  is-closed-under-right-multiplication-ideal-Semiring :
    is-closed-under-right-multiplication-subset-Semiring R subset-ideal-Semiring
  is-closed-under-right-multiplication-ideal-Semiring =
    pr2 (pr2 is-ideal-subset-ideal-Semiring)

  submonoid-ideal-Semiring : Submonoid l2 (additive-monoid-Semiring R)
  pr1 submonoid-ideal-Semiring = subset-ideal-Semiring
  pr1 (pr2 submonoid-ideal-Semiring) = contains-zero-ideal-Semiring
  pr2 (pr2 submonoid-ideal-Semiring) = is-closed-under-addition-ideal-Semiring
```

## Properties

### Characterizing equality of ideals in semirings

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) (I : ideal-Semiring l2 R)
  where

  has-same-elements-ideal-Semiring :
    (J : ideal-Semiring l3 R) → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-ideal-Semiring J =
    has-same-elements-subtype
      ( subset-ideal-Semiring R I)
      ( subset-ideal-Semiring R J)

module _
  {l1 l2 : Level} (R : Semiring l1) (I : ideal-Semiring l2 R)
  where

  refl-has-same-elements-ideal-Semiring :
    has-same-elements-ideal-Semiring R I I
  refl-has-same-elements-ideal-Semiring =
    refl-has-same-elements-subtype (subset-ideal-Semiring R I)

  is-torsorial-has-same-elements-ideal-Semiring :
    is-torsorial (has-same-elements-ideal-Semiring R I)
  is-torsorial-has-same-elements-ideal-Semiring =
    is-torsorial-Eq-subtype
      ( is-torsorial-has-same-elements-subtype (subset-ideal-Semiring R I))
      ( is-prop-is-ideal-subset-Semiring R)
      ( subset-ideal-Semiring R I)
      ( refl-has-same-elements-ideal-Semiring)
      ( is-ideal-ideal-Semiring R I)

  has-same-elements-eq-ideal-Semiring :
    (J : ideal-Semiring l2 R) →
    (I ＝ J) → has-same-elements-ideal-Semiring R I J
  has-same-elements-eq-ideal-Semiring .I refl =
    refl-has-same-elements-ideal-Semiring

  is-equiv-has-same-elements-eq-ideal-Semiring :
    (J : ideal-Semiring l2 R) → is-equiv (has-same-elements-eq-ideal-Semiring J)
  is-equiv-has-same-elements-eq-ideal-Semiring =
    fundamental-theorem-id
      is-torsorial-has-same-elements-ideal-Semiring
      has-same-elements-eq-ideal-Semiring

  extensionality-ideal-Semiring :
    (J : ideal-Semiring l2 R) →
    (I ＝ J) ≃ has-same-elements-ideal-Semiring R I J
  pr1 (extensionality-ideal-Semiring J) =
    has-same-elements-eq-ideal-Semiring J
  pr2 (extensionality-ideal-Semiring J) =
    is-equiv-has-same-elements-eq-ideal-Semiring J

  eq-has-same-elements-ideal-Semiring :
    (J : ideal-Semiring l2 R) → has-same-elements-ideal-Semiring R I J → I ＝ J
  eq-has-same-elements-ideal-Semiring J =
    map-inv-equiv (extensionality-ideal-Semiring J)
```
