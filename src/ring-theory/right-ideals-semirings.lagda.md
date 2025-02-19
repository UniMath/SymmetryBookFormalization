# Right ideals of semirings

```agda
module ring-theory.right-ideals-semirings where
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

open import ring-theory.semirings
open import ring-theory.subsets-semirings
```

</details>

## Idea

A {{#concept "right ideal" Disambiguation="semiring" Agda=right-ideal-Semiring}}
in a [semiring](ring-theory.semirings.md) `R` is a right submodule of `R`.

## Definitions

### Right ideals

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  is-right-ideal-subset-Semiring :
    {l2 : Level} → subset-Semiring l2 R → UU (l1 ⊔ l2)
  is-right-ideal-subset-Semiring P =
    is-additive-submonoid-subset-Semiring R P ×
    is-closed-under-right-multiplication-subset-Semiring R P

  is-prop-is-right-ideal-subset-Semiring :
    {l2 : Level} (S : subset-Semiring l2 R) →
    is-prop (is-right-ideal-subset-Semiring S)
  is-prop-is-right-ideal-subset-Semiring S =
    is-prop-product
      ( is-prop-is-additive-submonoid-subset-Semiring R S)
      ( is-prop-is-closed-under-right-multiplication-subset-Semiring R S)

right-ideal-Semiring :
  (l : Level) {l1 : Level} (R : Semiring l1) → UU (lsuc l ⊔ l1)
right-ideal-Semiring l R =
  Σ (subset-Semiring l R) (is-right-ideal-subset-Semiring R)

module _
  {l1 l2 : Level} (R : Semiring l1) (I : right-ideal-Semiring l2 R)
  where

  subset-right-ideal-Semiring : subset-Semiring l2 R
  subset-right-ideal-Semiring = pr1 I

  is-in-right-ideal-Semiring : type-Semiring R → UU l2
  is-in-right-ideal-Semiring x = type-Prop (subset-right-ideal-Semiring x)

  type-right-ideal-Semiring : UU (l1 ⊔ l2)
  type-right-ideal-Semiring = type-subset-Semiring R subset-right-ideal-Semiring

  inclusion-right-ideal-Semiring :
    type-right-ideal-Semiring → type-Semiring R
  inclusion-right-ideal-Semiring =
    inclusion-subset-Semiring R subset-right-ideal-Semiring

  ap-inclusion-right-ideal-Semiring :
    (x y : type-right-ideal-Semiring) → x ＝ y →
    inclusion-right-ideal-Semiring x ＝ inclusion-right-ideal-Semiring y
  ap-inclusion-right-ideal-Semiring =
    ap-inclusion-subset-Semiring R subset-right-ideal-Semiring

  is-in-subset-inclusion-right-ideal-Semiring :
    (x : type-right-ideal-Semiring) →
    is-in-right-ideal-Semiring (inclusion-right-ideal-Semiring x)
  is-in-subset-inclusion-right-ideal-Semiring =
    is-in-subset-inclusion-subset-Semiring R subset-right-ideal-Semiring

  is-closed-under-eq-right-ideal-Semiring :
    {x y : type-Semiring R} → is-in-right-ideal-Semiring x →
    (x ＝ y) → is-in-right-ideal-Semiring y
  is-closed-under-eq-right-ideal-Semiring =
    is-closed-under-eq-subset-Semiring R subset-right-ideal-Semiring

  is-closed-under-eq-right-ideal-Semiring' :
    {x y : type-Semiring R} → is-in-right-ideal-Semiring y →
    (x ＝ y) → is-in-right-ideal-Semiring x
  is-closed-under-eq-right-ideal-Semiring' =
    is-closed-under-eq-subset-Semiring' R subset-right-ideal-Semiring

  is-right-ideal-subset-right-ideal-Semiring :
    is-right-ideal-subset-Semiring R subset-right-ideal-Semiring
  is-right-ideal-subset-right-ideal-Semiring = pr2 I

  is-additive-submonoid-subset-right-ideal-Semiring :
    is-additive-submonoid-subset-Semiring R subset-right-ideal-Semiring
  is-additive-submonoid-subset-right-ideal-Semiring =
    pr1 is-right-ideal-subset-right-ideal-Semiring

  contains-zero-right-ideal-Semiring :
    is-in-right-ideal-Semiring (zero-Semiring R)
  contains-zero-right-ideal-Semiring =
    pr1 is-additive-submonoid-subset-right-ideal-Semiring

  is-closed-under-addition-right-ideal-Semiring :
    is-closed-under-addition-subset-Semiring R subset-right-ideal-Semiring
  is-closed-under-addition-right-ideal-Semiring =
    pr2 is-additive-submonoid-subset-right-ideal-Semiring

  is-closed-under-right-multiplication-right-ideal-Semiring :
    is-closed-under-right-multiplication-subset-Semiring R
      subset-right-ideal-Semiring
  is-closed-under-right-multiplication-right-ideal-Semiring =
    pr2 is-right-ideal-subset-right-ideal-Semiring

  is-right-ideal-right-ideal-Semiring :
    is-right-ideal-subset-Semiring R subset-right-ideal-Semiring
  is-right-ideal-right-ideal-Semiring = pr2 I
```

## Properties

### Characterizing equality of right ideals in semirings

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) (I : right-ideal-Semiring l2 R)
  where

  has-same-elements-right-ideal-Semiring :
    (J : right-ideal-Semiring l3 R) → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-right-ideal-Semiring J =
    has-same-elements-subtype
      ( subset-right-ideal-Semiring R I)
      ( subset-right-ideal-Semiring R J)

module _
  {l1 l2 : Level} (R : Semiring l1) (I : right-ideal-Semiring l2 R)
  where

  refl-has-same-elements-right-ideal-Semiring :
    has-same-elements-right-ideal-Semiring R I I
  refl-has-same-elements-right-ideal-Semiring =
    refl-has-same-elements-subtype (subset-right-ideal-Semiring R I)

  is-torsorial-has-same-elements-right-ideal-Semiring :
    is-torsorial (has-same-elements-right-ideal-Semiring R I)
  is-torsorial-has-same-elements-right-ideal-Semiring =
    is-torsorial-Eq-subtype
      ( is-torsorial-has-same-elements-subtype
        ( subset-right-ideal-Semiring R I))
      ( is-prop-is-right-ideal-subset-Semiring R)
      ( subset-right-ideal-Semiring R I)
      ( refl-has-same-elements-right-ideal-Semiring)
      ( is-right-ideal-right-ideal-Semiring R I)

  has-same-elements-eq-right-ideal-Semiring :
    (J : right-ideal-Semiring l2 R) →
    (I ＝ J) → has-same-elements-right-ideal-Semiring R I J
  has-same-elements-eq-right-ideal-Semiring .I refl =
    refl-has-same-elements-right-ideal-Semiring

  is-equiv-has-same-elements-eq-right-ideal-Semiring :
    (J : right-ideal-Semiring l2 R) →
    is-equiv (has-same-elements-eq-right-ideal-Semiring J)
  is-equiv-has-same-elements-eq-right-ideal-Semiring =
    fundamental-theorem-id
      is-torsorial-has-same-elements-right-ideal-Semiring
      has-same-elements-eq-right-ideal-Semiring

  extensionality-right-ideal-Semiring :
    (J : right-ideal-Semiring l2 R) →
    (I ＝ J) ≃ has-same-elements-right-ideal-Semiring R I J
  pr1 (extensionality-right-ideal-Semiring J) =
    has-same-elements-eq-right-ideal-Semiring J
  pr2 (extensionality-right-ideal-Semiring J) =
    is-equiv-has-same-elements-eq-right-ideal-Semiring J

  eq-has-same-elements-right-ideal-Semiring :
    (J : right-ideal-Semiring l2 R) →
    has-same-elements-right-ideal-Semiring R I J → I ＝ J
  eq-has-same-elements-right-ideal-Semiring J =
    map-inv-equiv (extensionality-right-ideal-Semiring J)
```
