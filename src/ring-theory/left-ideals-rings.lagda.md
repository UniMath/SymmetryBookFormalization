# Left ideals of rings

```agda
module ring-theory.left-ideals-rings where
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

open import ring-theory.left-ideals-semirings
open import ring-theory.rings
open import ring-theory.subsets-rings
```

</details>

## Idea

A {{#concept "left ideal" Disambiguation="rings" Agda=left-ideal-Ring}} in a [ring](ring-theory.rings.md) `R` is a left submodule of
`R`.

## Definitions

### Left ideals

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  is-left-ideal-subset-Ring :
    {l2 : Level} → subset-Ring l2 R → UU (l1 ⊔ l2)
  is-left-ideal-subset-Ring =
    is-left-ideal-subset-Semiring (semiring-Ring R)

  is-prop-is-left-ideal-subset-Ring :
    {l2 : Level} (S : subset-Ring l2 R) → is-prop (is-left-ideal-subset-Ring S)
  is-prop-is-left-ideal-subset-Ring =
    is-prop-is-left-ideal-subset-Semiring (semiring-Ring R)

left-ideal-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU (lsuc l ⊔ l1)
left-ideal-Ring l R =
  left-ideal-Semiring l (semiring-Ring R)

module _
  {l1 l2 : Level} (R : Ring l1) (I : left-ideal-Ring l2 R)
  where

  subset-left-ideal-Ring : subset-Ring l2 R
  subset-left-ideal-Ring =
    subset-left-ideal-Semiring (semiring-Ring R) I

  is-in-left-ideal-Ring : type-Ring R → UU l2
  is-in-left-ideal-Ring =
    is-in-left-ideal-Semiring (semiring-Ring R) I

  type-left-ideal-Ring : UU (l1 ⊔ l2)
  type-left-ideal-Ring = type-subset-Ring R subset-left-ideal-Ring

  inclusion-left-ideal-Ring : type-left-ideal-Ring → type-Ring R
  inclusion-left-ideal-Ring =
    inclusion-left-ideal-Semiring (semiring-Ring R) I

  ap-inclusion-left-ideal-Ring :
    (x y : type-left-ideal-Ring) → x ＝ y →
    inclusion-left-ideal-Ring x ＝ inclusion-left-ideal-Ring y
  ap-inclusion-left-ideal-Ring =
    ap-inclusion-left-ideal-Semiring (semiring-Ring R) I

  is-in-subset-inclusion-left-ideal-Ring :
    (x : type-left-ideal-Ring) →
    is-in-left-ideal-Ring (inclusion-left-ideal-Ring x)
  is-in-subset-inclusion-left-ideal-Ring =
    is-in-subset-inclusion-left-ideal-Semiring (semiring-Ring R) I

  is-closed-under-eq-left-ideal-Ring :
    {x y : type-Ring R} → is-in-left-ideal-Ring x →
    (x ＝ y) → is-in-left-ideal-Ring y
  is-closed-under-eq-left-ideal-Ring =
    is-closed-under-eq-left-ideal-Semiring (semiring-Ring R) I

  is-closed-under-eq-left-ideal-Ring' :
    {x y : type-Ring R} → is-in-left-ideal-Ring y →
    (x ＝ y) → is-in-left-ideal-Ring x
  is-closed-under-eq-left-ideal-Ring' =
    is-closed-under-eq-left-ideal-Semiring' (semiring-Ring R) I

  is-left-ideal-subset-left-ideal-Ring :
    is-left-ideal-subset-Ring R subset-left-ideal-Ring
  is-left-ideal-subset-left-ideal-Ring =
    is-left-ideal-subset-left-ideal-Semiring (semiring-Ring R) I

  is-additive-submonoid-subset-left-ideal-Ring :
    is-additive-submonoid-subset-Ring R subset-left-ideal-Ring
  is-additive-submonoid-subset-left-ideal-Ring =
    is-additive-submonoid-subset-left-ideal-Semiring (semiring-Ring R) I

  contains-zero-left-ideal-Ring : is-in-left-ideal-Ring (zero-Ring R)
  contains-zero-left-ideal-Ring =
    contains-zero-left-ideal-Semiring (semiring-Ring R) I

  is-closed-under-addition-left-ideal-Ring :
    is-closed-under-addition-subset-Ring R subset-left-ideal-Ring
  is-closed-under-addition-left-ideal-Ring =
    is-closed-under-addition-left-ideal-Semiring (semiring-Ring R) I

  is-closed-under-left-multiplication-left-ideal-Ring :
    is-closed-under-left-multiplication-subset-Ring R subset-left-ideal-Ring
  is-closed-under-left-multiplication-left-ideal-Ring =
    is-closed-under-left-multiplication-left-ideal-Semiring (semiring-Ring R) I

  is-additive-subgroup-left-ideal-Ring :
    is-additive-subgroup-subset-Ring R subset-left-ideal-Ring
  is-additive-subgroup-left-ideal-Ring =
    is-additive-subgroup-is-closed-under-left-multiplication-subset-Ring
      ( R)
      ( subset-left-ideal-Ring)
      ( is-additive-submonoid-subset-left-ideal-Ring)
      ( is-closed-under-left-multiplication-left-ideal-Ring)

  is-left-ideal-left-ideal-Ring :
    is-left-ideal-subset-Ring R subset-left-ideal-Ring
  is-left-ideal-left-ideal-Ring =
    is-left-ideal-left-ideal-Semiring (semiring-Ring R) I
```

## Properties

### Characterizing equality of left ideals in rings

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1) (I : left-ideal-Ring l2 R)
  where

  has-same-elements-left-ideal-Ring :
    (J : left-ideal-Ring l3 R) → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-left-ideal-Ring =
    has-same-elements-left-ideal-Semiring (semiring-Ring R) I

module _
  {l1 l2 : Level} (R : Ring l1) (I : left-ideal-Ring l2 R)
  where

  refl-has-same-elements-left-ideal-Ring :
    has-same-elements-left-ideal-Ring R I I
  refl-has-same-elements-left-ideal-Ring =
    refl-has-same-elements-left-ideal-Semiring (semiring-Ring R) I

  is-torsorial-has-same-elements-left-ideal-Ring :
    is-torsorial (has-same-elements-left-ideal-Ring R I)
  is-torsorial-has-same-elements-left-ideal-Ring =
    is-torsorial-has-same-elements-left-ideal-Semiring (semiring-Ring R) I

  has-same-elements-eq-left-ideal-Ring :
    (J : left-ideal-Ring l2 R) →
    (I ＝ J) → has-same-elements-left-ideal-Ring R I J
  has-same-elements-eq-left-ideal-Ring =
    has-same-elements-eq-left-ideal-Semiring (semiring-Ring R) I

  is-equiv-has-same-elements-eq-left-ideal-Ring :
    (J : left-ideal-Ring l2 R) →
    is-equiv (has-same-elements-eq-left-ideal-Ring J)
  is-equiv-has-same-elements-eq-left-ideal-Ring =
    is-equiv-has-same-elements-eq-left-ideal-Semiring (semiring-Ring R) I

  extensionality-left-ideal-Ring :
    (J : left-ideal-Ring l2 R) →
    (I ＝ J) ≃ has-same-elements-left-ideal-Ring R I J
  extensionality-left-ideal-Ring =
    extensionality-left-ideal-Semiring (semiring-Ring R) I

  eq-has-same-elements-left-ideal-Ring :
    (J : left-ideal-Ring l2 R) →
    has-same-elements-left-ideal-Ring R I J → I ＝ J
  eq-has-same-elements-left-ideal-Ring =
    eq-has-same-elements-left-ideal-Semiring (semiring-Ring R) I
```
