# Left ideals of semirings

```agda
module ring-theory.left-ideals-semirings where
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

A {{#concept "left ideal" Disambiguation="semiring" Agda=left-ideal-Semiring}} in a [semiring](ring-theory.semirings.md) `R` is a left submodule of
`R`.

## Definitions

### Left ideals

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  is-left-ideal-subset-Semiring :
    {l2 : Level} → subset-Semiring l2 R → UU (l1 ⊔ l2)
  is-left-ideal-subset-Semiring S =
    is-additive-submonoid-subset-Semiring R S ×
    is-closed-under-left-multiplication-subset-Semiring R S

  is-prop-is-left-ideal-subset-Semiring :
    {l2 : Level} (S : subset-Semiring l2 R) →
    is-prop (is-left-ideal-subset-Semiring S)
  is-prop-is-left-ideal-subset-Semiring S =
    is-prop-product
      ( is-prop-is-additive-submonoid-subset-Semiring R S)
      ( is-prop-is-closed-under-left-multiplication-subset-Semiring R S)

left-ideal-Semiring :
  (l : Level) {l1 : Level} (R : Semiring l1) → UU (lsuc l ⊔ l1)
left-ideal-Semiring l R =
  Σ (subset-Semiring l R) (is-left-ideal-subset-Semiring R)

module _
  {l1 l2 : Level} (R : Semiring l1) (I : left-ideal-Semiring l2 R)
  where

  subset-left-ideal-Semiring : subset-Semiring l2 R
  subset-left-ideal-Semiring = pr1 I

  is-in-left-ideal-Semiring : type-Semiring R → UU l2
  is-in-left-ideal-Semiring x = type-Prop (subset-left-ideal-Semiring x)

  type-left-ideal-Semiring : UU (l1 ⊔ l2)
  type-left-ideal-Semiring = type-subset-Semiring R subset-left-ideal-Semiring

  inclusion-left-ideal-Semiring :
    type-left-ideal-Semiring → type-Semiring R
  inclusion-left-ideal-Semiring =
    inclusion-subset-Semiring R subset-left-ideal-Semiring

  ap-inclusion-left-ideal-Semiring :
    (x y : type-left-ideal-Semiring) → x ＝ y →
    inclusion-left-ideal-Semiring x ＝ inclusion-left-ideal-Semiring y
  ap-inclusion-left-ideal-Semiring =
    ap-inclusion-subset-Semiring R subset-left-ideal-Semiring

  is-in-subset-inclusion-left-ideal-Semiring :
    (x : type-left-ideal-Semiring) →
    is-in-left-ideal-Semiring (inclusion-left-ideal-Semiring x)
  is-in-subset-inclusion-left-ideal-Semiring =
    is-in-subset-inclusion-subset-Semiring R subset-left-ideal-Semiring

  is-closed-under-eq-left-ideal-Semiring :
    {x y : type-Semiring R} → is-in-left-ideal-Semiring x →
    (x ＝ y) → is-in-left-ideal-Semiring y
  is-closed-under-eq-left-ideal-Semiring =
    is-closed-under-eq-subset-Semiring R subset-left-ideal-Semiring

  is-closed-under-eq-left-ideal-Semiring' :
    {x y : type-Semiring R} → is-in-left-ideal-Semiring y →
    (x ＝ y) → is-in-left-ideal-Semiring x
  is-closed-under-eq-left-ideal-Semiring' =
    is-closed-under-eq-subset-Semiring' R subset-left-ideal-Semiring

  is-left-ideal-subset-left-ideal-Semiring :
    is-left-ideal-subset-Semiring R subset-left-ideal-Semiring
  is-left-ideal-subset-left-ideal-Semiring = pr2 I

  is-additive-submonoid-subset-left-ideal-Semiring :
    is-additive-submonoid-subset-Semiring R subset-left-ideal-Semiring
  is-additive-submonoid-subset-left-ideal-Semiring =
    pr1 is-left-ideal-subset-left-ideal-Semiring

  contains-zero-left-ideal-Semiring :
    is-in-left-ideal-Semiring (zero-Semiring R)
  contains-zero-left-ideal-Semiring =
    pr1 is-additive-submonoid-subset-left-ideal-Semiring

  is-closed-under-addition-left-ideal-Semiring :
    is-closed-under-addition-subset-Semiring R subset-left-ideal-Semiring
  is-closed-under-addition-left-ideal-Semiring =
    pr2 is-additive-submonoid-subset-left-ideal-Semiring

  is-closed-under-left-multiplication-left-ideal-Semiring :
    is-closed-under-left-multiplication-subset-Semiring R
      ( subset-left-ideal-Semiring)
  is-closed-under-left-multiplication-left-ideal-Semiring =
    pr2 is-left-ideal-subset-left-ideal-Semiring

  is-left-ideal-left-ideal-Semiring :
    is-left-ideal-subset-Semiring R subset-left-ideal-Semiring
  is-left-ideal-left-ideal-Semiring = pr2 I
```

## Properties

### Characterizing equality of left ideals in semirings

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) (I : left-ideal-Semiring l2 R)
  where

  has-same-elements-left-ideal-Semiring :
    (J : left-ideal-Semiring l3 R) → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-left-ideal-Semiring J =
    has-same-elements-subtype
      ( subset-left-ideal-Semiring R I)
      ( subset-left-ideal-Semiring R J)

module _
  {l1 l2 : Level} (R : Semiring l1) (I : left-ideal-Semiring l2 R)
  where

  refl-has-same-elements-left-ideal-Semiring :
    has-same-elements-left-ideal-Semiring R I I
  refl-has-same-elements-left-ideal-Semiring =
    refl-has-same-elements-subtype (subset-left-ideal-Semiring R I)

  is-torsorial-has-same-elements-left-ideal-Semiring :
    is-torsorial (has-same-elements-left-ideal-Semiring R I)
  is-torsorial-has-same-elements-left-ideal-Semiring =
    is-torsorial-Eq-subtype
      ( is-torsorial-has-same-elements-subtype (subset-left-ideal-Semiring R I))
      ( is-prop-is-left-ideal-subset-Semiring R)
      ( subset-left-ideal-Semiring R I)
      ( refl-has-same-elements-left-ideal-Semiring)
      ( is-left-ideal-left-ideal-Semiring R I)

  has-same-elements-eq-left-ideal-Semiring :
    (J : left-ideal-Semiring l2 R) →
    (I ＝ J) → has-same-elements-left-ideal-Semiring R I J
  has-same-elements-eq-left-ideal-Semiring .I refl =
    refl-has-same-elements-left-ideal-Semiring

  is-equiv-has-same-elements-eq-left-ideal-Semiring :
    (J : left-ideal-Semiring l2 R) →
    is-equiv (has-same-elements-eq-left-ideal-Semiring J)
  is-equiv-has-same-elements-eq-left-ideal-Semiring =
    fundamental-theorem-id
      is-torsorial-has-same-elements-left-ideal-Semiring
      has-same-elements-eq-left-ideal-Semiring

  extensionality-left-ideal-Semiring :
    (J : left-ideal-Semiring l2 R) →
    (I ＝ J) ≃ has-same-elements-left-ideal-Semiring R I J
  pr1 (extensionality-left-ideal-Semiring J) =
    has-same-elements-eq-left-ideal-Semiring J
  pr2 (extensionality-left-ideal-Semiring J) =
    is-equiv-has-same-elements-eq-left-ideal-Semiring J

  eq-has-same-elements-left-ideal-Semiring :
    (J : left-ideal-Semiring l2 R) →
    has-same-elements-left-ideal-Semiring R I J → I ＝ J
  eq-has-same-elements-left-ideal-Semiring J =
    map-inv-equiv (extensionality-left-ideal-Semiring J)
```
