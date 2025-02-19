# Loops

```agda
module group-theory.loops where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.dependent-identifications
open import foundation-core.subtypes

open import group-theory.quasigroups
open import group-theory.units-quasigroups
```

</details>

## Idea

{{#concept "Loops" Agda=Loop}} are [quasigroups](quasigroups.quasigroups.md)
with a designated identity element, that is, an element `e : Q` such that for
any `x : type-Quasigroup Q`:

```text
  e * x ＝ x
  x * e ＝ x
```

Note: we will see that units, when they exist, are unique, and so being a loop
is actually a property of a quasigroup rather than structure.

## Definitions

### Left units in quasigroups

```agda
module _
  {l : Level} (Q : Quasigroup l)
  where

  private
    _*_ : type-Quasigroup Q → type-Quasigroup Q → type-Quasigroup Q
    _*_ = mul-Quasigroup Q

    _l/_ : type-Quasigroup Q → type-Quasigroup Q → type-Quasigroup Q
    _l/_ = left-div-Quasigroup Q

    _r/_ : type-Quasigroup Q → type-Quasigroup Q → type-Quasigroup Q
    _r/_ = right-div-Quasigroup Q

  is-left-unit-Quasigroup : (e : type-Quasigroup Q) → UU l
  is-left-unit-Quasigroup e = (x : type-Quasigroup Q) → e * x ＝ x

  is-prop-is-left-unit-Quasigroup :
    (e : type-Quasigroup Q) → is-prop (is-left-unit-Quasigroup e)
  is-prop-is-left-unit-Quasigroup e =
    is-prop-Π (λ x → is-set-Quasigroup Q (e * x) x)

  is-left-unit-Quasigroup-Prop : (e : type-Quasigroup Q) → Prop l
  is-left-unit-Quasigroup-Prop e =
    is-left-unit-Quasigroup e , is-prop-is-left-unit-Quasigroup e

  has-left-unit-Quasigroup : UU l
  has-left-unit-Quasigroup =
    Σ (type-Quasigroup Q) λ e → is-left-unit-Quasigroup e

  element-has-left-unit-Quasigroup :
    has-left-unit-Quasigroup → type-Quasigroup Q
  element-has-left-unit-Quasigroup (e , _) = e

  left-units-agree-Quasigroup :
    (e f : has-left-unit-Quasigroup) → element-has-left-unit-Quasigroup e
    ＝ element-has-left-unit-Quasigroup f
  left-units-agree-Quasigroup (e , e-left-unit) (f , f-left-unit) =
    equational-reasoning
    e
    ＝ (e * f) r/ f
      by is-right-cancellative-right-div-Quasigroup Q f e
    ＝ f r/ f
      by ap (λ x → x r/ f) (e-left-unit f)
    ＝ (f * f) r/ f
      by ap (λ x → x r/ f) (inv (f-left-unit f))
    ＝ f
      by inv (is-right-cancellative-right-div-Quasigroup Q f f)

  is-prop-has-left-unit-Quasigroup : is-prop has-left-unit-Quasigroup
  pr1 (is-prop-has-left-unit-Quasigroup e f) =
    eq-type-subtype
      ( is-left-unit-Quasigroup-Prop)
      ( left-units-agree-Quasigroup e f)
  pr2 (is-prop-has-left-unit-Quasigroup e f) =
    is-set-has-uip
      ( is-set-type-subtype is-left-unit-Quasigroup-Prop
        ( is-set-Quasigroup Q))
      ( e)
      ( f)
      ( pr1 (is-prop-has-left-unit-Quasigroup e f))
```

### Right units in quasigroups

```agda
  is-right-unit-Quasigroup : (e : type-Quasigroup Q) → UU l
  is-right-unit-Quasigroup e = (x : type-Quasigroup Q) → x * e ＝ x

  is-prop-is-right-unit-Quasigroup :
    (e : type-Quasigroup Q) → is-prop (is-right-unit-Quasigroup e)
  is-prop-is-right-unit-Quasigroup e =
    is-prop-Π (λ x → is-set-Quasigroup Q (x * e) x)

  is-right-unit-Quasigroup-Prop : (e : type-Quasigroup Q) → Prop l
  is-right-unit-Quasigroup-Prop e =
    is-right-unit-Quasigroup e , is-prop-is-right-unit-Quasigroup e

  has-right-unit-Quasigroup : UU l
  has-right-unit-Quasigroup =
    Σ (type-Quasigroup Q) λ e → is-right-unit-Quasigroup e

  element-has-right-unit-Quasigroup :
    has-right-unit-Quasigroup → type-Quasigroup Q
  element-has-right-unit-Quasigroup (e , _) = e

  right-units-agree-Quasigroup :
    (e f : has-right-unit-Quasigroup) → element-has-right-unit-Quasigroup e
    ＝ element-has-right-unit-Quasigroup f
  right-units-agree-Quasigroup (e , e-right-unit) (f , f-right-unit) =
    equational-reasoning
    e
    ＝ f l/ (f * e)
      by is-right-cancellative-left-div-Quasigroup Q f e
    ＝ f l/ f
      by ap (λ x → f l/ x) (e-right-unit f)
    ＝ f l/ (f * f)
      by inv ((ap (λ x → f l/ x) (f-right-unit f)))
    ＝ f
      by inv (is-right-cancellative-left-div-Quasigroup Q f f)

  is-prop-has-right-unit-Quasigroup : is-prop has-right-unit-Quasigroup
  pr1 (is-prop-has-right-unit-Quasigroup e f) =
    eq-type-subtype
      ( is-right-unit-Quasigroup-Prop)
      ( right-units-agree-Quasigroup e f)
  pr2 (is-prop-has-right-unit-Quasigroup e f) =
    is-set-has-uip
      ( is-set-type-subtype is-right-unit-Quasigroup-Prop
        ( is-set-Quasigroup Q))
      ( e)
      ( f)
      ( pr1 (is-prop-has-right-unit-Quasigroup e f))
```

### Units in quasigroups

A **unit**, as usual, is both a left and right unit. In fact, if `Q` has both a
left unit `e` and a right unit `f`, then already we have `e ＝ f`, and thus the
type of units is equivalent to the type of pairs of left and right units.

```agda
  has-unit-Quasigroup : UU l
  has-unit-Quasigroup =
    Σ ( type-Quasigroup Q)
      ( λ e → is-left-unit-Quasigroup e × is-right-unit-Quasigroup e)

  unit-has-unit-Quasigroup : has-unit-Quasigroup → type-Quasigroup Q
  unit-has-unit-Quasigroup (e , _) = e

  has-unit-has-left-unit-Quasigroup :
    has-unit-Quasigroup → has-left-unit-Quasigroup
  has-unit-has-left-unit-Quasigroup (e , e-left-unit , _) = (e , e-left-unit)

  has-unit-has-right-unit-Quasigroup :
    has-unit-Quasigroup → has-right-unit-Quasigroup
  has-unit-has-right-unit-Quasigroup (e , _ , e-right-unit) = (e , e-right-unit)

  has-left-and-right-units-has-unit-Quasigroup :
    has-unit-Quasigroup → has-left-unit-Quasigroup × has-right-unit-Quasigroup
  has-left-and-right-units-has-unit-Quasigroup e =
    ( has-unit-has-left-unit-Quasigroup e) ,
    ( has-unit-has-right-unit-Quasigroup e)

  left-and-right-units-agree-Quasigroup :
    (e : has-left-unit-Quasigroup) → (f : has-right-unit-Quasigroup) →
    element-has-left-unit-Quasigroup e ＝ element-has-right-unit-Quasigroup f
  left-and-right-units-agree-Quasigroup (e , e-left-unit) (f , f-right-unit) =
    equational-reasoning
    e
    ＝ (e * f) r/ f
      by is-right-cancellative-right-div-Quasigroup Q f e
    ＝ f r/ f
      by ap (λ x → x r/ f) (e-left-unit f)
    ＝ (f * f) r/ f
      by inv (ap (λ x → x r/ f) (f-right-unit f))
    ＝ f
      by inv (is-right-cancellative-right-div-Quasigroup Q f f)

  is-right-unit-has-left-unit-Quasigroup :
    (e : has-left-unit-Quasigroup) → has-right-unit-Quasigroup →
    is-right-unit-Quasigroup (element-has-left-unit-Quasigroup e)
  is-right-unit-has-left-unit-Quasigroup e f x =
    inv-tr is-right-unit-Quasigroup (left-and-right-units-agree-Quasigroup e f)
    (pr2 f) x

  has-unit-has-right-unit-has-left-unit-Quasigroup :
    has-left-unit-Quasigroup → has-right-unit-Quasigroup → has-unit-Quasigroup
  pr1 (has-unit-has-right-unit-has-left-unit-Quasigroup (e , _) _) = e
  pr1 (pr2 (has-unit-has-right-unit-has-left-unit-Quasigroup (e , e-left-unit) _)) =
    e-left-unit
  pr2 (pr2 (has-unit-has-right-unit-has-left-unit-Quasigroup e f)) =
    is-right-unit-has-left-unit-Quasigroup e f
```

### Loops

Note now that having a designated unit is a property of a quasigroup, and thus
we may make the easier definition.

```agda
Loop : (l : Level) → UU (lsuc l)
Loop l = Σ (Quasigroup l) (λ Q → has-unit-Quasigroup Q)

quasigroup-Loop : {l : Level} (Q : Loop l) → Quasigroup l
quasigroup-Loop (Q , _) = Q
```
