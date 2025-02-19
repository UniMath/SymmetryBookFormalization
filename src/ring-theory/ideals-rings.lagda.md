# Ideals of rings

```agda
module ring-theory.ideals-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.congruence-relations-abelian-groups
open import group-theory.congruence-relations-monoids
open import group-theory.subgroups-abelian-groups

open import ring-theory.congruence-relations-rings
open import ring-theory.left-ideals-rings
open import ring-theory.right-ideals-rings
open import ring-theory.rings
open import ring-theory.subsets-rings
```

</details>

## Idea

An **ideal** in a [ring](ring-theory.rings.md) `R` is a submodule of `R`.

## Definitions

### Two-sided ideals

```agda
is-ideal-subset-Ring :
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R) → UU (l1 ⊔ l2)
is-ideal-subset-Ring R P =
  is-additive-subgroup-subset-Ring R P ×
  ( is-closed-under-left-multiplication-subset-Ring R P ×
    is-closed-under-right-multiplication-subset-Ring R P)

is-prop-is-ideal-subset-Ring :
  {l1 l2 : Level} (R : Ring l1) (P : subset-Ring l2 R) →
  is-prop (is-ideal-subset-Ring R P)
is-prop-is-ideal-subset-Ring R P =
  is-prop-product
    ( is-prop-is-additive-subgroup-subset-Ring R P)
    ( is-prop-product
      ( is-prop-is-closed-under-left-multiplication-subset-Ring R P)
      ( is-prop-is-closed-under-right-multiplication-subset-Ring R P))

ideal-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU (lsuc l ⊔ l1)
ideal-Ring l R =
  Σ (subset-Ring l R) (is-ideal-subset-Ring R)

module _
  {l1 l2 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  where

  subset-ideal-Ring : subset-Ring l2 R
  subset-ideal-Ring = pr1 I

  is-in-ideal-Ring : type-Ring R → UU l2
  is-in-ideal-Ring x = type-Prop (subset-ideal-Ring x)

  type-ideal-Ring : UU (l1 ⊔ l2)
  type-ideal-Ring = type-subset-Ring R subset-ideal-Ring

  inclusion-ideal-Ring : type-ideal-Ring → type-Ring R
  inclusion-ideal-Ring =
    inclusion-subset-Ring R subset-ideal-Ring

  ap-inclusion-ideal-Ring :
    (x y : type-ideal-Ring) → x ＝ y →
    inclusion-ideal-Ring x ＝ inclusion-ideal-Ring y
  ap-inclusion-ideal-Ring = ap-inclusion-subset-Ring R subset-ideal-Ring

  is-in-subset-inclusion-ideal-Ring :
    (x : type-ideal-Ring) → is-in-ideal-Ring (inclusion-ideal-Ring x)
  is-in-subset-inclusion-ideal-Ring =
    is-in-subset-inclusion-subset-Ring R subset-ideal-Ring

  is-closed-under-eq-ideal-Ring :
    {x y : type-Ring R} → is-in-ideal-Ring x → (x ＝ y) → is-in-ideal-Ring y
  is-closed-under-eq-ideal-Ring =
    is-closed-under-eq-subset-Ring R subset-ideal-Ring

  is-closed-under-eq-ideal-Ring' :
    {x y : type-Ring R} → is-in-ideal-Ring y → (x ＝ y) → is-in-ideal-Ring x
  is-closed-under-eq-ideal-Ring' =
    is-closed-under-eq-subset-Ring' R subset-ideal-Ring

  is-ideal-ideal-Ring :
    is-ideal-subset-Ring R subset-ideal-Ring
  is-ideal-ideal-Ring = pr2 I

  is-additive-subgroup-ideal-Ring :
    is-additive-subgroup-subset-Ring R subset-ideal-Ring
  is-additive-subgroup-ideal-Ring =
    pr1 is-ideal-ideal-Ring

  contains-zero-ideal-Ring : contains-zero-subset-Ring R subset-ideal-Ring
  contains-zero-ideal-Ring = pr1 is-additive-subgroup-ideal-Ring

  is-closed-under-addition-ideal-Ring :
    is-closed-under-addition-subset-Ring R subset-ideal-Ring
  is-closed-under-addition-ideal-Ring =
    pr1 (pr2 is-additive-subgroup-ideal-Ring)

  is-closed-under-negatives-ideal-Ring :
    is-closed-under-negatives-subset-Ring R subset-ideal-Ring
  is-closed-under-negatives-ideal-Ring =
    pr2 (pr2 is-additive-subgroup-ideal-Ring)

  is-closed-under-left-multiplication-ideal-Ring :
    is-closed-under-left-multiplication-subset-Ring R subset-ideal-Ring
  is-closed-under-left-multiplication-ideal-Ring =
    pr1 (pr2 is-ideal-ideal-Ring)

  is-closed-under-right-multiplication-ideal-Ring :
    is-closed-under-right-multiplication-subset-Ring R subset-ideal-Ring
  is-closed-under-right-multiplication-ideal-Ring =
    pr2 (pr2 is-ideal-ideal-Ring)

  subgroup-ideal-Ring : Subgroup-Ab l2 (ab-Ring R)
  pr1 subgroup-ideal-Ring = subset-ideal-Ring
  pr1 (pr2 subgroup-ideal-Ring) = contains-zero-ideal-Ring
  pr1 (pr2 (pr2 subgroup-ideal-Ring)) = is-closed-under-addition-ideal-Ring
  pr2 (pr2 (pr2 subgroup-ideal-Ring)) = is-closed-under-negatives-ideal-Ring

  normal-subgroup-ideal-Ring : Normal-Subgroup-Ab l2 (ab-Ring R)
  normal-subgroup-ideal-Ring =
    normal-subgroup-Subgroup-Ab (ab-Ring R) subgroup-ideal-Ring

  left-ideal-ideal-Ring : left-ideal-Ring l2 R
  pr1 left-ideal-ideal-Ring =
    subset-ideal-Ring
  pr1 (pr1 (pr2 left-ideal-ideal-Ring)) =
    contains-zero-ideal-Ring
  pr2 (pr1 (pr2 left-ideal-ideal-Ring)) =
    is-closed-under-addition-ideal-Ring
  pr2 (pr2 left-ideal-ideal-Ring) =
    is-closed-under-left-multiplication-ideal-Ring

  right-ideal-ideal-Ring : right-ideal-Ring l2 R
  pr1 right-ideal-ideal-Ring = subset-ideal-Ring
  pr1 (pr2 right-ideal-ideal-Ring) = is-additive-subgroup-ideal-Ring
  pr2 (pr2 right-ideal-ideal-Ring) =
    is-closed-under-right-multiplication-ideal-Ring
```

## Properties

### Characterizing equality of ideals in rings

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  where

  has-same-elements-ideal-Ring : (J : ideal-Ring l3 R) → UU (l1 ⊔ l2 ⊔ l3)
  has-same-elements-ideal-Ring J =
    has-same-elements-subtype (subset-ideal-Ring R I) (subset-ideal-Ring R J)

module _
  {l1 l2 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  where

  refl-has-same-elements-ideal-Ring :
    has-same-elements-ideal-Ring R I I
  refl-has-same-elements-ideal-Ring =
    refl-has-same-elements-subtype (subset-ideal-Ring R I)

  is-torsorial-has-same-elements-ideal-Ring :
    is-torsorial (has-same-elements-ideal-Ring R I)
  is-torsorial-has-same-elements-ideal-Ring =
    is-torsorial-Eq-subtype
      ( is-torsorial-has-same-elements-subtype (subset-ideal-Ring R I))
      ( is-prop-is-ideal-subset-Ring R)
      ( subset-ideal-Ring R I)
      ( refl-has-same-elements-ideal-Ring)
      ( is-ideal-ideal-Ring R I)

  has-same-elements-eq-ideal-Ring :
    (J : ideal-Ring l2 R) → (I ＝ J) → has-same-elements-ideal-Ring R I J
  has-same-elements-eq-ideal-Ring .I refl = refl-has-same-elements-ideal-Ring

  is-equiv-has-same-elements-eq-ideal-Ring :
    (J : ideal-Ring l2 R) → is-equiv (has-same-elements-eq-ideal-Ring J)
  is-equiv-has-same-elements-eq-ideal-Ring =
    fundamental-theorem-id
      is-torsorial-has-same-elements-ideal-Ring
      has-same-elements-eq-ideal-Ring

  extensionality-ideal-Ring :
    (J : ideal-Ring l2 R) → (I ＝ J) ≃ has-same-elements-ideal-Ring R I J
  pr1 (extensionality-ideal-Ring J) = has-same-elements-eq-ideal-Ring J
  pr2 (extensionality-ideal-Ring J) = is-equiv-has-same-elements-eq-ideal-Ring J

  eq-has-same-elements-ideal-Ring :
    (J : ideal-Ring l2 R) → has-same-elements-ideal-Ring R I J → I ＝ J
  eq-has-same-elements-ideal-Ring J =
    map-inv-equiv (extensionality-ideal-Ring J)
```

### Two sided ideals of rings are in 1-1 correspondence with congruence relations

#### The standard similarity relation obtained from an ideal

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  where

  sim-congruence-ideal-Ring : (x y : type-Ring R) → UU l2
  sim-congruence-ideal-Ring =
    sim-congruence-Subgroup-Ab
      ( ab-Ring R)
      ( subgroup-ideal-Ring R I)

  is-prop-sim-congruence-ideal-Ring :
    (x y : type-Ring R) → is-prop (sim-congruence-ideal-Ring x y)
  is-prop-sim-congruence-ideal-Ring =
    is-prop-sim-congruence-Subgroup-Ab
      ( ab-Ring R)
      ( subgroup-ideal-Ring R I)

  prop-congruence-ideal-Ring : (x y : type-Ring R) → Prop l2
  prop-congruence-ideal-Ring =
    prop-congruence-Subgroup-Ab
      ( ab-Ring R)
      ( subgroup-ideal-Ring R I)
```

#### The left equivalence relation obtained from an ideal

```agda
  left-equivalence-relation-congruence-ideal-Ring :
    equivalence-relation l2 (type-Ring R)
  left-equivalence-relation-congruence-ideal-Ring =
    left-equivalence-relation-congruence-Subgroup-Ab
      ( ab-Ring R)
      ( subgroup-ideal-Ring R I)

  left-sim-congruence-ideal-Ring :
    type-Ring R → type-Ring R → UU l2
  left-sim-congruence-ideal-Ring =
    left-sim-congruence-Subgroup-Ab
      ( ab-Ring R)
      ( subgroup-ideal-Ring R I)
```

#### The left similarity relation of an ideal relates the same elements as the standard similarity relation

```agda
  left-sim-sim-congruence-ideal-Ring :
    (x y : type-Ring R) →
    sim-congruence-ideal-Ring x y →
    left-sim-congruence-ideal-Ring x y
  left-sim-sim-congruence-ideal-Ring =
    left-sim-sim-congruence-Subgroup-Ab
      ( ab-Ring R)
      ( subgroup-ideal-Ring R I)

  sim-left-sim-congruence-ideal-Ring :
    (x y : type-Ring R) →
    left-sim-congruence-ideal-Ring x y →
    sim-congruence-ideal-Ring x y
  sim-left-sim-congruence-ideal-Ring =
    sim-left-sim-congruence-Subgroup-Ab
      ( ab-Ring R)
      ( subgroup-ideal-Ring R I)
```

#### The standard similarity relation is a congruence relation

```agda
  refl-congruence-ideal-Ring :
    is-reflexive sim-congruence-ideal-Ring
  refl-congruence-ideal-Ring =
    refl-congruence-Subgroup-Ab
      ( ab-Ring R)
      ( subgroup-ideal-Ring R I)

  symmetric-congruence-ideal-Ring :
    is-symmetric sim-congruence-ideal-Ring
  symmetric-congruence-ideal-Ring =
    symmetric-congruence-Subgroup-Ab
      ( ab-Ring R)
      ( subgroup-ideal-Ring R I)

  transitive-congruence-ideal-Ring :
    is-transitive sim-congruence-ideal-Ring
  transitive-congruence-ideal-Ring =
    transitive-congruence-Subgroup-Ab
      ( ab-Ring R)
      ( subgroup-ideal-Ring R I)

  equivalence-relation-congruence-ideal-Ring :
    equivalence-relation l2 (type-Ring R)
  equivalence-relation-congruence-ideal-Ring =
    equivalence-relation-congruence-Subgroup-Ab
      ( ab-Ring R)
      ( subgroup-ideal-Ring R I)

  relate-same-elements-left-sim-congruence-ideal-Ring :
    relate-same-elements-equivalence-relation
      ( equivalence-relation-congruence-ideal-Ring)
      ( left-equivalence-relation-congruence-ideal-Ring)
  relate-same-elements-left-sim-congruence-ideal-Ring =
    relate-same-elements-left-sim-congruence-Subgroup-Ab
      ( ab-Ring R)
      ( subgroup-ideal-Ring R I)

  add-congruence-ideal-Ring :
    ( is-congruence-Ab
      ( ab-Ring R)
      ( equivalence-relation-congruence-ideal-Ring))
  add-congruence-ideal-Ring =
    ( add-congruence-Subgroup-Ab
      ( ab-Ring R)
      ( subgroup-ideal-Ring R I))

  is-congruence-monoid-mul-congruence-ideal-Ring :
    { x y u v : type-Ring R} →
    ( is-in-ideal-Ring R I (add-Ring R (neg-Ring R x) y)) →
    ( is-in-ideal-Ring R I (add-Ring R (neg-Ring R u) v)) →
    ( is-in-ideal-Ring R I
      ( add-Ring R (neg-Ring R (mul-Ring R x u)) (mul-Ring R y v)))
  is-congruence-monoid-mul-congruence-ideal-Ring {x} {y} {u} {v} e f =
    ( is-closed-under-eq-ideal-Ring R I
      ( is-closed-under-addition-ideal-Ring R I
        ( is-closed-under-right-multiplication-ideal-Ring R I
          ( add-Ring R (neg-Ring R x) y)
          ( u)
          ( e))
        ( is-closed-under-left-multiplication-ideal-Ring R I
          ( y)
          ( add-Ring R (neg-Ring R u) v)
          ( f))))
    ( equational-reasoning
      ( add-Ring R
        ( mul-Ring R (add-Ring R (neg-Ring R x) y) u)
        ( mul-Ring R y (add-Ring R (neg-Ring R u) v)))
    ＝ ( add-Ring R
        ( mul-Ring R (add-Ring R (neg-Ring R x) y) u)
        ( add-Ring R (mul-Ring R y (neg-Ring R u)) (mul-Ring R y v)))
      by
      ( ap
        ( add-Ring R ( mul-Ring R (add-Ring R (neg-Ring R x) y) u))
        ( left-distributive-mul-add-Ring R y (neg-Ring R u) v))
    ＝ ( add-Ring R
        ( mul-Ring R (add-Ring R (neg-Ring R x) y) u)
        ( add-Ring R (neg-Ring R (mul-Ring R y u)) (mul-Ring R y v)))
      by
      ( ap
        ( λ a →
          add-Ring R
            ( mul-Ring R (add-Ring R (neg-Ring R x) y) u)
            ( add-Ring R a (mul-Ring R y v)))
        ( right-negative-law-mul-Ring R y u))
    ＝ ( add-Ring R
        ( add-Ring R (mul-Ring R (neg-Ring R x) u) (mul-Ring R y u))
        ( add-Ring R (neg-Ring R (mul-Ring R y u)) (mul-Ring R y v)))
      by
      ( ap
        ( add-Ring' R
          ( add-Ring R (neg-Ring R (mul-Ring R y u)) (mul-Ring R y v)))
        ( right-distributive-mul-add-Ring R (neg-Ring R x) y u))
    ＝ ( add-Ring R
        ( add-Ring R (neg-Ring R (mul-Ring R x u)) (mul-Ring R y u))
        ( add-Ring R (neg-Ring R (mul-Ring R y u)) (mul-Ring R y v)))
      by
      ( ap
        ( λ a →
          add-Ring R
            ( add-Ring R a (mul-Ring R y u))
            ( add-Ring R (neg-Ring R (mul-Ring R y u)) (mul-Ring R y v)))
        ( left-negative-law-mul-Ring R x u))
    ＝ ( add-Ring R (neg-Ring R (mul-Ring R x u)) (mul-Ring R y v))
      by
      ( add-and-subtract-Ring R
        ( neg-Ring R (mul-Ring R x u))
        ( mul-Ring R y u)
        ( mul-Ring R y v)))

  mul-congruence-ideal-Ring :
    ( is-congruence-Monoid
      ( multiplicative-monoid-Ring R)
      ( equivalence-relation-congruence-ideal-Ring))
  mul-congruence-ideal-Ring =
    is-congruence-monoid-mul-congruence-ideal-Ring

  congruence-ideal-Ring : congruence-Ring l2 R
  congruence-ideal-Ring = construct-congruence-Ring R
    ( equivalence-relation-congruence-ideal-Ring)
    ( add-congruence-ideal-Ring)
    ( mul-congruence-ideal-Ring)
```

#### The ideal obtained from a congruence relation

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : congruence-Ring l2 R)
  where

  subset-congruence-Ring : subset-Ring l2 R
  subset-congruence-Ring = prop-congruence-Ring R S (zero-Ring R)

  is-in-subset-congruence-Ring : (type-Ring R) → UU l2
  is-in-subset-congruence-Ring = type-Prop ∘ subset-congruence-Ring

  contains-zero-subset-congruence-Ring :
    contains-zero-subset-Ring R subset-congruence-Ring
  contains-zero-subset-congruence-Ring =
    refl-congruence-Ring R S (zero-Ring R)

  is-closed-under-addition-subset-congruence-Ring :
    is-closed-under-addition-subset-Ring R subset-congruence-Ring
  is-closed-under-addition-subset-congruence-Ring H K =
    concatenate-eq-sim-congruence-Ring R S
      ( inv (left-unit-law-add-Ring R (zero-Ring R)))
      ( add-congruence-Ring R S H K)

  is-closed-under-negatives-subset-congruence-Ring :
    is-closed-under-negatives-subset-Ring R subset-congruence-Ring
  is-closed-under-negatives-subset-congruence-Ring H =
      concatenate-eq-sim-congruence-Ring R S
        ( inv (neg-zero-Ring R))
        ( neg-congruence-Ring R S H)

  is-closed-under-left-multiplication-subset-congruence-Ring :
    is-closed-under-left-multiplication-subset-Ring R subset-congruence-Ring
  is-closed-under-left-multiplication-subset-congruence-Ring x y H =
    concatenate-eq-sim-congruence-Ring R S
      ( inv (right-zero-law-mul-Ring R x))
      ( left-mul-congruence-Ring R S x H)

  is-closed-under-right-multiplication-subset-congruence-Ring :
    is-closed-under-right-multiplication-subset-Ring R subset-congruence-Ring
  is-closed-under-right-multiplication-subset-congruence-Ring x y H =
    concatenate-eq-sim-congruence-Ring R S
      ( inv (left-zero-law-mul-Ring R y))
      ( right-mul-congruence-Ring R S H y)

  is-additive-subgroup-congruence-Ring :
    is-additive-subgroup-subset-Ring R subset-congruence-Ring
  pr1 is-additive-subgroup-congruence-Ring =
    contains-zero-subset-congruence-Ring
  pr1 (pr2 is-additive-subgroup-congruence-Ring) =
    is-closed-under-addition-subset-congruence-Ring
  pr2 (pr2 is-additive-subgroup-congruence-Ring) =
    is-closed-under-negatives-subset-congruence-Ring

  ideal-congruence-Ring : ideal-Ring l2 R
  pr1 ideal-congruence-Ring =
    subset-congruence-Ring
  pr1 (pr2 ideal-congruence-Ring) =
    is-additive-subgroup-congruence-Ring
  pr1 (pr2 (pr2 ideal-congruence-Ring)) =
    is-closed-under-left-multiplication-subset-congruence-Ring
  pr2 (pr2 (pr2 ideal-congruence-Ring)) =
    is-closed-under-right-multiplication-subset-congruence-Ring
```

#### The ideal obtained from the congruence relation of an ideal `I` is `I` itself

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (I : ideal-Ring l2 R)
  where

  has-same-elements-ideal-congruence-Ring :
    has-same-elements-ideal-Ring R
      ( ideal-congruence-Ring R (congruence-ideal-Ring R I))
      ( I)
  pr1 (has-same-elements-ideal-congruence-Ring x) H =
    is-closed-under-eq-ideal-Ring R I H
      ( ( ap (add-Ring' R x) (neg-zero-Ring R)) ∙
        ( left-unit-law-add-Ring R x))
  pr2 (has-same-elements-ideal-congruence-Ring x) H =
    is-closed-under-eq-ideal-Ring' R I H
      ( ( ap (add-Ring' R x) (neg-zero-Ring R)) ∙
        ( left-unit-law-add-Ring R x))

  is-retraction-ideal-congruence-Ring :
    ideal-congruence-Ring R (congruence-ideal-Ring R I) ＝ I
  is-retraction-ideal-congruence-Ring =
    eq-has-same-elements-ideal-Ring R
      ( ideal-congruence-Ring R (congruence-ideal-Ring R I))
      ( I)
      ( has-same-elements-ideal-congruence-Ring)
```

#### The congruence relation of the ideal obtained from a congruence relation `S` is `S` itself

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : congruence-Ring l2 R)
  where

  relate-same-elements-congruence-ideal-congruence-Ring :
    relate-same-elements-congruence-Ring R
      ( congruence-ideal-Ring R (ideal-congruence-Ring R S))
      ( S)
  pr1
    ( relate-same-elements-congruence-ideal-congruence-Ring x y) H =
    binary-tr
      ( sim-congruence-Ring R S)
      ( right-unit-law-add-Ring R x)
      ( is-section-left-subtraction-Ring R x y)
      ( left-add-congruence-Ring R S x H)
  pr2
    ( relate-same-elements-congruence-ideal-congruence-Ring x y) H =
    symmetric-congruence-Ring R S
      ( left-subtraction-Ring R x y)
      ( zero-Ring R)
      ( map-sim-left-subtraction-zero-congruence-Ring R S H)

  is-section-ideal-congruence-Ring :
    congruence-ideal-Ring R (ideal-congruence-Ring R S) ＝ S
  is-section-ideal-congruence-Ring =
    eq-relate-same-elements-congruence-Ring R
      ( congruence-ideal-Ring R (ideal-congruence-Ring R S))
      ( S)
      ( relate-same-elements-congruence-ideal-congruence-Ring)
```

#### The equivalence of two sided ideals and congruence relations

```agda
module _
  {l1 l2 : Level} (R : Ring l1)
  where

  is-equiv-congruence-ideal-Ring :
    is-equiv (congruence-ideal-Ring {l1} {l2} R)
  is-equiv-congruence-ideal-Ring =
    is-equiv-is-invertible
      ( ideal-congruence-Ring R)
      ( is-section-ideal-congruence-Ring R)
      ( is-retraction-ideal-congruence-Ring R)

  equiv-congruence-ideal-Ring :
    ideal-Ring l2 R ≃ congruence-Ring l2 R
  pr1 equiv-congruence-ideal-Ring = congruence-ideal-Ring R
  pr2 equiv-congruence-ideal-Ring = is-equiv-congruence-ideal-Ring

  is-equiv-ideal-congruence-Ring :
    is-equiv (ideal-congruence-Ring {l1} {l2} R)
  is-equiv-ideal-congruence-Ring =
    is-equiv-is-invertible
      ( congruence-ideal-Ring R)
      ( is-retraction-ideal-congruence-Ring R)
      ( is-section-ideal-congruence-Ring R)

  equiv-ideal-congruence-Ring :
    congruence-Ring l2 R ≃ ideal-Ring l2 R
  pr1 equiv-ideal-congruence-Ring = ideal-congruence-Ring R
  pr2 equiv-ideal-congruence-Ring = is-equiv-ideal-congruence-Ring
```
