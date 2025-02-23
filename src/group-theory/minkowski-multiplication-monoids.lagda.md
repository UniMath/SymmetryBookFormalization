# Minkowski multiplication on subsets of a monoid

```agda
module group-theory.minkowski-multiplication-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.powersets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.minkowski-multiplication-semigroups
open import group-theory.monoids
open import group-theory.semigroups
open import group-theory.subsets-monoids
```

</details>

## Idea

Given two [subsets](group-theory.subsets-monoids.md) `A` and `B` of a
[monoid](group-theory.monoids.md) `M`, the
{{#concept "Minkowski multiplication" Disambiguation="on subsets of a monoid" WD="Minkowski addition" WDID=Q1322294  Agda=minkowski-mul-Monoid}}
of `A` and `B` is the [set](foundation-core.sets.md) of elements that can be
formed by multiplying an element of `A` and an element of `B`. This binary
operation defines a monoid structure on the [powerset](foundation.powersets.md)
of `M`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (M : Monoid l1)
  (A : subset-Monoid l2 M)
  (B : subset-Monoid l3 M)
  where

  minkowski-mul-Monoid : subset-Monoid (l1 ⊔ l2 ⊔ l3) M
  minkowski-mul-Monoid = minkowski-mul-Semigroup (semigroup-Monoid M) A B
```

## Properties

### Minkowski multiplication on subsets of a monoid is associative

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Monoid l1)
  (A : subset-Monoid l2 M)
  (B : subset-Monoid l3 M)
  (C : subset-Monoid l4 M)
  where

  associative-minkowski-mul-Monoid :
    minkowski-mul-Monoid M (minkowski-mul-Monoid M A B) C ＝
    minkowski-mul-Monoid M A (minkowski-mul-Monoid M B C)
  associative-minkowski-mul-Monoid =
    associative-minkowski-mul-Semigroup (semigroup-Monoid M) A B C
```

### Unit laws for Minkowski multiplication on subsets of a monoid

```agda
module _
  {l1 l2 : Level}
  (M : Monoid l1)
  (A : subset-Monoid l2 M)
  where

  left-unit-law-minkowski-mul-Monoid :
    sim-subtype (minkowski-mul-Monoid M (is-unit-Monoid-Prop M) A) A
  pr1 left-unit-law-minkowski-mul-Monoid a =
    elim-exists
      ( A a)
      ( λ (z , a') (z=1 , a'∈A , a=za') →
        tr
          ( is-in-subtype A)
          ( inv
            ( equational-reasoning
              a
              ＝ mul-Monoid M z a' by a=za'
              ＝ mul-Monoid M (unit-Monoid M) a' by ap (mul-Monoid' M a') z=1
              ＝ a' by left-unit-law-mul-Monoid M a'))
          ( a'∈A))
  pr2 left-unit-law-minkowski-mul-Monoid a a∈A =
    intro-exists
      ( unit-Monoid M , a)
      ( refl , a∈A , inv (left-unit-law-mul-Monoid M a))

  right-unit-law-minkowski-mul-Monoid :
    sim-subtype (minkowski-mul-Monoid M A (is-unit-Monoid-Prop M)) A
  pr1 right-unit-law-minkowski-mul-Monoid a =
    elim-exists
      ( A a)
      ( λ (a' , z) (a'∈A , z=1 , a=a'z) →
        tr
          ( is-in-subtype A)
          ( inv
            ( equational-reasoning
              a
              ＝ mul-Monoid M a' z by a=a'z
              ＝ mul-Monoid M a' (unit-Monoid M) by ap (mul-Monoid M a') z=1
              ＝ a' by right-unit-law-mul-Monoid M a'))
          ( a'∈A))
  pr2 right-unit-law-minkowski-mul-Monoid a a∈A =
    intro-exists
      ( a , unit-Monoid M)
      ( a∈A , refl , inv (right-unit-law-mul-Monoid M a))
```

### Minkowski multiplication on subsets of a monoid forms a monoid

```agda
module _
  {l : Level}
  (M : Monoid l)
  where

  is-unital-minkowski-mul-Monoid :
    is-unital (minkowski-mul-Monoid {l} {l} {l} M)
  pr1 is-unital-minkowski-mul-Monoid = is-unit-Monoid-Prop M
  pr1 (pr2 is-unital-minkowski-mul-Monoid) A =
    eq-sim-subtype
      ( minkowski-mul-Monoid M (is-unit-Monoid-Prop M) A)
      ( A)
      ( left-unit-law-minkowski-mul-Monoid M A)
  pr2 (pr2 is-unital-minkowski-mul-Monoid) A =
    eq-sim-subtype
      ( minkowski-mul-Monoid M A (is-unit-Monoid-Prop M))
      ( A)
      ( right-unit-law-minkowski-mul-Monoid M A)

  monoid-minkowski-mul-Monoid : Monoid (lsuc l)
  pr1 monoid-minkowski-mul-Monoid =
    semigroup-minkowski-mul-Semigroup (semigroup-Monoid M)
  pr2 monoid-minkowski-mul-Monoid = is-unital-minkowski-mul-Monoid
```

### The Minkowski multiplication of two inhabited subsets of a monoid is inhabited

```agda
module _
  {l1 : Level}
  (M : Monoid l1)
  where

  minkowski-mul-inhabited-is-inhabited-Monoid :
    {l2 l3 : Level} →
    (A : subset-Monoid l2 M) →
    (B : subset-Monoid l3 M) →
    is-inhabited-subtype A →
    is-inhabited-subtype B →
    is-inhabited-subtype (minkowski-mul-Monoid M A B)
  minkowski-mul-inhabited-is-inhabited-Monoid =
    minkowski-mul-inhabited-is-inhabited-Semigroup (semigroup-Monoid M)
```

### Containment of subsets is preserved by Minkowski multiplication

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Monoid l1)
  (B : subset-Monoid l2 M)
  (A : subset-Monoid l3 M)
  (A' : subset-Monoid l4 M)
  where

  preserves-leq-left-minkowski-mul-Monoid :
    A ⊆ A' → minkowski-mul-Monoid M A B ⊆ minkowski-mul-Monoid M A' B
  preserves-leq-left-minkowski-mul-Monoid =
    preserves-leq-left-minkowski-mul-Semigroup (semigroup-Monoid M) B A A'

  preserves-leq-right-minkowski-mul-Monoid :
    A ⊆ A' → minkowski-mul-Monoid M B A ⊆ minkowski-mul-Monoid M B A'
  preserves-leq-right-minkowski-mul-Monoid =
    preserves-leq-right-minkowski-mul-Semigroup (semigroup-Monoid M) B A A'
```

### Similarity of subsets is preserved by Minkowski multiplication

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Monoid l1)
  (B : subset-Monoid l2 M)
  (A : subset-Monoid l3 M)
  (A' : subset-Monoid l4 M)
  where

  preserves-sim-left-minkowski-mul-Monoid :
    sim-subtype A A' →
    sim-subtype (minkowski-mul-Monoid M A B) (minkowski-mul-Monoid M A' B)
  preserves-sim-left-minkowski-mul-Monoid =
    preserves-sim-left-minkowski-mul-Semigroup (semigroup-Monoid M) B A A'

  preserves-sim-right-minkowski-mul-Monoid :
    sim-subtype A A' →
    sim-subtype (minkowski-mul-Monoid M B A) (minkowski-mul-Monoid M B A')
  preserves-sim-right-minkowski-mul-Monoid =
    preserves-sim-right-minkowski-mul-Semigroup (semigroup-Monoid M) B A A'

module _
  {l1 l2 l3 l4 l5 : Level}
  (M : Monoid l1)
  (A : subset-Monoid l2 M)
  (A' : subset-Monoid l3 M)
  (B : subset-Monoid l4 M)
  (B' : subset-Monoid l5 M)
  where

  preserves-sim-minkowski-mul-Monoid :
    sim-subtype A A' →
    sim-subtype B B' →
    sim-subtype
      ( minkowski-mul-Monoid M A B)
      ( minkowski-mul-Monoid M A' B')
  preserves-sim-minkowski-mul-Monoid =
    preserves-sim-minkowski-mul-Semigroup (semigroup-Monoid M) A A' B B'
```

## See also

- Minkowski multiplication on semigroups is defined in
  [`group-theory.minkowski-multiplication-semigroups`](group-theory.minkowski-multiplication-semigroups.md).
- Minkowski multiplication on commutative monoids is defined in
  [`group-theory.minkowski-multiplication-commutative-monoids`](group-theory.minkowski-multiplication-commutative-monoids.md).

## External links

- [Minkowski addition](https://en.wikipedia.org/wiki/Minkowski_addition) at
  Wikipedia
