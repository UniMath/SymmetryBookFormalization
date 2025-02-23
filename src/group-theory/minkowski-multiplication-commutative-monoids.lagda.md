# Minkowski multiplication of subsets of a commutative monoid

```agda
module group-theory.minkowski-multiplication-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.powersets
open import foundation.subtypes
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.minkowski-multiplication-monoids
open import group-theory.monoids
open import group-theory.subsets-commutative-monoids

open import logic.functoriality-existential-quantification
```

</details>

## Idea

Given two [subsets](group-theory.subsets-commutative-monoids.md) `A` and `B` of
a [commutative monoid](group-theory.commutative-monoids.md) `M`, the
{{#concept "Minkowski multiplication" Disambiguation="on subsets of a commutative monoid" WD="Minkowski addition" WDID=Q1322294 Agda=minkowski-mul-Commutative-Monoid}}
of `A` and `B` is the [set](foundation-core.sets.md) of elements that can be
formed by multiplying an element of `A` and an element of `B`. This binary
operation defines a commutative monoid structure on the
[powerset](foundation.powersets.md) of `M`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (M : Commutative-Monoid l1)
  (A : subset-Commutative-Monoid l2 M)
  (B : subset-Commutative-Monoid l3 M)
  where

  minkowski-mul-Commutative-Monoid :
    subset-Commutative-Monoid (l1 ⊔ l2 ⊔ l3) M
  minkowski-mul-Commutative-Monoid =
    minkowski-mul-Monoid (monoid-Commutative-Monoid M) A B
```

## Properties

### Minkowski multiplication on subsets of a commutative monoid is associative

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Commutative-Monoid l1)
  (A : subset-Commutative-Monoid l2 M)
  (B : subset-Commutative-Monoid l3 M)
  (C : subset-Commutative-Monoid l4 M)
  where

  associative-minkowski-mul-Commutative-Monoid :
    minkowski-mul-Commutative-Monoid
      ( M)
      ( minkowski-mul-Commutative-Monoid M A B)
      ( C) ＝
    minkowski-mul-Commutative-Monoid
      ( M)
      ( A)
      ( minkowski-mul-Commutative-Monoid M B C)
  associative-minkowski-mul-Commutative-Monoid =
    associative-minkowski-mul-Monoid (monoid-Commutative-Monoid M) A B C
```

### Minkowski multiplication on subsets of a commutative monoid is unital

```agda
module _
  {l1 l2 : Level}
  (M : Commutative-Monoid l1)
  (A : subset-Commutative-Monoid l2 M)
  where

  left-unit-law-minkowski-mul-Commutative-Monoid :
    sim-subtype
      ( minkowski-mul-Commutative-Monoid
        ( M)
        ( is-unit-prop-Commutative-Monoid M)
        ( A))
      ( A)
  left-unit-law-minkowski-mul-Commutative-Monoid =
    left-unit-law-minkowski-mul-Monoid (monoid-Commutative-Monoid M) A

  right-unit-law-minkowski-mul-Commutative-Monoid :
    sim-subtype
      ( minkowski-mul-Commutative-Monoid
        ( M)
        ( A)
        ( is-unit-prop-Commutative-Monoid M))
      ( A)
  right-unit-law-minkowski-mul-Commutative-Monoid =
    right-unit-law-minkowski-mul-Monoid (monoid-Commutative-Monoid M) A
```

### Minkowski multiplication on a commutative monoid is unital

```agda
module _
  {l : Level}
  (M : Commutative-Monoid l)
  where

  is-unital-minkowski-mul-Commutative-Monoid :
    is-unital (minkowski-mul-Commutative-Monoid {l} {l} {l} M)
  is-unital-minkowski-mul-Commutative-Monoid =
    is-unital-minkowski-mul-Monoid (monoid-Commutative-Monoid M)
```

### Minkowski multiplication on subsets of a commutative monoid is commutative

```agda
module _
  {l1 l2 l3 : Level}
  (M : Commutative-Monoid l1)
  (A : subset-Commutative-Monoid l2 M)
  (B : subset-Commutative-Monoid l3 M)
  where

  commutative-minkowski-mul-leq-Commutative-Monoid :
    minkowski-mul-Commutative-Monoid M A B ⊆
    minkowski-mul-Commutative-Monoid M B A
  commutative-minkowski-mul-leq-Commutative-Monoid x =
    elim-exists
      ( minkowski-mul-Commutative-Monoid M B A x)
      ( λ (a , b) (a∈A , b∈B , x=ab) →
        intro-exists
          ( b , a)
          ( b∈B , a∈A , x=ab ∙ commutative-mul-Commutative-Monoid M a b))

module _
  {l1 l2 l3 : Level}
  (M : Commutative-Monoid l1)
  (A : subset-Commutative-Monoid l2 M)
  (B : subset-Commutative-Monoid l3 M)
  where

  commutative-minkowski-mul-Commutative-Monoid :
    minkowski-mul-Commutative-Monoid M A B ＝
    minkowski-mul-Commutative-Monoid M B A
  commutative-minkowski-mul-Commutative-Monoid =
    eq-sim-subtype
      ( minkowski-mul-Commutative-Monoid M A B)
      ( minkowski-mul-Commutative-Monoid M B A)
      ( commutative-minkowski-mul-leq-Commutative-Monoid M A B ,
        commutative-minkowski-mul-leq-Commutative-Monoid M B A)
```

### Minkowski multiplication on subsets of a commutative monoid is a commutative monoid

```agda
module _
  {l : Level}
  (M : Commutative-Monoid l)
  where

  commutative-monoid-minkowski-mul-Commutative-Monoid :
    Commutative-Monoid (lsuc l)
  pr1 commutative-monoid-minkowski-mul-Commutative-Monoid =
    monoid-minkowski-mul-Monoid (monoid-Commutative-Monoid M)
  pr2 commutative-monoid-minkowski-mul-Commutative-Monoid =
    commutative-minkowski-mul-Commutative-Monoid M
```

### The Minkowski multiplication of two inhabited subsets is inhabited

```agda
module _
  {l1 : Level}
  (M : Commutative-Monoid l1)
  where

  minkowski-mul-inhabited-is-inhabited-Commutative-Monoid :
    {l2 l3 : Level} →
    (A : subset-Commutative-Monoid l2 M) →
    (B : subset-Commutative-Monoid l3 M) →
    is-inhabited-subtype A →
    is-inhabited-subtype B →
    is-inhabited-subtype (minkowski-mul-Commutative-Monoid M A B)
  minkowski-mul-inhabited-is-inhabited-Commutative-Monoid =
    minkowski-mul-inhabited-is-inhabited-Monoid (monoid-Commutative-Monoid M)
```

### Containment of subsets is preserved by Minkowski multiplication

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Commutative-Monoid l1)
  (B : subset-Commutative-Monoid l2 M)
  (A : subset-Commutative-Monoid l3 M)
  (A' : subset-Commutative-Monoid l4 M)
  where

  preserves-leq-left-minkowski-mul-Commutative-Monoid :
    A ⊆ A' →
    minkowski-mul-Commutative-Monoid M A B ⊆
    minkowski-mul-Commutative-Monoid M A' B
  preserves-leq-left-minkowski-mul-Commutative-Monoid =
    preserves-leq-left-minkowski-mul-Monoid (monoid-Commutative-Monoid M) B A A'

  preserves-leq-right-minkowski-mul-Commutative-Monoid :
    A ⊆ A' →
    minkowski-mul-Commutative-Monoid M B A ⊆
    minkowski-mul-Commutative-Monoid M B A'
  preserves-leq-right-minkowski-mul-Commutative-Monoid =
    preserves-leq-right-minkowski-mul-Monoid
      ( monoid-Commutative-Monoid M)
      ( B)
      ( A)
      ( A')
```

### Similarity of subsets is preserved by Minkowski multiplication

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Commutative-Monoid l1)
  (B : subset-Commutative-Monoid l2 M)
  (A : subset-Commutative-Monoid l3 M)
  (A' : subset-Commutative-Monoid l4 M)
  where

  preserves-sim-left-minkowski-mul-Commutative-Monoid :
    sim-subtype A A' →
    sim-subtype
      ( minkowski-mul-Commutative-Monoid M A B)
      ( minkowski-mul-Commutative-Monoid M A' B)
  preserves-sim-left-minkowski-mul-Commutative-Monoid =
    preserves-sim-left-minkowski-mul-Monoid (monoid-Commutative-Monoid M) B A A'

  preserves-sim-right-minkowski-mul-Commutative-Monoid :
    sim-subtype A A' →
    sim-subtype
      ( minkowski-mul-Commutative-Monoid M B A)
      ( minkowski-mul-Commutative-Monoid M B A')
  preserves-sim-right-minkowski-mul-Commutative-Monoid =
    preserves-sim-right-minkowski-mul-Monoid
      ( monoid-Commutative-Monoid M)
      ( B)
      ( A)
      ( A')

module _
  {l1 l2 l3 l4 l5 : Level}
  (M : Commutative-Monoid l1)
  (A : subset-Commutative-Monoid l2 M)
  (A' : subset-Commutative-Monoid l3 M)
  (B : subset-Commutative-Monoid l4 M)
  (B' : subset-Commutative-Monoid l5 M)
  where

  preserves-sim-minkowski-mul-Commutative-Monoid :
    sim-subtype A A' →
    sim-subtype B B' →
    sim-subtype
      ( minkowski-mul-Commutative-Monoid M A B)
      ( minkowski-mul-Commutative-Monoid M A' B')
  preserves-sim-minkowski-mul-Commutative-Monoid =
    preserves-sim-minkowski-mul-Monoid (monoid-Commutative-Monoid M) A A' B B'
```

## See also

- Minkowski multiplication on semigroups is defined in
  [`group-theory.minkowski-multiplication-semigroups`](group-theory.minkowski-multiplication-semigroups.md).
- Minkowski multiplication on monoids is defined in
  [`group-theory.minkowski-multiplication-monoids`](group-theory.minkowski-multiplication-monoids.md).

## External links

- [Minkowski addition](https://en.wikipedia.org/wiki/Minkowski_addition) at
  Wikipedia
