# Multiplicative decompositions of natural numbers

```agda
module
  elementary-number-theory.multiplicative-decompositions-natural-numbers
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.products-lists-of-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nontrivial-divisors-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import lists.concatenation-lists
open import lists.lists
open import lists.universal-quantification-lists
```

</details>

## Idea

A
{{#concept "multiplicative decomposition" Disambiguation="natural numbers" Agda=is-multiplicative-decomposition-ℕ}}
of a [natural number](elementary-number-theory.natural-numbers.md) `n` is a
[list](lists.lists.md) `l` of natural numbers
[strictly greater than](elementary-number-theory.strict-inequality-natural-numbers.md)
`1`, such that the
[product](elementary-number-theory.products-lists-of-natural-numbers.md) of the
numbers in this list is [equal to](foundation-core.identity-types.md) `n`.

## Definitions

### The predicate on lists of natural numbers of being a product decomposition of a given number

```agda
module _
  (n : ℕ)
  (l : list ℕ)
  where

  is-multiplicative-decomposition-list-ℕ :
    UU lzero
  is-multiplicative-decomposition-list-ℕ =
    ( for-all-list l (le-ℕ 1)) × (mul-list-ℕ l ＝ n)

  is-prop-is-multiplicative-decomposition-list-ℕ :
    is-prop (is-multiplicative-decomposition-list-ℕ)
  is-prop-is-multiplicative-decomposition-list-ℕ =
    is-prop-product
      ( is-prop-for-all-list l (le-ℕ-Prop 1))
      ( is-set-ℕ (mul-list-ℕ l) n)

  le-one-list-is-multiplicative-decomposition-list-ℕ :
    is-multiplicative-decomposition-list-ℕ →
    for-all-list l (le-ℕ 1)
  le-one-list-is-multiplicative-decomposition-list-ℕ = pr1

  eq-is-multiplicative-decomposition-list-ℕ :
    is-multiplicative-decomposition-list-ℕ →
    mul-list-ℕ l ＝ n
  eq-is-multiplicative-decomposition-list-ℕ = pr2
```

## Properties

### Any list of numbers strictly greater than 1 is a multiplicative decomposition of its product

```agda
is-multiplicative-decomposition-mul-list-ℕ :
  (l : list ℕ) →
  for-all-list l (le-ℕ 1) →
  is-multiplicative-decomposition-list-ℕ (mul-list-ℕ l) l
pr1 (is-multiplicative-decomposition-mul-list-ℕ l H) = H
pr2 (is-multiplicative-decomposition-mul-list-ℕ l H) = refl
```

### The head and tail of a multiplicative decomposition of a number are strictly greater than 1

```agda
module _
  (n x : ℕ) (l : list ℕ)
  where

  le-one-head-is-multiplicative-decomposition-cons-list-ℕ :
    is-multiplicative-decomposition-list-ℕ n (cons x l) →
    1 <-ℕ x
  le-one-head-is-multiplicative-decomposition-cons-list-ℕ H =
    pr1 (le-one-list-is-multiplicative-decomposition-list-ℕ n (cons x l) H)

  le-one-tail-list-is-multiplicative-decomposition-cons-list-ℕ :
    is-multiplicative-decomposition-list-ℕ n (cons x l) →
    for-all-list l (le-ℕ 1)
  le-one-tail-list-is-multiplicative-decomposition-cons-list-ℕ H =
    pr2 (le-one-list-is-multiplicative-decomposition-list-ℕ n (cons x l) H)
```

### If `l` is a multiplicative decomposition of a number `n`, then `l` is a list of nontrivial divisors of `l`

```agda
div-head-is-multiplicative-decomposition-cons-list-ℕ :
  (n x : ℕ) (l : list ℕ) →
  is-multiplicative-decomposition-list-ℕ n (cons x l) →
  div-ℕ x n
pr1 (div-head-is-multiplicative-decomposition-cons-list-ℕ n x l H) =
  mul-list-ℕ l
pr2 (div-head-is-multiplicative-decomposition-cons-list-ℕ n x l H) =
  commutative-mul-ℕ (mul-list-ℕ l) x ∙
  eq-is-multiplicative-decomposition-list-ℕ n (cons x l) H

div-tail-is-multiplicative-decomposition-cons-list-ℕ :
  (n x : ℕ) (l : list ℕ) →
  is-multiplicative-decomposition-list-ℕ n (cons x l) →
  div-ℕ (mul-list-ℕ l) n
pr1 (div-tail-is-multiplicative-decomposition-cons-list-ℕ n x l H) =
  x
pr2 (div-tail-is-multiplicative-decomposition-cons-list-ℕ n x l H) =
  eq-is-multiplicative-decomposition-list-ℕ n (cons x l) H

is-nontrivial-divisor-head-is-multiplicative-decomposition-cons-list-ℕ :
  (n x : ℕ) (l : list ℕ) →
  is-multiplicative-decomposition-list-ℕ n (cons x l) →
  is-nontrivial-divisor-ℕ n x
pr1
  ( is-nontrivial-divisor-head-is-multiplicative-decomposition-cons-list-ℕ
    n x l H) =
  le-one-head-is-multiplicative-decomposition-cons-list-ℕ n x l H
pr2
  ( is-nontrivial-divisor-head-is-multiplicative-decomposition-cons-list-ℕ
    n x l H) =
  div-head-is-multiplicative-decomposition-cons-list-ℕ n x l H

is-list-of-nontrivial-divisors-is-multiplicative-decomposition-list-ℕ :
  (n : ℕ) (l : list ℕ) →
  is-multiplicative-decomposition-list-ℕ n l →
  is-list-of-nontrivial-divisors-ℕ n l
is-list-of-nontrivial-divisors-is-multiplicative-decomposition-list-ℕ n nil H =
  raise-star
is-list-of-nontrivial-divisors-is-multiplicative-decomposition-list-ℕ
  ( n)
  ( cons x l)
  ( H) =
  ( is-nontrivial-divisor-head-is-multiplicative-decomposition-cons-list-ℕ
    n x l H ,
    is-list-of-nontrivial-divisors-div-ℕ
      ( mul-list-ℕ l)
      ( n)
      ( div-tail-is-multiplicative-decomposition-cons-list-ℕ n x l H)
      ( l)
      ( is-list-of-nontrivial-divisors-is-multiplicative-decomposition-list-ℕ
        ( mul-list-ℕ l)
        ( l)
        ( is-multiplicative-decomposition-mul-list-ℕ l
          ( le-one-tail-list-is-multiplicative-decomposition-cons-list-ℕ n x l
            ( H)))))
```

### The concatenation of two multiplicative decompositions is a multiplicative decomposition

```agda
is-multiplicative-decomposition-concat-list-ℕ :
  (n m : ℕ) (p q : list ℕ) →
  is-multiplicative-decomposition-list-ℕ n p →
  is-multiplicative-decomposition-list-ℕ m q →
  is-multiplicative-decomposition-list-ℕ (n *ℕ m) (concat-list p q)
pr1 (is-multiplicative-decomposition-concat-list-ℕ n m l k H K) =
  for-all-concat-list l k
    ( le-ℕ 1)
    ( le-one-list-is-multiplicative-decomposition-list-ℕ n l H)
    ( le-one-list-is-multiplicative-decomposition-list-ℕ m k K)
pr2 (is-multiplicative-decomposition-concat-list-ℕ n m l k H K) =
  compute-mul-concat-list-ℕ l k ∙
  ap-mul-ℕ
    ( eq-is-multiplicative-decomposition-list-ℕ n l H)
    ( eq-is-multiplicative-decomposition-list-ℕ m k K)
```
