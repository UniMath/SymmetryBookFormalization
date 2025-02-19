# The fundamental theorem of arithmetic

```agda
module elementary-number-theory.fundamental-theorem-of-arithmetic where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.based-strong-induction-natural-numbers
open import elementary-number-theory.bezouts-lemma-integers
open import elementary-number-theory.decidable-total-order-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.lists-of-prime-numbers
open import elementary-number-theory.lower-bounds-natural-numbers
open import elementary-number-theory.minimal-structured-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.products-lists-of-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.multiplicative-decompositions-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nontrivial-divisors-natural-numbers
open import elementary-number-theory.prime-numbers
open import elementary-number-theory.relatively-prime-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels

open import lists.concatenation-lists
open import lists.elementhood-relation-lists
open import lists.functoriality-lists
open import lists.lists
open import lists.permutation-lists
open import lists.universal-quantification-lists
open import lists.sort-by-insertion-lists
open import lists.sorted-lists
```

</details>

## Idea

The
{{#concept "fundamental theorem of arithmetic" WD="fundamental theorem of arithmetic" WDID=Q670235 Agda=fundamental-theorem-arithmetic-list-ℕ}}
asserts that every
[nonzero](elementary-number-theory.nonzero-natural-numbers.md)
[natural number](elementary-number-theory.natural-numbers.md) can be written as
a [product](elementary-number-theory.products-of-natural-numbers.md) of
[primes](elementary-number-theory.prime-numbers.md), and this product is
[unique](foundation-core.contractible-types.md) up to the order of the factors.

The uniqueness of the prime factorization of a natural number can be expressed
in several ways:

- We can find a unique [list](lists.lists.md) of primes `p₁ ≤ p₂ ≤ ⋯ ≤ pᵢ` of
  which the product is equal to `n`
- The type of [finite sets](univalent-combinatorics.finite-types.md) `X`
  [equipped](foundation.structure.md) with functions `p : X → Σ ℕ is-prime-ℕ`
  and `m : X → positive-ℕ` such that the product of `pₓᵐ⁽ˣ⁾` is
  [equal](foundation-core.identity-types.md) to `n` is contractible.

Note that the [univalence axiom](foundation-core.univalence.md) is neccessary to
prove the second uniqueness property of prime factorizations. On this page we
will prove the fundamental theorem using the first approach.

The fundamental theorem of arithmetic is the
[80th](literature.100-theorems.md#80) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

## Definitions

### Prime decomposition of a natural number with lists

A list of natural numbers is a prime decomposition of a natural number `n` if:

- The list is sorted.
- Every element of the list is prime.
- The list is a
  [multiplicative decomposition](elementary-number-theory.multiplicative-decompositions-natural-numbers.md)
  of `n`.

```agda
module _
  (x : ℕ)
  (l : list ℕ)
  where

  is-prime-decomposition-list-ℕ :
    UU lzero
  is-prime-decomposition-list-ℕ =
    is-sorted-list ℕ-Decidable-Total-Order l ×
    ( is-prime-list-ℕ l ×
      is-multiplicative-decomposition-list-ℕ x l)

  is-sorted-is-prime-decomposition-list-ℕ :
    is-prime-decomposition-list-ℕ →
    is-sorted-list ℕ-Decidable-Total-Order l
  is-sorted-is-prime-decomposition-list-ℕ D =
    pr1 D

  is-prime-list-is-prime-decomposition-list-ℕ :
    is-prime-decomposition-list-ℕ → is-prime-list-ℕ l
  is-prime-list-is-prime-decomposition-list-ℕ D =
    pr1 (pr2 D)

  is-multiplicative-decomposition-is-prime-decomposition-list-ℕ :
    is-prime-decomposition-list-ℕ →
    is-multiplicative-decomposition-list-ℕ x l
  is-multiplicative-decomposition-is-prime-decomposition-list-ℕ D =
    pr2 (pr2 D)

  le-one-list-is-prime-decomposition-list-ℕ :
    is-prime-decomposition-list-ℕ →
    for-all-list l (le-ℕ 1)
  le-one-list-is-prime-decomposition-list-ℕ H =
    map-for-all-list l
      ( le-one-is-prime-ℕ)
      ( is-prime-list-is-prime-decomposition-list-ℕ H)

  leq-one-list-is-prime-decomposition-list-ℕ :
    is-prime-decomposition-list-ℕ →
    for-all-list l (leq-ℕ 1)
  leq-one-list-is-prime-decomposition-list-ℕ H =
    map-for-all-list l
      ( leq-le-ℕ 1)
      ( le-one-list-is-prime-decomposition-list-ℕ H)

  eq-is-prime-decomposition-list-ℕ :
    is-prime-decomposition-list-ℕ →
    mul-list-ℕ l ＝ x
  eq-is-prime-decomposition-list-ℕ H =
    pr2 (is-multiplicative-decomposition-is-prime-decomposition-list-ℕ H)

  leq-one-is-prime-decomposition-list-ℕ :
    is-prime-decomposition-list-ℕ → 1 ≤-ℕ x
  leq-one-is-prime-decomposition-list-ℕ H =
    tr
      ( leq-ℕ 1)
      ( eq-is-prime-decomposition-list-ℕ H)
      ( leq-one-mul-list-ℕ l (leq-one-list-is-prime-decomposition-list-ℕ H))

  is-list-of-nontrivial-divisors-is-prime-dicomposition-list-ℕ :
    is-prime-decomposition-list-ℕ →
    is-list-of-nontrivial-divisors-ℕ x l
  is-list-of-nontrivial-divisors-is-prime-dicomposition-list-ℕ H =
    is-list-of-nontrivial-divisors-is-multiplicative-decomposition-list-ℕ x l
      ( is-multiplicative-decomposition-is-prime-decomposition-list-ℕ H)

  is-list-of-nontrivial-divisors-is-prime-decomposition-list-ℕ :
    is-prime-decomposition-list-ℕ →
    is-list-of-nontrivial-divisors-ℕ x l
  is-list-of-nontrivial-divisors-is-prime-decomposition-list-ℕ D =
    is-list-of-nontrivial-divisors-is-multiplicative-decomposition-list-ℕ x l
      ( is-multiplicative-decomposition-is-prime-decomposition-list-ℕ D)

  is-prop-is-prime-decomposition-list-ℕ :
    is-prop (is-prime-decomposition-list-ℕ)
  is-prop-is-prime-decomposition-list-ℕ =
    is-prop-product
      ( is-prop-is-sorted-list ℕ-Decidable-Total-Order l)
      ( is-prop-product
        ( is-prop-is-prime-list-ℕ l)
        ( is-prop-is-multiplicative-decomposition-list-ℕ x l))

  is-prime-decomposition-list-ℕ-Prop : Prop lzero
  pr1 is-prime-decomposition-list-ℕ-Prop = is-prime-decomposition-list-ℕ
  pr2 is-prime-decomposition-list-ℕ-Prop = is-prop-is-prime-decomposition-list-ℕ

module _
  (x y : ℕ) (l : list ℕ) (H : is-prime-decomposition-list-ℕ x (cons y l))
  where

  is-prime-head-is-prime-decomposition-cons-list-ℕ :
    is-prime-ℕ y
  is-prime-head-is-prime-decomposition-cons-list-ℕ =
    pr1 (is-prime-list-is-prime-decomposition-list-ℕ x (cons y l) H)

  is-prime-tail-is-prime-decomposition-cons-list-ℕ :
    is-prime-list-ℕ l
  is-prime-tail-is-prime-decomposition-cons-list-ℕ =
    pr2 (is-prime-list-is-prime-decomposition-list-ℕ x (cons y l) H)

  le-one-head-is-prime-decomposition-cons-list-ℕ :
    1 <-ℕ y
  le-one-head-is-prime-decomposition-cons-list-ℕ =
    le-one-is-prime-ℕ y is-prime-head-is-prime-decomposition-cons-list-ℕ

  div-head-is-prime-decomposition-cons-list-ℕ :
    div-ℕ y x
  div-head-is-prime-decomposition-cons-list-ℕ =
    div-head-is-multiplicative-decomposition-cons-list-ℕ
      ( x)
      ( y)
      ( l)
      ( is-multiplicative-decomposition-is-prime-decomposition-list-ℕ x
        ( cons y l)
        ( H))

  quotient-head-is-prime-decomposition-cons-list-ℕ :
    ℕ
  quotient-head-is-prime-decomposition-cons-list-ℕ =
    quotient-div-ℕ y x div-head-is-prime-decomposition-cons-list-ℕ

  eq-quotient-head-is-prime-decomposition-cons-list-ℕ :
    quotient-head-is-prime-decomposition-cons-list-ℕ *ℕ y ＝ x
  eq-quotient-head-is-prime-decomposition-cons-list-ℕ =
    eq-quotient-div-ℕ y x div-head-is-prime-decomposition-cons-list-ℕ

  leq-one-quotient-head-is-prime-decomposition-cons-list-ℕ :
    1 ≤-ℕ quotient-head-is-prime-decomposition-cons-list-ℕ
  leq-one-quotient-head-is-prime-decomposition-cons-list-ℕ =
    leq-one-quotient-div-ℕ y x
      ( div-head-is-prime-decomposition-cons-list-ℕ)
      ( leq-one-is-prime-decomposition-list-ℕ x (cons y l) H)

  is-nontrivial-divisor-head-is-prime-decomposition-cons-list-ℕ :
    is-nontrivial-divisor-ℕ x y
  is-nontrivial-divisor-head-is-prime-decomposition-cons-list-ℕ =
    is-nontrivial-divisor-head-is-multiplicative-decomposition-cons-list-ℕ
      ( x)
      ( y)
      ( l)
      ( is-multiplicative-decomposition-is-prime-decomposition-list-ℕ x
        ( cons y l)
        ( H))

  le-one-is-prime-decomposition-cons-list-ℕ :
    le-ℕ 1 x
  le-one-is-prime-decomposition-cons-list-ℕ =
    concatenate-le-leq-ℕ 1 y x
      ( le-one-head-is-prime-decomposition-cons-list-ℕ)
      ( leq-div-ℕ
        ( y)
        ( x)
        ( is-nonzero-leq-one-ℕ x
          ( leq-one-is-prime-decomposition-list-ℕ x (cons y l) H))
        ( div-head-is-prime-decomposition-cons-list-ℕ))

  is-sorted-tail-is-prime-decomposition-cons-list-ℕ :
    is-sorted-list ℕ-Decidable-Total-Order l
  is-sorted-tail-is-prime-decomposition-cons-list-ℕ =
    is-sorted-tail-is-sorted-list
      ( ℕ-Decidable-Total-Order)
      ( cons y l)
      ( is-sorted-is-prime-decomposition-list-ℕ x (cons y l) H)

  le-one-tail-is-prime-decomposition-cons-list-ℕ :
    for-all-list l (le-ℕ 1)
  le-one-tail-is-prime-decomposition-cons-list-ℕ =
    pr2 (le-one-list-is-prime-decomposition-list-ℕ x (cons y l) H)

  compute-quotient-head-is-prime-decomposition-cons-list-ℕ :
    quotient-head-is-prime-decomposition-cons-list-ℕ ＝
    mul-list-ℕ l
  compute-quotient-head-is-prime-decomposition-cons-list-ℕ =
    is-injective-right-mul-ℕ y
      ( is-nonzero-is-prime-ℕ y
        ( is-prime-head-is-prime-decomposition-cons-list-ℕ))
      ( ( eq-quotient-head-is-prime-decomposition-cons-list-ℕ) ∙
        ( inv (eq-is-prime-decomposition-list-ℕ x (cons y l) H)) ∙
        ( commutative-mul-ℕ y (mul-list-ℕ l)))

  is-multiplicative-decomposition-tail-quotient-head-is-prime-decomposition-cons-list-ℕ :
    is-multiplicative-decomposition-list-ℕ
      ( quotient-head-is-prime-decomposition-cons-list-ℕ)
      ( l)
  pr1
    is-multiplicative-decomposition-tail-quotient-head-is-prime-decomposition-cons-list-ℕ =
    le-one-tail-is-prime-decomposition-cons-list-ℕ
  pr2
    is-multiplicative-decomposition-tail-quotient-head-is-prime-decomposition-cons-list-ℕ =
    inv compute-quotient-head-is-prime-decomposition-cons-list-ℕ

  is-prime-decomposition-tail-quotient-head-is-prime-decomposition-cons-list-ℕ :
    is-prime-decomposition-list-ℕ
      ( quotient-head-is-prime-decomposition-cons-list-ℕ)
      ( l)
  is-prime-decomposition-tail-quotient-head-is-prime-decomposition-cons-list-ℕ =
    ( is-sorted-tail-is-prime-decomposition-cons-list-ℕ ,
      is-prime-tail-is-prime-decomposition-cons-list-ℕ ,
      is-multiplicative-decomposition-tail-quotient-head-is-prime-decomposition-cons-list-ℕ)
```

### The type of prime decompositions of a natural number

```agda
prime-decomposition-list-ℕ :
  (x : ℕ) → UU lzero
prime-decomposition-list-ℕ x =
  Σ (list ℕ) (λ l → is-prime-decomposition-list-ℕ x l)
```

## The fundamental theorem of arithmetic

### Existence

#### The list of primes in the prime decomposition of a number

```agda
successor-step-list-of-primes-fundamental-theorem-arithmetic-ℕ :
  (n : ℕ) → 1 ≤-ℕ n → ((m : ℕ) → 1 ≤-ℕ m → m ≤-ℕ n → list Prime-ℕ) →
  list Prime-ℕ
successor-step-list-of-primes-fundamental-theorem-arithmetic-ℕ n N f =
  cons
    ( prime-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
    ( f
      ( quotient-div-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
      ( leq-one-quotient-div-ℕ
        ( nat-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
        ( succ-ℕ n)
        ( div-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
        ( leq-succ-leq-ℕ 1 n N))
      ( upper-bound-quotient-div-least-prime-divisor-ℕ n (le-succ-leq-ℕ 1 n N)))

list-of-primes-fundamental-theorem-arithmetic-ℕ :
  (n : ℕ) → 1 ≤-ℕ n → list Prime-ℕ
list-of-primes-fundamental-theorem-arithmetic-ℕ =
  based-strong-ind-ℕ 1
    ( λ n → list Prime-ℕ)
    ( nil)
    ( successor-step-list-of-primes-fundamental-theorem-arithmetic-ℕ)

list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) → 1 ≤-ℕ x → list ℕ
list-fundamental-theorem-arithmetic-ℕ x H =
  map-list nat-Prime-ℕ (list-of-primes-fundamental-theorem-arithmetic-ℕ x H)
```

#### Computation rules for the list of primes in the prime decomposition of a number

```agda
compute-list-of-primes-fundamental-theorem-arithmetic-succ-ℕ :
  (x : ℕ) (H : 1 ≤-ℕ x) →
  list-of-primes-fundamental-theorem-arithmetic-ℕ (succ-ℕ x) star ＝
  cons
    ( prime-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
    ( list-of-primes-fundamental-theorem-arithmetic-ℕ
      ( quotient-div-least-prime-divisor-ℕ
        ( succ-ℕ x)
        ( le-succ-leq-ℕ 1 x H))
      ( leq-one-quotient-div-ℕ
        ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( succ-ℕ x)
        ( div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( leq-succ-leq-ℕ 1 x H)))
compute-list-of-primes-fundamental-theorem-arithmetic-succ-ℕ x H =
  compute-succ-based-strong-ind-ℕ
    ( 1)
    ( λ _ → list Prime-ℕ)
    ( nil)
    ( successor-step-list-of-primes-fundamental-theorem-arithmetic-ℕ)
    ( x)
    ( H)
    ( star)

compute-list-fundamental-theorem-arithmetic-succ-ℕ :
  (x : ℕ) (H : 1 ≤-ℕ x) →
  list-fundamental-theorem-arithmetic-ℕ (succ-ℕ x) _ ＝
  cons
    ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
    ( list-fundamental-theorem-arithmetic-ℕ
      ( quotient-div-least-prime-divisor-ℕ
        ( succ-ℕ x)
        ( le-succ-leq-ℕ 1 x H))
      ( leq-one-quotient-div-ℕ
        ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( succ-ℕ x)
        ( div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( leq-succ-leq-ℕ 1 x H)))
compute-list-fundamental-theorem-arithmetic-succ-ℕ x H =
  ap
    ( map-list nat-Prime-ℕ)
    ( compute-list-of-primes-fundamental-theorem-arithmetic-succ-ℕ x H)
```

#### The list of primes in the prime decomposition of a number is a prime decomposition

```agda
is-prime-list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) (H : 1 ≤-ℕ x) →
  is-prime-list-ℕ (list-fundamental-theorem-arithmetic-ℕ x H)
is-prime-list-fundamental-theorem-arithmetic-ℕ x H =
  is-prime-list-list-Prime-ℕ
    ( list-of-primes-fundamental-theorem-arithmetic-ℕ x H)

le-one-list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) (H : 1 ≤-ℕ x) →
  for-all-list (list-fundamental-theorem-arithmetic-ℕ x H) (le-ℕ 1)
le-one-list-fundamental-theorem-arithmetic-ℕ x H =
  map-for-all-list
    ( list-fundamental-theorem-arithmetic-ℕ x H)
    ( le-one-is-prime-ℕ)
    ( is-prime-list-fundamental-theorem-arithmetic-ℕ x H)

is-multiplicative-decomposition-list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) (H : 1 ≤-ℕ x) →
  is-multiplicative-decomposition-list-ℕ x
    ( list-fundamental-theorem-arithmetic-ℕ x H)
is-multiplicative-decomposition-list-fundamental-theorem-arithmetic-ℕ =
  based-strong-ind-ℕ' 1
    ( λ n N →
      is-multiplicative-decomposition-list-ℕ n
        ( list-fundamental-theorem-arithmetic-ℕ n N))
    ( for-all-nil-list (le-ℕ 1) , refl)
    ( λ n N f →
      ( le-one-list-fundamental-theorem-arithmetic-ℕ (succ-ℕ n) star) ,
      ( ( ap
          ( mul-list-ℕ)
          ( compute-list-fundamental-theorem-arithmetic-succ-ℕ n N)) ∙
        ( ap
          ( ( nat-least-prime-divisor-ℕ
              ( succ-ℕ n)
              ( le-succ-leq-ℕ 1 n N)) *ℕ_)
          ( pr2
            ( f
              ( quotient-div-least-prime-divisor-ℕ
                ( succ-ℕ n)
                ( le-succ-leq-ℕ 1 n N))
              ( leq-one-quotient-div-ℕ
                ( nat-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
                ( succ-ℕ n)
                ( div-least-prime-divisor-ℕ (succ-ℕ n) (le-succ-leq-ℕ 1 n N))
                ( leq-succ-leq-ℕ 1 n N))
              ( upper-bound-quotient-div-least-prime-divisor-ℕ
                ( n)
                ( le-succ-leq-ℕ 1 n N))))) ∙
        ( eq-quotient-div-ℕ'
          ( nat-least-prime-divisor-ℕ
            ( succ-ℕ n)
            ( le-succ-leq-ℕ 1 n N))
          ( succ-ℕ n)
          ( div-least-prime-divisor-ℕ
            ( succ-ℕ n)
            ( le-succ-leq-ℕ 1 n N)))))

is-list-of-nontrivial-divisors-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) (H : 1 ≤-ℕ x) →
  is-list-of-nontrivial-divisors-ℕ x (list-fundamental-theorem-arithmetic-ℕ x H)
is-list-of-nontrivial-divisors-fundamental-theorem-arithmetic-ℕ x H =
  is-list-of-nontrivial-divisors-is-multiplicative-decomposition-list-ℕ
    ( x)
    ( list-fundamental-theorem-arithmetic-ℕ x H)
    ( is-multiplicative-decomposition-list-fundamental-theorem-arithmetic-ℕ x H)

is-least-element-list-least-prime-divisor-ℕ :
  (x : ℕ) (H : 1 ≤-ℕ x) (l : list ℕ) →
  is-list-of-nontrivial-divisors-ℕ
    ( quotient-div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
    ( l) →
  is-least-element-list
    ( ℕ-Decidable-Total-Order)
    ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
    ( l)
is-least-element-list-least-prime-divisor-ℕ x H nil D = raise-star
is-least-element-list-least-prime-divisor-ℕ x H (cons y l) D =
  ( is-minimal-least-nontrivial-divisor-ℕ
    ( succ-ℕ x)
    ( le-succ-leq-ℕ 1 x H)
    ( y)
    ( pr1 (pr1 D))
    ( transitive-div-ℕ
      ( y)
      ( quotient-div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
      ( succ-ℕ x)
      ( div-quotient-div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
      ( pr2 (pr1 D))) ,
    is-least-element-list-least-prime-divisor-ℕ x H l (pr2 D))

is-least-element-head-list-fundamental-theorem-arithmetic-succ-ℕ :
  (x : ℕ) (H : 1 ≤-ℕ x) →
  is-least-element-list
    ( ℕ-Decidable-Total-Order)
    ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
    ( list-fundamental-theorem-arithmetic-ℕ
      ( quotient-div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
      ( leq-one-quotient-div-ℕ
        ( nat-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( succ-ℕ x)
        ( div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
        ( leq-succ-leq-ℕ 1 x H)))
is-least-element-head-list-fundamental-theorem-arithmetic-succ-ℕ x H =
  is-least-element-list-least-prime-divisor-ℕ
    ( x)
    ( H)
    ( list-fundamental-theorem-arithmetic-ℕ
      ( quotient-div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
      ( leq-one-quotient-div-least-prime-divisor-ℕ
        ( succ-ℕ x)
        ( le-succ-leq-ℕ 1 x H)))
    ( is-list-of-nontrivial-divisors-fundamental-theorem-arithmetic-ℕ
      ( quotient-div-least-prime-divisor-ℕ (succ-ℕ x) (le-succ-leq-ℕ 1 x H))
      ( leq-one-quotient-div-least-prime-divisor-ℕ
        ( succ-ℕ x)
        ( le-succ-leq-ℕ 1 x H)))

is-sorted-least-element-list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) (H : 1 ≤-ℕ x) →
  is-sorted-least-element-list
    ( ℕ-Decidable-Total-Order)
    ( list-fundamental-theorem-arithmetic-ℕ x H)
is-sorted-least-element-list-fundamental-theorem-arithmetic-ℕ x H =
  based-strong-ind-ℕ' 1
    ( λ x H →
      is-sorted-least-element-list
        ( ℕ-Decidable-Total-Order)
        ( list-fundamental-theorem-arithmetic-ℕ x H))
    ( raise-star)
    ( λ n N f →
      tr
        ( λ l →
          is-sorted-least-element-list
            ( ℕ-Decidable-Total-Order)
            ( l))
        ( inv (compute-list-fundamental-theorem-arithmetic-succ-ℕ n N))
        ( is-least-element-head-list-fundamental-theorem-arithmetic-succ-ℕ n N ,
          f ( quotient-div-least-prime-divisor-ℕ
              ( succ-ℕ n)
              ( le-succ-leq-ℕ 1 n N))
            ( leq-one-quotient-div-least-prime-divisor-ℕ
              ( succ-ℕ n)
              ( le-succ-leq-ℕ 1 n N))
            ( upper-bound-quotient-div-least-prime-divisor-ℕ n
              ( le-succ-leq-ℕ 1 n N))))
    ( x)
    ( H)

is-sorted-list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) (H : 1 ≤-ℕ x) →
  is-sorted-list
    ( ℕ-Decidable-Total-Order)
    ( list-fundamental-theorem-arithmetic-ℕ x H)
is-sorted-list-fundamental-theorem-arithmetic-ℕ x H =
  is-sorted-list-is-sorted-least-element-list
    ( ℕ-Decidable-Total-Order)
    ( list-fundamental-theorem-arithmetic-ℕ x H)
    ( is-sorted-least-element-list-fundamental-theorem-arithmetic-ℕ x H)

is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) (H : 1 ≤-ℕ x) →
  is-prime-decomposition-list-ℕ x (list-fundamental-theorem-arithmetic-ℕ x H)
pr1 (is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕ x H) =
  is-sorted-list-fundamental-theorem-arithmetic-ℕ x H
pr1 (pr2 (is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕ x H)) =
  is-prime-list-fundamental-theorem-arithmetic-ℕ x H
pr2 (pr2 (is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕ x H)) =
  is-multiplicative-decomposition-list-fundamental-theorem-arithmetic-ℕ x H

prime-decomposition-fundamental-theorem-arithmetic-ℕ :
  (x : ℕ) (H : 1 ≤-ℕ x) → prime-decomposition-list-ℕ x
pr1 (prime-decomposition-fundamental-theorem-arithmetic-ℕ x H) =
  list-fundamental-theorem-arithmetic-ℕ x H
pr2 (prime-decomposition-fundamental-theorem-arithmetic-ℕ x H) =
  is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕ x H
```

### Uniqueness

#### The type of prime decompositions of any natural number is contractible

```agda
is-in-prime-decomposition-is-prime-divisor-ℕ :
  (x : ℕ) (H : 1 ≤-ℕ x) (l : list ℕ) → is-prime-decomposition-list-ℕ x l →
  (y : ℕ) → div-ℕ y x → is-prime-ℕ y → y ∈-list l
is-in-prime-decomposition-is-prime-divisor-ℕ x H nil D y d p =
  ex-falso
    ( no-prime-divisors-one-ℕ y p
      ( tr (div-ℕ y) (inv (eq-is-prime-decomposition-list-ℕ x nil D)) d))
is-in-prime-decomposition-is-prime-divisor-ℕ x H (cons z l) D y d p =
  rec-coproduct
    ( λ p → tr (_∈-list cons z l) (inv p) (is-head z l))
    ( λ e →
      is-in-tail y z l
        ( is-in-prime-decomposition-is-prime-divisor-ℕ
          ( quotient-head-is-prime-decomposition-cons-list-ℕ x z l D)
          ( leq-one-quotient-head-is-prime-decomposition-cons-list-ℕ
            x z l D)
          ( l)
          ( is-prime-decomposition-tail-quotient-head-is-prime-decomposition-cons-list-ℕ
            x z l D)
          ( y)
          ( div-right-factor-coprime-ℕ y z
            ( quotient-head-is-prime-decomposition-cons-list-ℕ x z l D)
            ( tr
              ( div-ℕ y)
              ( ( inv
                  ( eq-quotient-head-is-prime-decomposition-cons-list-ℕ
                    x z l D)) ∙
                ( commutative-mul-ℕ _ z))
              ( d))
            ( is-relatively-prime-is-prime-ℕ
              ( y)
              ( z)
              ( p)
              ( is-prime-head-is-prime-decomposition-cons-list-ℕ x z l D)
              ( e)))
          ( p)))
    ( has-decidable-equality-ℕ y z)

is-lower-bound-head-prime-decomposition-list-ℕ :
  (x : ℕ) (H : 1 ≤-ℕ x) (y : ℕ) (l : list ℕ) →
  is-prime-decomposition-list-ℕ x (cons y l) →
  is-lower-bound-ℕ (is-nontrivial-divisor-ℕ x) y
is-lower-bound-head-prime-decomposition-list-ℕ x H y l D m d =
  transitive-leq-ℕ
    ( y)
    ( nat-least-prime-divisor-ℕ m (pr1 d))
    ( m)
    ( leq-div-ℕ
      ( nat-least-prime-divisor-ℕ m (pr1 d))
      ( m)
      ( is-nonzero-le-ℕ 1 m (pr1 d))
      ( div-least-prime-divisor-ℕ m (pr1 d)))
    ( leq-element-in-list-leq-head-is-sorted-list
      ( ℕ-Decidable-Total-Order)
      ( y)
      ( y)
      ( nat-least-prime-divisor-ℕ m (pr1 d))
      ( l)
      ( is-sorted-is-prime-decomposition-list-ℕ x (cons y l) D)
      ( is-in-prime-decomposition-is-prime-divisor-ℕ
        ( x)
        ( H)
        ( cons y l)
        ( D)
        ( nat-least-prime-divisor-ℕ m (pr1 d))
        ( transitive-div-ℕ
          ( nat-least-prime-divisor-ℕ m (pr1 d))
          ( m)
          ( x)
          ( pr2 d)
          ( div-least-nontrivial-divisor-ℕ m (pr1 d)))
        ( is-prime-least-prime-divisor-ℕ m (pr1 d)))
      ( refl-leq-ℕ y))

eq-head-prime-decomposition-list-ℕ :
  (x : ℕ) (H : 1 ≤-ℕ x) (y z : ℕ) (p q : list ℕ) →
  is-prime-decomposition-list-ℕ x (cons y p) →
  is-prime-decomposition-list-ℕ x (cons z q) →
  y ＝ z
eq-head-prime-decomposition-list-ℕ x H y z p q I J =
  ap
    ( pr1)
    ( all-elements-equal-minimal-element-ℕ
      ( is-nontrivial-divisor-ℕ-Prop x)
      ( y ,
        is-nontrivial-divisor-head-is-prime-decomposition-cons-list-ℕ x y p I ,
        is-lower-bound-head-prime-decomposition-list-ℕ x H y p I)
      ( z ,
        is-nontrivial-divisor-head-is-prime-decomposition-cons-list-ℕ x z q J ,
        is-lower-bound-head-prime-decomposition-list-ℕ x H z q J))

eq-prime-decomposition-list-ℕ :
  (x : ℕ) (H : 1 ≤-ℕ x) (p q : list ℕ) →
  is-prime-decomposition-list-ℕ x p →
  is-prime-decomposition-list-ℕ x q →
  p ＝ q
eq-prime-decomposition-list-ℕ x H nil nil _ _ =
  refl
eq-prime-decomposition-list-ℕ x H (cons y l) nil I J =
  ex-falso
    ( contradiction-le-ℕ
      ( 1)
      ( x)
      ( le-one-is-prime-decomposition-cons-list-ℕ x y l I)
      ( leq-eq-ℕ
        ( x)
        ( 1)
        ( inv (eq-is-prime-decomposition-list-ℕ x nil J))))
eq-prime-decomposition-list-ℕ x H nil (cons y l) I J =
  ex-falso
    ( contradiction-le-ℕ
      ( 1)
      ( x)
      ( le-one-is-prime-decomposition-cons-list-ℕ x y l J)
      ( leq-eq-ℕ
        ( x)
        ( 1)
        ( inv (eq-is-prime-decomposition-list-ℕ x nil I))))
eq-prime-decomposition-list-ℕ x H (cons y l) (cons z p) I J =
  eq-Eq-list
    ( cons y l)
    ( cons z p)
    ( ( eq-head-prime-decomposition-list-ℕ x H y z l p I J) ,
      ( Eq-eq-list
        ( l)
        ( p)
        ( eq-prime-decomposition-list-ℕ
          ( quotient-head-is-prime-decomposition-cons-list-ℕ x y l I)
          ( leq-one-quotient-head-is-prime-decomposition-cons-list-ℕ x y l I)
          ( l)
          ( p)
          ( is-prime-decomposition-tail-quotient-head-is-prime-decomposition-cons-list-ℕ
             x y l I)
          ( ( is-sorted-tail-is-prime-decomposition-cons-list-ℕ x z p J) ,
            ( is-prime-tail-is-prime-decomposition-cons-list-ℕ x z p J) ,
            ( le-one-tail-is-prime-decomposition-cons-list-ℕ x z p J) ,
             ( eq-quotient-div-eq-divisor-ℕ z y x
               ( is-nonzero-is-prime-ℕ z
                 ( is-prime-head-is-prime-decomposition-cons-list-ℕ x z p J))
               ( inv (eq-head-prime-decomposition-list-ℕ x H y z l p I J))
               ( div-head-is-prime-decomposition-cons-list-ℕ x z p J)
               ( div-head-is-prime-decomposition-cons-list-ℕ x y l I)) ∙
             ( inv
               ( compute-quotient-head-is-prime-decomposition-cons-list-ℕ
                 x y l I))))))

fundamental-theorem-arithmetic-list-ℕ :
  (x : ℕ) → (H : 1 ≤-ℕ x) → is-contr (prime-decomposition-list-ℕ x)
pr1 (fundamental-theorem-arithmetic-list-ℕ x H) =
  prime-decomposition-fundamental-theorem-arithmetic-ℕ x H
pr2 (fundamental-theorem-arithmetic-list-ℕ x H) d =
  eq-type-subtype
    ( is-prime-decomposition-list-ℕ-Prop x)
    ( eq-prime-decomposition-list-ℕ
      ( x)
      ( H)
      ( list-fundamental-theorem-arithmetic-ℕ x H)
      ( pr1 d)
      ( is-prime-decomposition-list-fundamental-theorem-arithmetic-ℕ x H)
      ( pr2 d))
```

### The sorted list associated with the concatenation of the prime decomposition of `n` and the prime decomposition of `m` is the prime decomposition of `n *ℕ m`

```agda
is-prime-list-concat-list-ℕ :
  (p q : list ℕ) → is-prime-list-ℕ p → is-prime-list-ℕ q →
  is-prime-list-ℕ (concat-list p q)
is-prime-list-concat-list-ℕ nil q Pp Pq = Pq
is-prime-list-concat-list-ℕ (cons x p) q Pp Pq =
  pr1 Pp , is-prime-list-concat-list-ℕ p q (pr2 Pp) Pq

is-prime-is-in-list-ℕ :
  (p : list ℕ) → UU lzero
is-prime-is-in-list-ℕ p = (x : ℕ) → x ∈-list p → is-prime-ℕ x

is-prime-is-in-list-tail-ℕ :
  (p : list ℕ) (x : ℕ) (P : is-prime-is-in-list-ℕ (cons x p)) →
  is-prime-is-in-list-ℕ p
is-prime-is-in-list-tail-ℕ p x P y I = P y (is-in-tail y x p I)

is-prime-is-in-list-is-prime-list-ℕ :
  (p : list ℕ) → is-prime-list-ℕ p → is-prime-is-in-list-ℕ p
is-prime-is-in-list-is-prime-list-ℕ (cons x p) P .x (is-head .x .p) =
  pr1 P
is-prime-is-in-list-is-prime-list-ℕ
  ( cons x p)
  ( P)
  ( y)
  ( is-in-tail .y .x .p I) =
  is-prime-is-in-list-is-prime-list-ℕ p (pr2 P) y I

is-prime-list-is-prime-is-in-list-ℕ :
  (p : list ℕ) → is-prime-is-in-list-ℕ p → is-prime-list-ℕ p
is-prime-list-is-prime-is-in-list-ℕ nil P = raise-star
is-prime-list-is-prime-is-in-list-ℕ (cons x p) P =
  P x (is-head x p) ,
  is-prime-list-is-prime-is-in-list-ℕ
    ( p)
    ( is-prime-is-in-list-tail-ℕ p x P)

is-prime-list-permute-list-ℕ :
  (p : list ℕ) (t : permutation (length-list p)) → is-prime-list-ℕ p →
  is-prime-list-ℕ (permute-list p t)
is-prime-list-permute-list-ℕ p t P =
  is-prime-list-is-prime-is-in-list-ℕ
    ( permute-list p t)
    ( λ x I →
      is-prime-is-in-list-is-prime-list-ℕ p P x
        ( is-in-list-is-in-permute-list p t x I))

is-decomposition-list-permute-list-ℕ :
  (n : ℕ) (p : list ℕ) (t : permutation (length-list p)) →
  is-multiplicative-decomposition-list-ℕ n p →
  is-multiplicative-decomposition-list-ℕ n (permute-list p t)
is-decomposition-list-permute-list-ℕ n p t D =
  {!!} -- inv (permutation-invariant-mul-list-ℕ p t) ∙ D

is-prime-decomposition-list-sort-concatenation-ℕ :
  (x y : ℕ) (H : 1 ≤-ℕ x) (I : 1 ≤-ℕ y) (p q : list ℕ) →
  is-prime-decomposition-list-ℕ x p →
  is-prime-decomposition-list-ℕ y q →
  is-prime-decomposition-list-ℕ
    ( x *ℕ y)
    ( insertion-sort-list
      ( ℕ-Decidable-Total-Order)
      ( concat-list p q))
pr1 (is-prime-decomposition-list-sort-concatenation-ℕ x y H I p q Dp Dq) =
  is-sorting-insertion-sort-list ℕ-Decidable-Total-Order (concat-list p q)
pr1
  ( pr2
    ( is-prime-decomposition-list-sort-concatenation-ℕ x y H I p q Dp Dq)) =
  tr
    ( λ p → is-prime-list-ℕ p)
    ( inv
      ( eq-permute-list-permutation-insertion-sort-list
        ( ℕ-Decidable-Total-Order)
        ( concat-list p q)))
    ( is-prime-list-permute-list-ℕ
      ( concat-list p q)
      ( permutation-insertion-sort-list
        ( ℕ-Decidable-Total-Order)
        ( concat-list p q))
      ( is-prime-list-concat-list-ℕ
        ( p)
        ( q)
        ( is-prime-list-is-prime-decomposition-list-ℕ x p Dp)
        ( is-prime-list-is-prime-decomposition-list-ℕ y q Dq)))
pr2
  ( pr2
    ( is-prime-decomposition-list-sort-concatenation-ℕ x y H I p q Dp Dq)) =
  tr
    ( λ p → is-multiplicative-decomposition-list-ℕ (x *ℕ y) p)
    ( inv
      ( eq-permute-list-permutation-insertion-sort-list
        ( ℕ-Decidable-Total-Order)
        ( concat-list p q)))
    ( is-decomposition-list-permute-list-ℕ
      ( x *ℕ y)
      ( concat-list p q)
      ( permutation-insertion-sort-list
        ( ℕ-Decidable-Total-Order)
        ( concat-list p q))
      ( is-multiplicative-decomposition-concat-list-ℕ
        ( x)
        ( y)
        ( p)
        ( q)
        ( is-multiplicative-decomposition-is-prime-decomposition-list-ℕ x p Dp)
        ( is-multiplicative-decomposition-is-prime-decomposition-list-ℕ
          y q Dq)))

prime-decomposition-list-sort-concatenation-ℕ :
  (x y : ℕ) (H : 1 ≤-ℕ x) (I : 1 ≤-ℕ y) (p q : list ℕ) →
  is-prime-decomposition-list-ℕ x p →
  is-prime-decomposition-list-ℕ y q →
  prime-decomposition-list-ℕ (x *ℕ y)
pr1 (prime-decomposition-list-sort-concatenation-ℕ x y H I p q Dp Dq) =
  insertion-sort-list ℕ-Decidable-Total-Order (concat-list p q)
pr2 (prime-decomposition-list-sort-concatenation-ℕ x y H I p q Dp Dq) =
  is-prime-decomposition-list-sort-concatenation-ℕ x y H I p q Dp Dq
```

## External links

- [Fundamental theorem of arithmetic](https://en.wikipedia.org/wiki/Fundamental_theorem_of_arithmetic)
  at Wikipedia

## References

{{#bibliography}}
