# Nontrivial divisors of natural numbers

```agda
module elementary-number-theory.nontrivial-divisors-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.minimal-structured-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels

open import lists.lists
open import lists.universal-quantification-lists
```

</details>

## Idea

A {{#concept "nontrivial divisor"}} of a
[natural number](elementary-number-theory.natural-numbers.md) is a
[divisor](elementary-number-theory.divisibility-natural-numbers.md)
[strictly greater](elementary-number-theory.strict-inequality-natural-numbers.md)
than `1`.

Every number strictly greater than `1` has a least nontrivial divisor, which is
a [prime number](elementary-number-theory.prime-numbers.md). This fact is
essential in the
[Fundamental Theorem of Arithmetic](elementary-number-theory.fundamental-theorem-of-arithmetic.md).

## Definitions

### Nontrivial divisors

Nontrivial divisors of a natural number are divisors strictly greater than `1`.

```agda
module _
  (n x : ℕ)
  where

  is-nontrivial-divisor-ℕ : UU lzero
  is-nontrivial-divisor-ℕ = (1 <-ℕ x) × (div-ℕ x n)

  is-prop-is-nontrivial-divisor-ℕ : is-prop is-nontrivial-divisor-ℕ
  is-prop-is-nontrivial-divisor-ℕ =
    is-prop-Σ
      ( is-prop-le-ℕ 1 x)
      ( λ p → is-prop-div-ℕ x n (inl (is-nonzero-le-ℕ 1 x p)))

  is-nontrivial-divisor-ℕ-Prop : Prop lzero
  pr1 is-nontrivial-divisor-ℕ-Prop = is-nontrivial-divisor-ℕ
  pr2 is-nontrivial-divisor-ℕ-Prop = is-prop-is-nontrivial-divisor-ℕ

  le-one-is-nontrivial-divisor-ℕ :
    is-nontrivial-divisor-ℕ → 1 <-ℕ x
  le-one-is-nontrivial-divisor-ℕ = pr1

  div-is-nontrivial-divisor-ℕ :
    is-nontrivial-divisor-ℕ → div-ℕ x n
  div-is-nontrivial-divisor-ℕ = pr2
```

### Lists of nontrivial divisors of a number

```agda
is-list-of-nontrivial-divisors-ℕ :
  ℕ → list ℕ → UU lzero
is-list-of-nontrivial-divisors-ℕ n l =
  for-all-list l (is-nontrivial-divisor-ℕ n)
```

## Properties

### Being a nontrivial divisor is decidable

```agda
is-decidable-is-nontrivial-divisor-ℕ :
  (n x : ℕ) → is-decidable (is-nontrivial-divisor-ℕ n x)
is-decidable-is-nontrivial-divisor-ℕ n x =
  is-decidable-product (is-decidable-le-ℕ 1 x) (is-decidable-div-ℕ x n)
```

### Any number strictly greater than `1` is a nontrivial divisor of itself

```agda
is-nontrivial-divisor-diagonal-ℕ :
  (n : ℕ) → le-ℕ 1 n → is-nontrivial-divisor-ℕ n n
pr1 (is-nontrivial-divisor-diagonal-ℕ n H) = H
pr2 (is-nontrivial-divisor-diagonal-ℕ n H) = refl-div-ℕ n
```

### Any nontrivial divisor of a number `x` that divides a number `y` is a nontrivial divisor of `y`

```agda
is-nontrivial-divisor-div-ℕ :
  (m n k : ℕ) → div-ℕ n k →
  is-nontrivial-divisor-ℕ n m → is-nontrivial-divisor-ℕ k m
pr1 (is-nontrivial-divisor-div-ℕ m n k H K) =
  le-one-is-nontrivial-divisor-ℕ n m K
pr2 (is-nontrivial-divisor-div-ℕ m n k H K) =
  transitive-div-ℕ m n k H (div-is-nontrivial-divisor-ℕ n m K)
```

### Any list of nontrivial divisors of a number `x` that divides a number `y` is a list of nontrivial divisors of `y`

```agda
is-list-of-nontrivial-divisors-div-ℕ :
  (x y : ℕ) → div-ℕ x y → (l : list ℕ) →
  is-list-of-nontrivial-divisors-ℕ x l → is-list-of-nontrivial-divisors-ℕ y l
is-list-of-nontrivial-divisors-div-ℕ x y d nil H = raise-star
pr1 (is-list-of-nontrivial-divisors-div-ℕ x y d (cons z l) (H , K)) =
  is-nontrivial-divisor-div-ℕ z x y d H
pr2 (is-list-of-nontrivial-divisors-div-ℕ x y d (cons z l) (H , K)) =
  is-list-of-nontrivial-divisors-div-ℕ x y d l K
```

### Every natural number strictly greater than `1` has a least nontrivial divisor

```agda
least-nontrivial-divisor-ℕ :
  (n : ℕ) → le-ℕ 1 n → minimal-element-ℕ (is-nontrivial-divisor-ℕ n)
least-nontrivial-divisor-ℕ n H =
  well-ordering-principle-ℕ
    ( is-nontrivial-divisor-ℕ n)
    ( is-decidable-is-nontrivial-divisor-ℕ n)
    ( is-nontrivial-divisor-diagonal-ℕ n H)

nat-least-nontrivial-divisor-ℕ : (n : ℕ) → le-ℕ 1 n → ℕ
nat-least-nontrivial-divisor-ℕ n H = pr1 (least-nontrivial-divisor-ℕ n H)

nat-least-nontrivial-divisor-ℕ' : ℕ → ℕ
nat-least-nontrivial-divisor-ℕ' zero-ℕ = 0
nat-least-nontrivial-divisor-ℕ' (succ-ℕ zero-ℕ) = 1
nat-least-nontrivial-divisor-ℕ' (succ-ℕ (succ-ℕ n)) =
  nat-least-nontrivial-divisor-ℕ (succ-ℕ (succ-ℕ n)) star

le-one-least-nontrivial-divisor-ℕ :
  (n : ℕ) (H : le-ℕ 1 n) → le-ℕ 1 (nat-least-nontrivial-divisor-ℕ n H)
le-one-least-nontrivial-divisor-ℕ n H =
  pr1 (pr1 (pr2 (least-nontrivial-divisor-ℕ n H)))

div-least-nontrivial-divisor-ℕ :
  (n : ℕ) (H : le-ℕ 1 n) → div-ℕ (nat-least-nontrivial-divisor-ℕ n H) n
div-least-nontrivial-divisor-ℕ n H =
  pr2 (pr1 (pr2 (least-nontrivial-divisor-ℕ n H)))

is-minimal-least-nontrivial-divisor-ℕ :
  (n : ℕ) (H : le-ℕ 1 n) (x : ℕ) (K : 1 <-ℕ x) (d : div-ℕ x n) →
  leq-ℕ (nat-least-nontrivial-divisor-ℕ n H) x
is-minimal-least-nontrivial-divisor-ℕ n H x K d =
  pr2 (pr2 (least-nontrivial-divisor-ℕ n H)) x (K , d)
```

### The least nontrivial divisor of a number `> 1` is nonzero

```agda
abstract
  is-nonzero-least-nontrivial-divisor-ℕ :
    (n : ℕ) (H : le-ℕ 1 n) → is-nonzero-ℕ (nat-least-nontrivial-divisor-ℕ n H)
  is-nonzero-least-nontrivial-divisor-ℕ n H =
    is-nonzero-div-ℕ
      ( nat-least-nontrivial-divisor-ℕ n H)
      ( n)
      ( div-least-nontrivial-divisor-ℕ n H)
      ( λ where refl → H)
```

### The least nontrivial divisor of a number `> 1` is prime

```agda
is-prime-least-nontrivial-divisor-ℕ :
  (n : ℕ) (H : le-ℕ 1 n) → is-prime-ℕ (nat-least-nontrivial-divisor-ℕ n H)
pr1 (is-prime-least-nontrivial-divisor-ℕ n H x) (K , L) =
  map-right-unit-law-coproduct-is-empty
    ( is-one-ℕ x)
    ( 1 <-ℕ x)
    ( λ p →
      contradiction-le-ℕ x
        ( nat-least-nontrivial-divisor-ℕ n H)
        ( le-div-ℕ x
          ( nat-least-nontrivial-divisor-ℕ n H)
          ( is-nonzero-least-nontrivial-divisor-ℕ n H)
          ( L)
          ( K))
        ( is-minimal-least-nontrivial-divisor-ℕ n H x p
          ( transitive-div-ℕ x
            ( nat-least-nontrivial-divisor-ℕ n H)
            ( n)
            ( div-least-nontrivial-divisor-ℕ n H)
            ( L))))
    ( eq-or-le-leq-ℕ' 1 x
      ( leq-one-div-ℕ x n
        ( transitive-div-ℕ x
          ( nat-least-nontrivial-divisor-ℕ n H)
          ( n)
          ( div-least-nontrivial-divisor-ℕ n H)
          ( L))
        ( leq-le-ℕ 1 n H)))
pr1 (pr2 (is-prime-least-nontrivial-divisor-ℕ n H .1) refl) =
  neq-le-ℕ 1
    ( nat-least-nontrivial-divisor-ℕ n H)
    ( le-one-least-nontrivial-divisor-ℕ n H)
pr2 (pr2 (is-prime-least-nontrivial-divisor-ℕ n H .1) refl) =
  div-one-ℕ _
```

### The least prime divisor of a number `1 < n`

```agda
nat-least-prime-divisor-ℕ : (x : ℕ) → 1 <-ℕ x → ℕ
nat-least-prime-divisor-ℕ x H = nat-least-nontrivial-divisor-ℕ x H

is-prime-least-prime-divisor-ℕ :
  (x : ℕ) (H : 1 <-ℕ x) → is-prime-ℕ (nat-least-prime-divisor-ℕ x H)
is-prime-least-prime-divisor-ℕ x H = is-prime-least-nontrivial-divisor-ℕ x H

prime-least-prime-divisor-ℕ : (x : ℕ) → 1 <-ℕ x → Prime-ℕ
pr1 (prime-least-prime-divisor-ℕ x H) = nat-least-prime-divisor-ℕ x H
pr2 (prime-least-prime-divisor-ℕ x H) = is-prime-least-prime-divisor-ℕ x H

div-least-prime-divisor-ℕ :
  (x : ℕ) (H : 1 <-ℕ x) → div-ℕ (nat-least-prime-divisor-ℕ x H) x
div-least-prime-divisor-ℕ x H = div-least-nontrivial-divisor-ℕ x H

quotient-div-least-prime-divisor-ℕ :
  (x : ℕ) (H : 1 <-ℕ x) → ℕ
quotient-div-least-prime-divisor-ℕ x H =
  quotient-div-ℕ
    ( nat-least-prime-divisor-ℕ x H)
    ( x)
    ( div-least-prime-divisor-ℕ x H)

div-quotient-div-least-prime-divisor-ℕ :
  (x : ℕ) (H : 1 <-ℕ x) → div-ℕ (quotient-div-least-prime-divisor-ℕ x H) x
div-quotient-div-least-prime-divisor-ℕ x H =
  div-quotient-div-ℕ
    ( nat-least-prime-divisor-ℕ x H)
    ( x)
    ( div-least-prime-divisor-ℕ x H)

leq-one-quotient-div-least-prime-divisor-ℕ :
  (x : ℕ) (H : 1 <-ℕ x) → 1 ≤-ℕ quotient-div-least-prime-divisor-ℕ x H
leq-one-quotient-div-least-prime-divisor-ℕ x H =
  leq-one-quotient-div-ℕ
    ( nat-least-prime-divisor-ℕ x H)
    ( x)
    ( div-least-prime-divisor-ℕ x H)
    ( leq-le-ℕ 1 x H)

upper-bound-quotient-div-least-prime-divisor-ℕ :
  (x : ℕ) (H : 1 <-ℕ succ-ℕ x) →
  quotient-div-least-prime-divisor-ℕ (succ-ℕ x) H ≤-ℕ x
upper-bound-quotient-div-least-prime-divisor-ℕ x H =
  upper-bound-quotient-div-is-prime-ℕ
    ( nat-least-prime-divisor-ℕ (succ-ℕ x) H)
    ( x)
    ( is-prime-least-prime-divisor-ℕ (succ-ℕ x) H)
    ( div-least-prime-divisor-ℕ (succ-ℕ x) H)
```
