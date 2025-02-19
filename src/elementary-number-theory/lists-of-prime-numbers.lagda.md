# Lists of prime numbers

```agda
module elementary-number-theory.lists-of-prime-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import lists.functoriality-lists
open import lists.lists
open import lists.universal-quantification-lists
```

</details>

## Idea

A {{#concept "list of prime numbers"}} is a [list](lists.lists.md) of
[natural numbers](elementary-number-theory.natural-numbers.md) such that each
number in the list is [prime](elementary-number-theory.prime-numbers.md).

## Definitions

### The predicate on lists of natural numbers of being a list of prime numbers

```agda
is-prime-list-ℕ :
  list ℕ → UU lzero
is-prime-list-ℕ l = for-all-list l is-prime-ℕ

is-prop-is-prime-list-ℕ :
  (l : list ℕ) → is-prop (is-prime-list-ℕ l)
is-prop-is-prime-list-ℕ l = is-prop-for-all-list l is-prime-ℕ-Prop
```

## Properties

### Any list of prime numbers is a prime list

```agda
is-prime-list-list-Prime-ℕ :
  (l : list Prime-ℕ) → is-prime-list-ℕ (map-list nat-Prime-ℕ l)
is-prime-list-list-Prime-ℕ nil = raise-star
is-prime-list-list-Prime-ℕ (cons x l) =
  ( is-prime-Prime-ℕ x , is-prime-list-list-Prime-ℕ l)
```
