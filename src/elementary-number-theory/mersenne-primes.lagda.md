# Mersenne primes

```agda
module elementary-number-theory.mersenne-primes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.mersenne-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "Mersenne prime" Agda=is-mersenne-prime-ℕ WDID=Q186875 WD="Mersenne prime"}}
is a [prime number](elementary-number-theory.prime-numbers.md) that is one less
than a
[power of two](elementary-number-theory.exponentiation-natural-numbers.md).

## Definitions

### The predicate of being a Mersenne prime

```agda
is-mersenne-prime-ℕ :
  ℕ → UU lzero
is-mersenne-prime-ℕ n =
  is-prime-ℕ n × is-mersenne-number-ℕ n
```

### The predicate on Mersenne numbers of being prime

```agda
is-prime-mersenne-number-ℕ :
  ℕ → UU lzero
is-prime-mersenne-number-ℕ k =
  is-prime-ℕ (mersenne-number-ℕ k)
```
