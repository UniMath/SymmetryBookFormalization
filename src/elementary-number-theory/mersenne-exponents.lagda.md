# Mersenne exponents

```agda
module elementary-number-theory.mersenne-exponents where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.mersenne-primes
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers

open import foundation.cartesian-product-types
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "Mersenne exponent" Agda=mersenne-exponent-ℕ OEIS=A000043}} is a
[prime number](elementary-number-theory.prime-numbers.md) $p$ such that the
[Mersenne number](elementary-number-theory.mersenne-numbers.md) $M_p$ is a
[Mersenne prime](elementary-number-theory.mersenne-primes.md).

## Definitions

### The predicate of being a Mersenne exponent

```agda
is-mersenne-exponent-ℕ : ℕ → UU lzero
is-mersenne-exponent-ℕ n =
  is-prime-ℕ n × is-prime-mersenne-number-ℕ n
```
