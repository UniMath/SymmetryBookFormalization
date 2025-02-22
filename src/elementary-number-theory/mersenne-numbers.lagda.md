# Mersenne numbers

```agda
module elementary-number-theory.mersenne-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.infinitude-of-primes
open import elementary-number-theory.natural-numbers

open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.universe-levels
```

</details>

## Idea

The $n$th {{#concept "Mersenne number" Agda=mersenne-number-ℕ OEIS=A000225}}
$M_n$ is defined to be

$$
  M_n := 2^n-1.
$$

[Mersenne primes](elementary-number-theory.mersenne-primes.md) are Mersenne
numbers that are [prime](elementary-number-theory.prime-numbers.md).

## Definitions

### The Mersenne numbers

```agda
mersenne-number-ℕ :
  ℕ → ℕ
mersenne-number-ℕ n =
  pred-is-nonzero-ℕ (exp-ℕ 2 n) (is-nonzero-exp-ℕ 2 n is-nonzero-two-ℕ)
```

### The Mersenne numbers of prime powers

Some sources only refer to numbers of the form $2^p-1$ with $p$ prime as
Mersenne numbers. The sequence $n ↦ 2^{p(n)}-1$, where $p(n)$ is the $n$th prime
number, is listed as A001348 in the [OEIS](literature.oeis.md) {{#cite OEIS}}.
The first few numbers in this sequence are

```text
  3, 7, 31, 127, 2047, ...
```

```agda
mersenne-number-prime-ℕ :
  ℕ → ℕ
mersenne-number-prime-ℕ =
  mersenne-number-ℕ ∘ prime-ℕ
```

### The predicate of being a Mersenne number

```agda
is-mersenne-number-ℕ :
  ℕ → UU lzero
is-mersenne-number-ℕ =
  fiber mersenne-number-ℕ
```

## See also

- [Mersenne exponents](elementary-number-theory.mersenne-exponents.md)
- [Mersenne primes](elementary-number-theory.mersenne-primes.md)
