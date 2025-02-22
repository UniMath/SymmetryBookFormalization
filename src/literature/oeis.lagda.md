# Sequences of the online encyclopedia of integer sequences

This file records formalized sequences of the
[Online Encyclopedia of Integer Sequences](https://oeis.org) {{#cite oeis}}.

```agda
module literature.oeis where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.function-types
```

</details>

## Sequences

### A000001 – The number of groups of order `n`

```agda
open import finite-group-theory.finite-groups using
  ( number-of-groups-of-order)
```

OEIS: [A000001](https://oeis.org/A000001)

### A000002 – The Kolakoski sequence

```agda
open import elementary-number-theory.kolakoski-sequence using
  ( kolakoski)
```

OEIS: [A000002](https://oeis.org/A000002)

### A000004 – The zero sequence

```agda
A000004 : ℕ → ℕ
A000004 _ = zero-ℕ
```

OEIS: [A000004](https://oeis.org/A000004)

### A000005 – The number of divisors

```agda
open import elementary-number-theory.number-of-divisors using
  ( number-of-divisors-ℕ)
```

OEIS: [A000005](https://oeis.org/A000005)

### A000007 – The characteristic function for 0

```agda
A000007 : ℕ → ℕ
A000007 zero-ℕ = 1
A000007 (succ-ℕ _) = 0
```

OEIS: [A000007](https://oeis.org/A000007)

### A000010 – Euler's totient function

```agda
open import elementary-number-theory.eulers-totient-function using
  ( eulers-totient-function-relatively-prime)
```

OEIS: [A000010](https://oeis.org/A000010)

### A000012 – All 1's sequence

```agda
A000012 : ℕ → ℕ
A000012 _ = 1
```

OEIS: [A000012](https://oeis.org/A000012)

### A000027 – The positive integers

```agda
A000027 : ℕ → ℕ
A000027 = succ-ℕ
```

OEIS: [A000027](https://oeis.org/A000027)

### A000040 – The prime numbers

```agda
open import elementary-number-theory.infinitude-of-primes using
  ( prime-ℕ)
```

OEIS: [A000040](https://oeis.org/A000040)

### A000043 – The Mersenne exponents

```agda
open import elementary-number-theory.mersenne-exponents using
  ( is-mersenne-exponent-ℕ)
```

OEIS: [A000043](https://oeis.org/A000043)

### A000045 – The Fibonacci sequence

```agda
open import elementary-number-theory.fibonacci-sequence using
  ( fibonacci-ℕ)
```

OEIS: [A000045](https://oeis.org/A000045)

### A000058 – Sylvester's sequence

```agda
open import elementary-number-theory.sylvesters-sequence using
  ( sylvesters-sequence-ℕ)
```

OEIS: [A000058](https://oeis.org/A000058)

### A000079 – Powers of `2`

```agda
A000079 : ℕ → ℕ
A000079 = exp-ℕ 2
```

OEIS: [A000079](https://oeis.org/A000079)

### A000108 – The Catalan numbers

```agda
open import elementary-number-theory.catalan-numbers using
  ( catalan-numbers)
```

OEIS: [A000108](https://oeis.org/A000108)

### A000110 – The Bell numbers

```agda
open import elementary-number-theory.bell-numbers using
  ( bell-number-ℕ)
```

OEIS: [A000110](https://oeis.org/A000110)

### A000142 – Factorials

```agda
open import elementary-number-theory.factorials using
  ( factorial-ℕ)
```

OEIS: [A000142](https://oeis.org/A000142)

### A000215 – The Fermat numbers

```agda
open import elementary-number-theory.fermat-numbers using
  ( fermat-number-ℕ)
```

OEIS: [A000215](https://oeis.org/A000215)

### A000217 – The triangular numbers

```agda
open import elementary-number-theory.triangular-numbers using
  ( triangular-number-ℕ)
```

OEIS: [A000217](https://oeis.org/A000217)

### A000225 – Mersenne numbers

```agda
open import elementary-number-theory.mersenne-numbers using
  ( mersenne-number-ℕ)
```

OEIS: [A000225](https://oeis.org/A000225)

### A000244 – Powers of `3`

```agda
A000244 : ℕ → ℕ
A000244 = exp-ℕ 3
```

OEIS: [A000244](https://oeis.org/A000244)

### A000330 – The square pyramidal numbers

```agda
open import elementary-number-theory.square-pyramidal-numbers using
  ( square-pyramidal-number-ℕ)
```

OEIS: [A000330](https://oeis.org/A000330)

### A000720 – The prime counting function

```agda
open import elementary-number-theory.infinitude-of-primes using
  ( prime-counting-ℕ)
```

OEIS: [A000720](https://oeis.org/A000720)

### A000945 – The Euclid–Mullin sequence

```agda
open import elementary-number-theory.euclid-mullin-sequence using
  ( euclid-mullin-ℕ)
```

OEIS: [A000945](https://oeis.org/A000945)

### A001175 – Pisano periods

```agda
open import elementary-number-theory.pisano-periods using
  ( pisano-period)
```

OEIS: [A001175](https://oeis.org/A001175)

### A001177 – The cofibonacci sequence

```agda
open import elementary-number-theory.cofibonacci using
  ( cofibonacci)
```

OEIS: [A001177](https://oeis.org/A001177)

### A001348 – The Mersenne numbers (at primes)

```agda
open import elementary-number-theory.mersenne-numbers using
  ( mersenne-number-prime-ℕ)
```

OEIS: [A001348](https://oeis.org/A001348)

### A001477 – The natural numbers

```agda
A001477 : ℕ → ℕ
A001477 = id
```

OEIS: [A001477](https://oeis.org/A001477)

### A002378 – The pronic numbers

```agda
open import elementary-number-theory.pronic-numbers using
  ( pronic-number-ℕ)
```

OEIS: [A002378](https://oeis.org/A002378)

### A003090 – The number of main classes of Latin squares of order `n`

```agda
open import univalent-combinatorics.main-classes-of-latin-squares using
  ( number-of-main-classes-of-Latin-squares-of-order)
```

OEIS: [A003090](https://oeis.org/A003090)

### A005408 – The odd numbers

```agda
open import elementary-number-theory.parity-natural-numbers using
  ( odd-number-ℕ)
```

OEIS: [A005408](https://oeis.org/A005408)

### A005843 – The nonnegative natural numbers

```agda
open import elementary-number-theory.parity-natural-numbers using
  ( even-number-ℕ)
```

OEIS: [A005843](https://oeis.org/A005843)

### A006369 – Collatz' bijection

```agda
open import elementary-number-theory.collatz-bijection using
  ( map-collatz-bijection)
```

OEIS: [A006369](https://oeis.org/A006369)

### A007018 – The iterated pronic numbers

```agda
open import elementary-number-theory.pronic-numbers using
  ( iterated-pronic-number-ℕ)
```

OEIS: [A007018](https://oeis.org/A007018)

### A027851 – The number of semigroups of order `n` up to isomorphism

```agda
open import finite-group-theory.finite-semigroups using
  ( number-of-semigroups-of-order)
```

OEIS: [A027851](https://oeis.org/A027851)

### A046859 – The main diagonal of the Ackermann–Péter function

```agda
open import elementary-number-theory.ackermann-function using
  ( simplified-ackermann-ℕ)
```

OEIS: [A046859](https://oeis.org/A046859)

### A058129 – The number of monoids of order `n` up to isomorphism

```agda
open import finite-group-theory.finite-monoids using
  ( number-of-monoids-of-order)
```

OEIS: [A058129](https://oeis.org/A058129)

## References

{{#bibliography}}
