# Sequences of the online encyclopedia of integer sequences

```agda
module online-encyclopedia-of-integer-sequences.oeis where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.ackermann-function
open import elementary-number-theory.catalan-numbers
open import elementary-number-theory.cofibonacci
open import elementary-number-theory.collatz-bijection
open import elementary-number-theory.euclid-mullin-sequence
open import elementary-number-theory.eulers-totient-function
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.factorials
open import elementary-number-theory.fermat-numbers
open import elementary-number-theory.fibonacci-sequence
open import elementary-number-theory.infinitude-of-primes
open import elementary-number-theory.kolakoski-sequence
open import elementary-number-theory.multiset-coefficients
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.pisano-periods

open import finite-group-theory.finite-groups

open import foundation.function-types

open import univalent-combinatorics.main-classes-of-latin-squares
```

</details>

## Sequences

### [A000001](https://oeis.org/A000001) The number of groups of order `n`

```agda
A000001 : ℕ → ℕ
A000001 = number-of-groups-of-order
```

### [A000002](https://oeis.org/A000002) The Kolakoski sequence

```agda
A000002 : ℕ → ℕ
A000002 = kolakoski
```

### [A000004](https://oeis.org/A000004) The zero sequence

```agda
A000004 : ℕ → ℕ
A000004 _ = zero-ℕ
```

### [A000007](https://oeis.org/A000007) The characteristic function for 0

```agda
A000007 : ℕ → ℕ
A000007 zero-ℕ = 1
A000007 (succ-ℕ _) = 0
```

### [A000010](https://oeis.org/A000010) Euler's totient function

```agda
A000010 : ℕ → ℕ
A000010 = eulers-totient-function-relatively-prime
```

### [A000012](https://oeis.org/A000012) All 1's sequence

```agda
A000012 : ℕ → ℕ
A000012 _ = 1
```

### [A000027](https://oeis.org/A000027) The positive integers

```agda
A000027 : ℕ → ℕ
A000027 = succ-ℕ
```

### [A000040](https://oeis.org/A000040) The prime numbers

```agda
A000040 : ℕ → ℕ
A000040 = prime-ℕ
```

### [A000045](https://oeis.org/A000045) The Fibonacci sequence

```agda
A000045 : ℕ → ℕ
A000045 = Fibonacci-ℕ
```

### [A000079](https://oeis.org/A000079) Powers of `2`

```agda
A000079 : ℕ → ℕ
A000079 = exp-ℕ 2
```

### [A000108](https://oeis.org/A000108) The Catalan numbers

```agda
A000108 : ℕ → ℕ
A000108 = catalan-numbers
```

### [A000142](https://oeis.org/A000142) Factorials

```agda
A000142 : ℕ → ℕ
A000142 = factorial-ℕ
```

### [A000215](https://oeis.org/A000215) The Fermat numbers

```agda
A000215 : ℕ → ℕ
A000215 = fermat-number-ℕ
```

### [A000244](https://oeis.org/A000244) Powers of `3`

```agda
A000244 : ℕ → ℕ
A000244 = exp-ℕ 3
```

### [A000720](https://oeis.org/A000720) The prime counting function

```agda
A000720 : ℕ → ℕ
A000720 = prime-counting-ℕ
```

### [A000945](https://oeis.org/A000945) The Euclid–Mullin sequence

```agda
A000945 : ℕ → ℕ
A000945 = euclid-mullin-ℕ
```

### [A001175](https://oeis.org/A001175) Pisano periods

```agda
A001175 : ℕ → ℕ
A001175 = pisano-period
```

### [A001177](https://oeis.org/A001177) The cofibonacci sequence

```agda
A001177 : ℕ → ℕ
A001177 = cofibonacci
```

### [A001477](https://oeis.org/A001477) The natural numbers

```agda
A001477 : ℕ → ℕ
A001477 = id
```

### [A003090](https://oeis.org/A003090) The number of main classes of Latin squares of order `n`

```agda
A003090 : ℕ → ℕ
A003090 = number-of-main-classes-of-Latin-squares-of-order
```

### [A006369](https://oeis.org/A006369) Collatz' bijection

```agda
A006369 : ℕ → ℕ
A006369 = map-collatz-bijection
```

### [A046859](https://oeis.org/A046859) The main diagonal of the Ackermann–Péter function

```agda
A046859 : ℕ → ℕ
A046859 n = ackermann n n
```
