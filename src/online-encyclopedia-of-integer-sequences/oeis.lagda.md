# Sequences of the online encyclopedia of integer sequences

```agda
module online-encyclopedia-of-integer-sequences.oeis where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.eulers-totient-function
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.factorials
open import elementary-number-theory.fibonacci-sequence
open import elementary-number-theory.infinitude-of-primes
open import elementary-number-theory.natural-numbers

open import finite-group-theory.finite-groups

open import foundation.functions
```

</details>

## Sequences

### [A000001](https://oeis.org/A000001) The number of groups of order `n`

```agda
A000001 : ℕ → ℕ
A000001 = number-of-groups-of-order
```

### [A000010](https://oeis.org/A000010) Euler's totient function

```agda
A000010 : ℕ → ℕ
A000010 = eulers-totient-function
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

### [A000079](https://oeis.org/A000079) Powers of `2

```agda
A000079 : ℕ → ℕ
A000079 = exp-ℕ 2
```

### [A000142](https://oeis.org/A000142) Factorials

```agda
A000142 : ℕ → ℕ
A000142 = factorial-ℕ
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

### [A001477](https://oeis.org/A001477) The natural numbers

```agda
A001477 : ℕ → ℕ
A001477 = id
```
