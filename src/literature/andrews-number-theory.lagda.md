# Andrews, G. E., Number Theory

This file collects references to formalization of constructions and theorems
from {{#cite Andrews94}}.

```agda
module literature.andrews-number-theory where
```

## Part 1 Multiplicativity–Divisibility

### Chapter 1 Basis Representation

#### Section 1–1 Basis Representation

Theorem 1–1 establishes the identity for [triangular numbers](elementary-number-theory.triangular-numbers.md)

```agda
open import elementary-number-theory.triangular-numbers using
  ( compute-triangular-number-ℕ)
```

Theorem 1–2 is the formula for the geometric series stated for real numbers. This would be best formalized as an identity of polynomials. However, we don't have polynomials yet.

Corollary 1–1 states that the [exponential function](elementary-number-theory.exponentiation-natural-numbers.md) is [strictly inflationary](elementary-number-theory.strictly-inflationary-functions-natural-numbers.md).

```agda
open import elementary-number-theory.exponentiation-natural-numbers using
  ( is-strictly-inflationary-exp-ℕ)
```

Exercise 1–1 asks to compute the $n$th [square pyramidal number](elementary-number-theory.square-pyramidal-numbers.md)

```agda
open import elementary-number-theory.square-pyramidal-numbers using
  ( compute-square-pyramidal-number-ℕ)
```

Exercise 1–2 asks to prove [Nicomachus's theorem](elementary-number-theory.nicomachuss-theorem.md)

```agda
open import elementary-number-theory.nicomachuss-theorem using
  ( nicomachuss-theorem-ℕ)
```

Exercise 1–3 is a polynomial identity, which we have to skip for now.

Exercise 1–4 computes the sum of the first $n$ [pronic numbers](elementary-number-theory.pronic-numbers.md)

```agda
open import elementary-number-theory.pronic-numbers using
  ( compute-sum-of-pronic-numbers-ℕ)
```

Exercise 1–5 computes the sum of the first $n$ [odd numbers](elementary-number-theory.parity-natural-numbers.md)

```agda
open import elementary-number-theory.squares-natural-numbers using
  ( compute-sum-of-odd-numbers-ℕ)
```

Exercise 1–6 asks to compute the sum of the first $n$ multiplicative inverses of the pronic numbers. The infrastructure exists in the library, but we haven't done so yet.

Exercise 1–7 computes the sum of the first $n$ Fibonacci numbers

```agda
open import elementary-number-theory.fibonacci-sequence using
  ( compute-sum-of-fibonacci-ℕ)
```

Exercise 1–8 computes the sum of the first $n$ oddly indexed Fibonacci numbers

```agda
open import elementary-number-theory.fibonacci-sequence using
  ( compute-strictly-bounded-sum-fibonacci-odd-number-ℕ)
```

Exercise 1–9 computes the sum of the first $n$ evenly indexed Fibonacci numbers

```agda
open import elementary-number-theory.fibonacci-sequence using
  ( compute-bounded-sum-fibonacci-even-ℕ)
```

Exercise 1–10 asks to prove
[Cassini's identity](https://en.wikipedia.org/wiki/Cassini_and_Catalan_identities), named after the Italian mathematican and astronomer Giovanni Domenico Cassini, who proved the result in 1680. Note that this identity has two further generalizations, one due to Eugène Catalan and one due to Steven Vajda.

```agda

```
