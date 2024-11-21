# Freek Wiedijk's 100 Theorems

This file records formalized results from
[Freek Wiedijk's](http://www.cs.ru.nl/F.Wiedijk/)
[_Formalizing 100 Theorems_](https://www.cs.ru.nl/~freek/100/).
{{#cite 100theorems}}

```agda
module literature.100-theorems where
```

## The list

### [3. The Denumerability of the Rational Numbers](https://www.cs.ru.nl/~freek/100/#3) {#3}

**Author:** [Fredrik Bakke](https://www.ntnu.edu/employees/fredrik.bakke)

```agda
open import elementary-number-theory.rational-numbers using
  ( is-countable-ℚ)
```

### [11. The Infinitude of Primes](https://www.cs.ru.nl/~freek/100/#11) {#11}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

```agda
open import elementary-number-theory.infinitude-of-primes using
  ( infinitude-of-primes-ℕ)
```

### [22. The Non-Denumerability of the Continuum](https://www.cs.ru.nl/~freek/100/#22) {#22}

> This is not yet formalized.

### [25. Schröder–Bernstein Theorem](https://www.cs.ru.nl/~freek/100/#25) {#25}

**Author:** [Elif Uskuplu](https://elifuskuplu.github.io)

Note: The formalization of the Cantor-Schröder-Bernstein theorem in agda-unimath
is a generalization of the statement to all types, i.e., it is not restricted to
sets. This generalization is originally due to Martin-Escardó, hence we refer to
the generalization as the Cantor-Schröder-Bernstein-Escardó theorem.

```agda
open import foundation.cantor-schroder-bernstein-escardo using
  ( Cantor-Schröder-Bernstein-Escardó)
open import foundation.cantor-schroder-bernstein-escardo using
  ( Cantor-Schröder-Bernstein)
```

### [44. The Binomial Theorem](https://www.cs.ru.nl/~freek/100/#44) {#44}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

```agda
open import commutative-algebra.binomial-theorem-commutative-rings using
  ( binomial-theorem-Commutative-Ring)
open import commutative-algebra.binomial-theorem-commutative-semirings using
  ( binomial-theorem-Commutative-Semiring)
open import ring-theory.binomial-theorem-rings using
  ( binomial-theorem-Ring)
open import ring-theory.binomial-theorem-semirings using
  ( binomial-theorem-Semiring)
open import elementary-number-theory.binomial-theorem-integers using
  ( binomial-theorem-ℤ)
open import elementary-number-theory.binomial-theorem-natural-numbers using
  ( binomial-theorem-ℕ)
```

### [52. The Number of Subsets of a Set](https://www.cs.ru.nl/~freek/100/#52) {#52}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

```agda
open import univalent-combinatorics.decidable-subtypes using
  ( number-of-elements-decidable-subtype-is-finite)
```

### [58. Formula for the number of combinations](https://www.cs.ru.nl/~freek/100/#58) {#58}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

```agda
open import univalent-combinatorics.binomial-types using
  ( has-cardinality-binomial-type)
```

### [60. Bezout's Lemma](https://www.cs.ru.nl/~freek/100/#60) {#60}

**Author:** [Bryan Lu](https://blu-bird.github.io)

Note that the 60th theorem in Freek's list is listed as "Bezout's Theorem",
while the linked theorems are formalizations of Bezout's lemma, even though
these are different statements.

```agda
open import elementary-number-theory.bezouts-lemma-integers using
  ( bezouts-lemma-ℤ)
open import elementary-number-theory.bezouts-lemma-natural-numbers using
  ( bezouts-lemma-ℕ)
```

### [63. Cantor's Theorem](https://www.cs.ru.nl/~freek/100/#63) {#63}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

```agda
open import foundation.cantors-theorem using
  ( theorem-Cantor)
```

### [69. Greatest Common Divisor Algorithm](https://www.cs.ru.nl/~freek/100/#69) {#69}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

```agda
open import
  elementary-number-theory.greatest-common-divisor-natural-numbers using
  ( GCD-ℕ)
```

### [74. The Principle of Mathematical Induction](https://www.cs.ru.nl/~freek/100/#74) {#74}

**Author:** [Egbert Rijke](https://egbertrijke.github.io)

```agda
open import elementary-number-theory.natural-numbers using
  ( ind-ℕ)
```

### [80. The Fundamental Theorem of Arithmetic](https://www.cs.ru.nl/~freek/100/#80) {#80}

**Author:** [Victor Blanchi](https://github.com/VictorBlanchi)

```agda
open import elementary-number-theory.fundamental-theorem-of-arithmetic using
  ( fundamental-theorem-arithmetic-list-ℕ)
```

### [91. The Triangle Inequality](https://www.cs.ru.nl/~freek/100/#91) {#91}

**Author:** [malarbol](https://github.com/malarbol)

```agda
open import real-numbers.metric-space-of-real-numbers using
  ( is-triangular-premetric-leq-ℝ)
```

### [96. Principle of Inclusion/Exclusion](https://www.cs.ru.nl/~freek/100/#96) {#96}

> This is not yet formalized.

## References

{{#bibliography}}

## External links

- The spiritual successor to _Formalizing 100 Theorems_ is
  [_1000+ theorems_](https://1000-plus.github.io/), also due to Freek Wiedijk.
