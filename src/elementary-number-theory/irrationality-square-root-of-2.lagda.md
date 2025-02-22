# The irrationality of the square root of 2

```agda
module elementary-number-theory.irrationality-square-root-of-2 where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.reduced-integer-fractions
open import elementary-number-theory.squares-natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negation
```

</details>

## Idea

The {{#concept "irrationality of √2" Agda=irrationality-sqrt-2}} is the theorem
that there is no [rational number](elementary-number-theory.rational-numbers.md)
whose square is $2$.

**Proof.** Suppose that there is a rational number $q$ such that $q^2 = 2$. Then
we can represent $q$ as a
[reduced integer fraction](elementary-number-theory.reduced-integer-fractions.md)
$\frac{a}{b}$ such that

$$
a^2 = 2b^2.
$$

Since $a^2$ is an
[even number](elementary-number-theory.parity-natural-numbers.md), it follows
that $a$ is an even number. In other words, $a = 2k$ for some number $k$. This
implies that $a^2 = 4k^2$, and thus we see that

$$
2k^2 = b^2.
$$

Now we see that $b^2$ is even, which implies that $b$ is even. The consequence
that both $a$ and $b$ are even contradicts the assumption that $\frac{a}{b}$ is
a reduced fraction.

## Properties

### There is no reduced fraction whose square is $2$

```text
not-two-square-reduced-fraction-ℤ :
  (x : fraction-ℤ) (H : is-reduced-fraction-ℤ x) →
  ¬ sim-fraction-ℤ (mul-fraction-ℤ x x) (in-fraction-ℤ (int-ℕ 2))
not-two-square-reduced-fraction-ℤ x@(a , b , pb) H K =
  {!!}
```
