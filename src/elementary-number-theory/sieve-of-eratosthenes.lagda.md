# The sieve of Eratosthenes

```agda
module elementary-number-theory.sieve-of-eratosthenes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-types
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.factorials
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

The sieve of Erathostenes is a sequence of subsets of the natural numbers used
to prove the infinitude of primes.

## Definition

```agda
is-one-is-divisor-below-ℕ : ℕ → ℕ → UU lzero
is-one-is-divisor-below-ℕ n a =
  (x : ℕ) → leq-ℕ x n → div-ℕ x a → is-one-ℕ x

in-sieve-of-eratosthenes-ℕ : ℕ → ℕ → UU lzero
in-sieve-of-eratosthenes-ℕ n a =
  (le-ℕ n a) × (is-one-is-divisor-below-ℕ n a)

le-in-sieve-of-eratosthenes-ℕ :
  (n a : ℕ) → in-sieve-of-eratosthenes-ℕ n a → le-ℕ n a
le-in-sieve-of-eratosthenes-ℕ n a = pr1
```

## Properties

### Being in the sieve of Eratosthenes is decidable

```agda
is-decidable-in-sieve-of-eratosthenes-ℕ :
  (n a : ℕ) → is-decidable (in-sieve-of-eratosthenes-ℕ n a)
is-decidable-in-sieve-of-eratosthenes-ℕ n a =
  is-decidable-product
    ( is-decidable-le-ℕ n a)
    ( is-decidable-bounded-Π-ℕ
      ( λ x → leq-ℕ x n)
      ( λ x → div-ℕ x a → is-one-ℕ x)
      ( λ x → is-decidable-leq-ℕ x n)
      ( λ x →
        is-decidable-function-type
          ( is-decidable-div-ℕ x a)
          ( is-decidable-is-one-ℕ x))
      ( n)
      ( λ x → id))
```

### The successor of the `n`-th factorial is in the `n`-th sieve

```agda
in-sieve-of-eratosthenes-succ-factorial-ℕ :
  (n : ℕ) → in-sieve-of-eratosthenes-ℕ n (succ-ℕ (factorial-ℕ n))
pr1 (in-sieve-of-eratosthenes-succ-factorial-ℕ zero-ℕ) = star
pr2 (in-sieve-of-eratosthenes-succ-factorial-ℕ zero-ℕ) x l d =
  ex-falso
    ( Eq-eq-ℕ
      ( is-zero-is-zero-div-ℕ x 2 d (is-zero-leq-zero-ℕ x l)))
pr1 (in-sieve-of-eratosthenes-succ-factorial-ℕ (succ-ℕ n)) =
  concatenate-leq-le-ℕ
    ( succ-ℕ n)
    ( factorial-ℕ (succ-ℕ n))
    ( succ-ℕ (factorial-ℕ (succ-ℕ n)))
    ( leq-factorial-ℕ (succ-ℕ n))
    ( succ-le-ℕ (factorial-ℕ (succ-ℕ n)))
pr2 (in-sieve-of-eratosthenes-succ-factorial-ℕ (succ-ℕ n)) x l (pair y p) with
  is-decidable-is-zero-ℕ x
... | inl refl =
  ex-falso
    ( is-nonzero-succ-ℕ
      ( factorial-ℕ (succ-ℕ n))
      ( inv p ∙ (right-zero-law-mul-ℕ y)))
... | inr f =
  is-one-div-ℕ x
    ( factorial-ℕ (succ-ℕ n))
    ( div-factorial-ℕ (succ-ℕ n) x l f)
    ( pair y p)
```
