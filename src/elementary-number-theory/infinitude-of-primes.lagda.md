# The infinitude of primes

```agda
module elementary-number-theory.infinitude-of-primes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.factorials
open import elementary-number-theory.lower-bounds-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers
open import elementary-number-theory.proper-divisors-natural-numbers
open import elementary-number-theory.sieve-of-eratosthenes
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.iterating-functions
open import foundation.negation
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

We show, using the
[sieve of Eratosthenes](elementary-number-theory.sieve-of-eratosthenes.md) and
the
[well-ordering principle of `ℕ`](elementary-number-theory.well-ordering-principle-natural-numbers.md),
that there are infinitely many
[primes](elementary-number-theory.prime-numbers.md). Consequently we obtain the
function that returns for each `n` the `n`-th prime, and we obtain the function
that counts the number of primes below a number `n`. This result is known as
{{#concept "Euclid's theorem" WD="Euclid's theorem" WDID=Q1506253 Agda=infinitude-of-primes-ℕ}}

The infinitude of primes is the [11th](literature.100-theorems.md#11) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

## Definition

We begin by stating the
{{#concept "infinitude of primes" Agda=Infinitude-Of-Primes-ℕ}} in type theory.

```agda
Infinitude-Of-Primes-ℕ : UU lzero
Infinitude-Of-Primes-ℕ = (n : ℕ) → Σ ℕ (λ p → is-prime-ℕ p × le-ℕ n p)
```

## Theorem

### The infinitude of primes

```agda
minimal-element-in-sieve-of-eratosthenes-ℕ :
  (n : ℕ) → minimal-element-ℕ (in-sieve-of-eratosthenes-ℕ n)
minimal-element-in-sieve-of-eratosthenes-ℕ n =
  well-ordering-principle-ℕ
    ( in-sieve-of-eratosthenes-ℕ n)
    ( is-decidable-in-sieve-of-eratosthenes-ℕ n)
    ( pair
      ( succ-ℕ (factorial-ℕ n))
      ( in-sieve-of-eratosthenes-succ-factorial-ℕ n))

larger-prime-ℕ : ℕ → ℕ
larger-prime-ℕ n = pr1 (minimal-element-in-sieve-of-eratosthenes-ℕ n)

in-sieve-of-eratosthenes-larger-prime-ℕ :
  (n : ℕ) → in-sieve-of-eratosthenes-ℕ n (larger-prime-ℕ n)
in-sieve-of-eratosthenes-larger-prime-ℕ n =
  pr1 (pr2 (minimal-element-in-sieve-of-eratosthenes-ℕ n))

is-one-is-divisor-below-larger-prime-ℕ :
  (n : ℕ) → is-one-is-divisor-below-ℕ n (larger-prime-ℕ n)
is-one-is-divisor-below-larger-prime-ℕ n =
  pr2 (in-sieve-of-eratosthenes-larger-prime-ℕ n)

le-larger-prime-ℕ : (n : ℕ) → le-ℕ n (larger-prime-ℕ n)
le-larger-prime-ℕ n = pr1 (in-sieve-of-eratosthenes-larger-prime-ℕ n)

is-nonzero-larger-prime-ℕ : (n : ℕ) → is-nonzero-ℕ (larger-prime-ℕ n)
is-nonzero-larger-prime-ℕ n =
  is-nonzero-le-ℕ n (larger-prime-ℕ n) (le-larger-prime-ℕ n)

is-lower-bound-larger-prime-ℕ :
  (n : ℕ) → is-lower-bound-ℕ (in-sieve-of-eratosthenes-ℕ n) (larger-prime-ℕ n)
is-lower-bound-larger-prime-ℕ n =
  pr2 (pr2 (minimal-element-in-sieve-of-eratosthenes-ℕ n))

is-not-one-larger-prime-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → is-not-one-ℕ (larger-prime-ℕ n)
is-not-one-larger-prime-ℕ n H p with is-successor-is-nonzero-ℕ H
... | pair k refl =
  neq-le-ℕ {1} {larger-prime-ℕ n}
    ( concatenate-leq-le-ℕ 1
      ( succ-ℕ k)
      ( larger-prime-ℕ n)
      ( star)
      ( le-larger-prime-ℕ (succ-ℕ k)))
    ( inv p)

not-in-sieve-of-eratosthenes-is-proper-divisor-larger-prime-ℕ :
  (n x : ℕ) → is-proper-divisor-ℕ (larger-prime-ℕ n) x →
  ¬ (in-sieve-of-eratosthenes-ℕ n x)
not-in-sieve-of-eratosthenes-is-proper-divisor-larger-prime-ℕ n x H K =
  ex-falso
    ( contradiction-le-ℕ x (larger-prime-ℕ n)
      ( le-is-proper-divisor-ℕ x (larger-prime-ℕ n)
        ( is-nonzero-larger-prime-ℕ n)
        ( H))
      ( is-lower-bound-larger-prime-ℕ n x K))

is-one-is-proper-divisor-larger-prime-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → is-one-is-proper-divisor-ℕ (larger-prime-ℕ n)
is-one-is-proper-divisor-larger-prime-ℕ n H x (pair f K) =
  is-one-is-divisor-below-larger-prime-ℕ n x
    ( leq-not-le-ℕ n x
      ( is-empty-left-factor-is-empty-product
        ( not-in-sieve-of-eratosthenes-is-proper-divisor-larger-prime-ℕ n x
          ( pair f K))
        ( λ y l d →
          is-one-is-divisor-below-larger-prime-ℕ n y l
            ( transitive-div-ℕ y x (larger-prime-ℕ n) K d))))
    ( K)

is-prime-larger-prime-ℕ :
  (n : ℕ) → is-nonzero-ℕ n → is-prime-ℕ (larger-prime-ℕ n)
is-prime-larger-prime-ℕ n H =
  is-prime-is-prime-easy-ℕ
    ( larger-prime-ℕ n)
    ( pair
      ( is-not-one-larger-prime-ℕ n H)
      ( is-one-is-proper-divisor-larger-prime-ℕ n H))

infinitude-of-primes-ℕ : Infinitude-Of-Primes-ℕ
infinitude-of-primes-ℕ n with is-decidable-is-zero-ℕ n
... | inl refl = pair 2 (pair is-prime-two-ℕ star)
... | inr H =
  pair
    ( larger-prime-ℕ n)
    ( pair
      ( is-prime-larger-prime-ℕ n H)
      ( le-larger-prime-ℕ n))
```

## Consequences

### The function that returns the `n`-th prime

The function `prime-ℕ` is defined to start at `prime-ℕ 0 := 2`

```agda
prime-ℕ : ℕ → ℕ
prime-ℕ n = iterate (succ-ℕ n) (λ x → pr1 (infinitude-of-primes-ℕ x)) 0

is-prime-prime-ℕ : (n : ℕ) → is-prime-ℕ (prime-ℕ n)
is-prime-prime-ℕ zero-ℕ = pr1 (pr2 (infinitude-of-primes-ℕ 0))
is-prime-prime-ℕ (succ-ℕ n) = pr1 (pr2 (infinitude-of-primes-ℕ (prime-ℕ n)))
```

### The prime counting function

The prime counting function is defined such that `prime-counting-ℕ n` is the
number of primes `≤ n`

```agda
prime-counting-succ-ℕ :
  (n : ℕ) → is-decidable (is-prime-ℕ (succ-ℕ n)) → ℕ → ℕ
prime-counting-succ-ℕ n (inl d) x = succ-ℕ x
prime-counting-succ-ℕ n (inr d) x = x

prime-counting-ℕ : ℕ → ℕ
prime-counting-ℕ zero-ℕ = zero-ℕ
prime-counting-ℕ (succ-ℕ n) =
  prime-counting-succ-ℕ n
    ( is-decidable-is-prime-ℕ (succ-ℕ n))
    ( prime-counting-ℕ n)
```

### A very weak lower bound on the prime counting function

In section 2.2 of {{#cite HW08}}, Hardy and Wright illustrate how Euclid's proof
of the infinitued of primes can be used to derive a lower bound on the prime
counting function. This lower bound is extremely weak, but could nevertheless be
found illustrative.

## References

{{#bibliography}}

## External links

- [Euclid's theorem](https://en.wikipedia.org/wiki/Euclid%27s_theorem) on
  Wikipedia
