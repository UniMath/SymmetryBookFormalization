# Prime divisors of natural numbers

```agda
module elementary-number-theory.prime-divisors-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "prime divisor" Disambiguation="natural numbers" Agda=is-prime-divisor-ℕ}} of a [natural number](elementary-number-theory.natural-numbers.md) $n$ is a [prime number](elementary-number-theory.prime-numbers.md) $p$ which is a [divisor](elementary-number-theory.divisibility-natural-numbers.md) of $n$.

## Definitions

### The predicate of being a prime divisor

```agda
module _
  (n d : ℕ)
  where
  
  is-prime-divisor-ℕ :
    UU lzero
  is-prime-divisor-ℕ =
    is-prime-ℕ d × is-divisor-ℕ n d

  is-prop-is-prime-divisor-ℕ :
    is-prop is-prime-divisor-ℕ
  is-prop-is-prime-divisor-ℕ =
    is-prop-Σ
      ( is-prop-is-prime-ℕ d)
      ( λ H → is-prop-div-ℕ d n (inl (is-nonzero-is-prime-ℕ d H)))

  is-prime-divisor-prop-ℕ :
    Prop lzero
  pr1 is-prime-divisor-prop-ℕ =
    is-prime-divisor-ℕ
  pr2 is-prime-divisor-prop-ℕ =
    is-prop-is-prime-divisor-ℕ

  is-decidable-is-prime-divisor-ℕ :
    is-decidable is-prime-divisor-ℕ
  is-decidable-is-prime-divisor-ℕ =
    is-decidable-product (is-decidable-is-prime-ℕ d) (is-decidable-div-ℕ d n)

  is-decidable-prop-is-prime-divisor-ℕ :
    is-decidable-prop is-prime-divisor-ℕ
  pr1 is-decidable-prop-is-prime-divisor-ℕ =
    is-prop-is-prime-divisor-ℕ
  pr2 is-decidable-prop-is-prime-divisor-ℕ =
    is-decidable-is-prime-divisor-ℕ

  is-prime-divisor-decidable-prop-ℕ :
    Decidable-Prop lzero
  pr1 is-prime-divisor-decidable-prop-ℕ =
    is-prime-divisor-ℕ
  pr2 is-prime-divisor-decidable-prop-ℕ =
    is-decidable-prop-is-prime-divisor-ℕ
```


