# Largest power divisors of natural numbers

```agda
module elementary-number-theory.largest-power-divisors-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.finite-maps-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximal-structured-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.upper-bounds-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "largest power divisor" Disambiguation="natural numbers" Agda=largest-power-divisor-ℕ}}
of a [natural number](elementary-number-theory.natural-numbers.md) $n$ with base
$m$ is the
[largest number](elementary-number-theory.maximal-structured-natural-numbers.md)
of the form $m^k$ that
[divides](elementary-number-theory.divisibility-natural-numbers.md) $n$.

## Definitions

### Power divisors of natural numbers

```agda
is-power-divisor-ℕ : ℕ → ℕ → ℕ → UU lzero
is-power-divisor-ℕ m n x = is-exponential-ℕ m x × div-ℕ x n

valuation-is-power-divisor-ℕ :
  (m n x : ℕ) → is-power-divisor-ℕ m n x → ℕ
valuation-is-power-divisor-ℕ m n x H =
  pr1 (pr1 H)

compute-exp-valuation-is-power-divisor-ℕ :
  (m n x : ℕ) (H : is-power-divisor-ℕ m n x) →
  m ^ℕ valuation-is-power-divisor-ℕ m n x H ＝ x
compute-exp-valuation-is-power-divisor-ℕ m n x H =
  pr2 (pr1 H)
```

### The predicate of being the largest power divisor of a natural number

```agda
module _
  (m n x : ℕ)
  where
  
  is-largest-power-divisor-ℕ : UU lzero
  is-largest-power-divisor-ℕ =
    Σ ( is-power-divisor-ℕ m n x)
      ( λ H →
        (y : ℕ) (K : is-power-divisor-ℕ m n y) →
        valuation-is-power-divisor-ℕ m n y K ≤-ℕ
        valuation-is-power-divisor-ℕ m n x H)

  is-power-divisor-is-largest-power-divisor-ℕ :
    is-largest-power-divisor-ℕ → is-power-divisor-ℕ m n x
  is-power-divisor-is-largest-power-divisor-ℕ =
    pr1

  valuation-is-largest-power-divisor-ℕ :
    is-largest-power-divisor-ℕ → ℕ
  valuation-is-largest-power-divisor-ℕ H =
    valuation-is-power-divisor-ℕ m n x
      ( is-power-divisor-is-largest-power-divisor-ℕ H)

  compute-exp-valuation-is-largest-power-divisor-ℕ :
    (H : is-largest-power-divisor-ℕ) →
    m ^ℕ valuation-is-largest-power-divisor-ℕ H ＝ x
  compute-exp-valuation-is-largest-power-divisor-ℕ H =
    compute-exp-valuation-is-power-divisor-ℕ m n x
      ( is-power-divisor-is-largest-power-divisor-ℕ H)

  is-upper-bound-valuation-is-largest-power-divisor-ℕ :
    (H : is-largest-power-divisor-ℕ) →
    (y : ℕ) (K : is-power-divisor-ℕ m n y) →
    valuation-is-power-divisor-ℕ m n y K ≤-ℕ
    valuation-is-largest-power-divisor-ℕ H
  is-upper-bound-valuation-is-largest-power-divisor-ℕ =
    pr2
```

### The largest power divisor of a nonzero natural number

```agda
module _
  (m n : ℕ) (H : 1 <-ℕ m) (K : is-nonzero-ℕ n)
  where

  largest-power-divisor-ℕ :
    maximal-element-ℕ
      ( is-structured-value-bound-input-ℕ (is-divisor-ℕ n) (m ^ℕ_) n)
  largest-power-divisor-ℕ =
    maximal-structured-value-bound-input-property-is-finite-map-ℕ
      ( is-divisor-ℕ n)
      ( λ x → is-decidable-div-ℕ x n)
      ( m ^ℕ_)
      ( is-finite-map-exp-ℕ m H)
      ( n)
      ( 0)
      ( leq-one-is-nonzero-ℕ n K)
      ( div-one-ℕ n)

  valuation-largest-power-divisor-ℕ :
    ℕ
  valuation-largest-power-divisor-ℕ =
    nat-maximal-element-ℕ
      ( is-structured-value-bound-input-ℕ (is-divisor-ℕ n) (m ^ℕ_) n)
      ( largest-power-divisor-ℕ)

  nat-largest-power-divisor-ℕ :
    ℕ
  nat-largest-power-divisor-ℕ =
    m ^ℕ valuation-largest-power-divisor-ℕ

  upper-bound-nat-largest-power-divisor-ℕ :
    m ^ℕ valuation-largest-power-divisor-ℕ ≤-ℕ n
  upper-bound-nat-largest-power-divisor-ℕ =
    pr1
      ( structure-maximal-element-ℕ
        ( is-structured-value-bound-input-ℕ (is-divisor-ℕ n) (m ^ℕ_) n)
        ( largest-power-divisor-ℕ))

  div-largest-power-divisor-ℕ :
    div-ℕ (m ^ℕ valuation-largest-power-divisor-ℕ) n
  div-largest-power-divisor-ℕ =
    pr2
      ( structure-maximal-element-ℕ
        ( is-structured-value-bound-input-ℕ (is-divisor-ℕ n) (m ^ℕ_) n)
        ( largest-power-divisor-ℕ))

  is-power-divisor-largest-power-divisor-ℕ :
    is-power-divisor-ℕ m n nat-largest-power-divisor-ℕ
  pr1 (pr1 is-power-divisor-largest-power-divisor-ℕ) =
    valuation-largest-power-divisor-ℕ
  pr2 (pr1 is-power-divisor-largest-power-divisor-ℕ) =
    refl
  pr2 is-power-divisor-largest-power-divisor-ℕ =
    div-largest-power-divisor-ℕ

  is-upper-bound-valuation-largest-power-divisor-ℕ :
    (k : ℕ) → div-ℕ (m ^ℕ k) n → k ≤-ℕ valuation-largest-power-divisor-ℕ
  is-upper-bound-valuation-largest-power-divisor-ℕ k L =
    is-upper-bound-maximal-element-ℕ
      ( is-structured-value-bound-input-ℕ (is-divisor-ℕ n) (m ^ℕ_) n)
      ( largest-power-divisor-ℕ)
      ( k)
      ( leq-div-ℕ (m ^ℕ k) n K L , L)

  is-largest-power-divisor-largest-power-divisor-ℕ :
    is-largest-power-divisor-ℕ m n nat-largest-power-divisor-ℕ
  pr1 is-largest-power-divisor-largest-power-divisor-ℕ =
    is-power-divisor-largest-power-divisor-ℕ
  pr2 is-largest-power-divisor-largest-power-divisor-ℕ y ((k , refl) , K) =
    is-upper-bound-valuation-largest-power-divisor-ℕ k K
```

### Any two largest power divisors are equal

```agda
module _
  (m n x y : ℕ) (H : 1 <-ℕ m)
  where

  eq-valuation-is-largest-power-divisor-ℕ :
    (H : is-largest-power-divisor-ℕ m n x)
    (K : is-largest-power-divisor-ℕ m n y) →
    valuation-is-largest-power-divisor-ℕ m n x H ＝
    valuation-is-largest-power-divisor-ℕ m n y K
  eq-valuation-is-largest-power-divisor-ℕ H K =
    antisymmetric-leq-ℕ
      ( valuation-is-largest-power-divisor-ℕ m n x H)
      ( valuation-is-largest-power-divisor-ℕ m n y K)
      ( is-upper-bound-valuation-is-largest-power-divisor-ℕ m n y K x
        ( is-power-divisor-is-largest-power-divisor-ℕ m n x H))
      ( is-upper-bound-valuation-is-largest-power-divisor-ℕ m n x H y
        ( is-power-divisor-is-largest-power-divisor-ℕ m n y K))

  eq-is-largest-power-divisor-ℕ :
    is-largest-power-divisor-ℕ m n x → is-largest-power-divisor-ℕ m n y →
    x ＝ y
  eq-is-largest-power-divisor-ℕ H K =
    inv (compute-exp-valuation-is-largest-power-divisor-ℕ m n x H) ∙
    ap (m ^ℕ_) (eq-valuation-is-largest-power-divisor-ℕ H K) ∙
    compute-exp-valuation-is-largest-power-divisor-ℕ m n y K
```

## See also

- [2-adic decomposition](elementary-number-theory.2-adic-decomposition.md)
