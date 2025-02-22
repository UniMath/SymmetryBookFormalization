# Proper divisors of natural numbers

```agda
module elementary-number-theory.proper-divisors-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
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
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.type-arithmetic-empty-type
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "proper divisor" Disambituation="natural numbers" Agda=is-proper-divisor-ℕ}}
of a [natural number](elementary-number-theory.natural-numbers.md) `n` is a
natural number `d ≠ n` that
[divides](elementary-number-theory.divisbility-natural-numbers.md) `n`.

## Definitions

### The predicate of being a proper divisor of a natural number

```agda
is-proper-divisor-ℕ : ℕ → ℕ → UU lzero
is-proper-divisor-ℕ n d = (d ≠ n) × (div-ℕ d n)
```

## Properties

### Being a proper divisor of a natural number is decidable

```agda
is-decidable-is-proper-divisor-ℕ :
  (n d : ℕ) → is-decidable (is-proper-divisor-ℕ n d)
is-decidable-is-proper-divisor-ℕ n d =
  is-decidable-product
    ( is-decidable-neg (has-decidable-equality-ℕ d n))
    ( is-decidable-div-ℕ d n)
```

### Any successor is a proper divisor of $0$

```agda
is-proper-divisor-zero-succ-ℕ : (n : ℕ) → is-proper-divisor-ℕ zero-ℕ (succ-ℕ n)
pr1 (is-proper-divisor-zero-succ-ℕ n) = is-nonzero-succ-ℕ n
pr2 (is-proper-divisor-zero-succ-ℕ n) = div-zero-ℕ (succ-ℕ n)
```

### Any proper divisor of a natural number is strictly smaller than its dividend

```agda
le-is-proper-divisor-ℕ :
  (x y : ℕ) → is-nonzero-ℕ y → is-proper-divisor-ℕ y x → le-ℕ x y
le-is-proper-divisor-ℕ x y H K =
  le-leq-neq-ℕ (leq-div-ℕ x y H (pr2 K)) (pr1 K)
```

### Being a proper divisor is a property

```agda
is-prop-is-proper-divisor-ℕ : (n d : ℕ) → is-prop (is-proper-divisor-ℕ n d)
is-prop-is-proper-divisor-ℕ n zero-ℕ (pair f g) =
  ex-falso (f (inv (is-zero-div-zero-ℕ n g)))
is-prop-is-proper-divisor-ℕ n (succ-ℕ d) =
  is-prop-product
    ( is-prop-neg)
    ( is-prop-div-ℕ (succ-ℕ d) n (inl (is-nonzero-succ-ℕ d)))
```

### If a natural number has a proper divisor, then `1` is a proper divisor

```agda
is-proper-divisor-one-is-proper-divisor-ℕ :
  {n x : ℕ} → is-proper-divisor-ℕ n x → is-proper-divisor-ℕ n 1
pr1 (is-proper-divisor-one-is-proper-divisor-ℕ {.1} {x} H) refl =
  pr1 H (is-one-div-one-ℕ x (pr2 H))
pr1 (pr2 (is-proper-divisor-one-is-proper-divisor-ℕ {n} {x} H)) = n
pr2 (pr2 (is-proper-divisor-one-is-proper-divisor-ℕ {n} {x} H)) =
  right-unit-law-mul-ℕ n
```

### If `x` is nonzero and `d | x` is a proper divisor, then `1 < x/d`

```agda
le-one-quotient-div-is-proper-divisor-ℕ :
  (d x : ℕ) → is-nonzero-ℕ x → (H : div-ℕ d x) →
  d ≠ x → le-ℕ 1 (quotient-div-ℕ d x H)
le-one-quotient-div-is-proper-divisor-ℕ d x f H g =
  map-left-unit-law-coproduct-is-empty
    ( is-one-ℕ (quotient-div-ℕ d x H))
    ( le-ℕ 1 (quotient-div-ℕ d x H))
    ( map-neg (eq-is-one-quotient-div-ℕ d x H) g)
    ( eq-or-le-leq-ℕ' 1
      ( quotient-div-ℕ d x H)
      ( leq-one-quotient-div-ℕ d x H (leq-one-is-nonzero-ℕ x f)))
```

### A divisor `d` of a number `n` is a proper divisor if and only if `x ∤ d`

```agda
neg-div-is-proper-divisor-ℕ :
  (d n : ℕ) → is-proper-divisor-ℕ n d → ¬ div-ℕ n d
neg-div-is-proper-divisor-ℕ d n (np , H) K =
  np (antisymmetric-div-ℕ d n H K)

is-proper-divisor-neg-div-ℕ :
  (d n : ℕ) → div-ℕ d n → ¬ div-ℕ n d → is-proper-divisor-ℕ n d
pr1 (is-proper-divisor-neg-div-ℕ d .d H K) refl = K H
pr2 (is-proper-divisor-neg-div-ℕ d n H K) = H
```

## See also

- [Prime numbers](elementary-number-theory.prime-numbers.md)
- [Nontrivial divisors](elementary-number-theory.nontrivial-divisors-natural-numbers.md)
