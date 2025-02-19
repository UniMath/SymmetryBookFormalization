# Strictly ordered pairs of natural numbers

```agda
module elementary-number-theory.strictly-ordered-pairs-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.pairs-of-distinct-elements
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "strictly ordered pair of natural numbers" Agda=strictly-ordered-pair-ℕ}} consists of `x y : ℕ` satisfying the [strict inequality](elementary-number-theory.strict-inequality-natural-numbers.md)
`x < y`.

## Definition

```agda
strictly-ordered-pair-ℕ : UU lzero
strictly-ordered-pair-ℕ = Σ ℕ (λ x → Σ ℕ (λ y → le-ℕ x y))

module _
  (p : strictly-ordered-pair-ℕ)
  where

  first-strictly-ordered-pair-ℕ : ℕ
  first-strictly-ordered-pair-ℕ = pr1 p

  second-strictly-ordered-pair-ℕ : ℕ
  second-strictly-ordered-pair-ℕ = pr1 (pr2 p)

  strict-inequality-strictly-ordered-pair-ℕ :
    le-ℕ first-strictly-ordered-pair-ℕ second-strictly-ordered-pair-ℕ
  strict-inequality-strictly-ordered-pair-ℕ = pr2 (pr2 p)
```

## Properties

### Strictly ordered pairs of natural numbers are pairs of distinct elements

```agda
pair-of-distinct-elements-strictly-ordered-pair-ℕ :
  strictly-ordered-pair-ℕ → pair-of-distinct-elements ℕ
pair-of-distinct-elements-strictly-ordered-pair-ℕ (a , b , H) =
  (a , b , neq-le-ℕ a b H)
```

### Any pair of distinct elements of natural numbers can be strictly ordered

```agda
strictly-ordered-pair-pair-of-distinct-elements-ℕ' :
  (a b : ℕ) → a ≠ b → strictly-ordered-pair-ℕ
strictly-ordered-pair-pair-of-distinct-elements-ℕ' zero-ℕ zero-ℕ H =
  ex-falso (H refl)
strictly-ordered-pair-pair-of-distinct-elements-ℕ' zero-ℕ (succ-ℕ b) H =
  (0 , succ-ℕ b , star)
strictly-ordered-pair-pair-of-distinct-elements-ℕ' (succ-ℕ a) zero-ℕ H =
  (0 , succ-ℕ a , star)
strictly-ordered-pair-pair-of-distinct-elements-ℕ' (succ-ℕ a) (succ-ℕ b) H =
  map-Σ
    ( λ x → Σ ℕ (λ y → le-ℕ x y))
    ( succ-ℕ)
    ( λ x →
      map-Σ (le-ℕ (succ-ℕ x)) succ-ℕ (λ y → id))
    ( strictly-ordered-pair-pair-of-distinct-elements-ℕ' a b
      ( λ p → H (ap succ-ℕ p)))

strictly-ordered-pair-pair-of-distinct-elements-ℕ :
  pair-of-distinct-elements ℕ → strictly-ordered-pair-ℕ
strictly-ordered-pair-pair-of-distinct-elements-ℕ (a , b , H) =
  strictly-ordered-pair-pair-of-distinct-elements-ℕ' a b H
```
