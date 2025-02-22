# Negation of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.negation-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import real-numbers.dedekind-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.negation-lower-upper-dedekind-real-numbers
open import real-numbers.rational-lower-dedekind-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.rational-upper-dedekind-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

The {{#concept "negation" Disambiguation="Dedekind real number" Agda=neg-ℝ}} of
a [Dedekind real number](real-numbers.dedekind-real-numbers.md) with cuts
`(L, U)` has lower cut equal to the negation of elements of `U`, and upper cut
equal to the negation of elements in `L`.

```agda
module _
  {l : Level} (x : ℝ l)
  where

  lower-real-neg-ℝ : lower-ℝ l
  lower-real-neg-ℝ = neg-upper-ℝ (upper-real-ℝ x)

  upper-real-neg-ℝ : upper-ℝ l
  upper-real-neg-ℝ = neg-lower-ℝ (lower-real-ℝ x)

  lower-cut-neg-ℝ : subtype l ℚ
  lower-cut-neg-ℝ = cut-lower-ℝ lower-real-neg-ℝ

  upper-cut-neg-ℝ : subtype l ℚ
  upper-cut-neg-ℝ = cut-upper-ℝ upper-real-neg-ℝ

  is-disjoint-cut-neg-ℝ :
    (q : ℚ) →
    ¬ (is-in-subtype lower-cut-neg-ℝ q × is-in-subtype upper-cut-neg-ℝ q)
  is-disjoint-cut-neg-ℝ q (in-lower-neg , in-upper-neg) =
    is-disjoint-cut-ℝ x (neg-ℚ q) (in-upper-neg , in-lower-neg)

  is-located-lower-upper-cut-neg-ℝ :
    (q r : ℚ) → le-ℚ q r →
    type-disjunction-Prop (lower-cut-neg-ℝ q) (upper-cut-neg-ℝ r)
  is-located-lower-upper-cut-neg-ℝ q r q<r =
    elim-disjunction
      ( disjunction-Prop (lower-cut-neg-ℝ q) (upper-cut-neg-ℝ r))
      ( inr-disjunction)
      ( inl-disjunction)
      ( is-located-lower-upper-cut-ℝ x (neg-ℚ r) (neg-ℚ q) (neg-le-ℚ q r q<r))

  neg-ℝ : ℝ l
  neg-ℝ =
    real-lower-upper-ℝ
      ( lower-real-neg-ℝ)
      ( upper-real-neg-ℝ)
      ( is-disjoint-cut-neg-ℝ)
      ( is-located-lower-upper-cut-neg-ℝ)
```

## Properties

### The negation function on real numbers is an involution

```agda
neg-neg-ℝ : {l : Level} → (x : ℝ l) → neg-ℝ (neg-ℝ x) ＝ x
neg-neg-ℝ x =
  eq-eq-lower-cut-ℝ
    ( neg-ℝ (neg-ℝ x))
    ( x)
    ( eq-has-same-elements-subtype
      ( lower-cut-ℝ (neg-ℝ (neg-ℝ x)))
      ( lower-cut-ℝ x)
      ( λ q →
        tr (is-in-lower-cut-ℝ x) (neg-neg-ℚ q) ,
        tr (is-in-lower-cut-ℝ x) (inv (neg-neg-ℚ q))))
```

### Negation preserves rationality

```agda
neg-Rational-ℝ : {l : Level} → Rational-ℝ l → Rational-ℝ l
neg-Rational-ℝ (x , q , q≮x , x≮q) =
  neg-ℝ x ,
  neg-ℚ q ,
  x≮q ∘ tr (is-in-upper-cut-ℝ x) (neg-neg-ℚ q) ,
  q≮x ∘ tr (is-in-lower-cut-ℝ x) (neg-neg-ℚ q)

neg-real-ℚ : (q : ℚ) → neg-ℝ (real-ℚ q) ＝ real-ℚ (neg-ℚ q)
neg-real-ℚ q = eq-sim-ℝ (sim-rational-ℝ (neg-Rational-ℝ (rational-real-ℚ q)))
```
