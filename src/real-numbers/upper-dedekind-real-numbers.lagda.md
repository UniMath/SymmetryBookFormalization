# Upper Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.upper-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.powersets
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universal-quantification
open import foundation.universe-levels
```

</details>

## Idea

A [subtype](foundation-core.subtypes.md) `U` of
[the rational numbers](elementary-number-theory.rational-numbers.md) is an
{{#concept "upper Dedekind cut" Agda=is-upper-dedekind-cut}} if it satisfies the
following two conditions:

1. _Inhabitedness_. `U` is [inhabited](foundation.inhabited-subtypes.md).
2. _Upper roundedness_. A rational number `q` is in `U`
   [if and only if](foundation.logical-equivalences.md) there
   [exists](foundation.existential-quantification.md) `p < q` such that `p ∈ U`.

The {{#concept "upper Dedekind real numbers" Agda=upper-ℝ}} is the type of all
upper Dedekind cuts.

## Definition

### Upper Dedekind cuts

```agda
module _
  {l : Level}
  (U : subtype l ℚ)
  where

  is-upper-dedekind-cut-Prop : Prop l
  is-upper-dedekind-cut-Prop =
    (∃ ℚ U) ∧
    (∀' ℚ (λ q → U q ⇔ (∃ ℚ (λ p → le-ℚ-Prop p q ∧ U p))))

  is-upper-dedekind-cut : UU l
  is-upper-dedekind-cut = type-Prop is-upper-dedekind-cut-Prop
```

## The upper Dedekind real numbers

```agda
upper-ℝ : (l : Level) → UU (lsuc l)
upper-ℝ l = Σ (subtype l ℚ) is-upper-dedekind-cut

module _
  {l : Level}
  (x : upper-ℝ l)
  where

  cut-upper-ℝ : subtype l ℚ
  cut-upper-ℝ = pr1 x

  is-in-cut-upper-ℝ : ℚ → UU l
  is-in-cut-upper-ℝ = is-in-subtype cut-upper-ℝ

  is-upper-dedekind-cut-upper-ℝ : is-upper-dedekind-cut cut-upper-ℝ
  is-upper-dedekind-cut-upper-ℝ = pr2 x

  is-inhabited-cut-upper-ℝ : exists ℚ cut-upper-ℝ
  is-inhabited-cut-upper-ℝ = pr1 (pr2 x)

  is-rounded-cut-upper-ℝ :
    (q : ℚ) →
    is-in-cut-upper-ℝ q ↔ exists ℚ (λ p → le-ℚ-Prop p q ∧ cut-upper-ℝ p)
  is-rounded-cut-upper-ℝ = pr2 (pr2 x)
```

## Properties

### There is a least upper Dedekind real, whose cut is all rational numbers

```agda
neg-∞-upper-ℝ : upper-ℝ lzero
pr1 neg-∞-upper-ℝ _ = unit-Prop
pr1 (pr2 neg-∞-upper-ℝ) = intro-exists zero-ℚ star
pr1 (pr2 (pr2 neg-∞-upper-ℝ) q) _ =
  intro-exists (q -ℚ one-ℚ) (le-diff-rational-ℚ⁺ q one-ℚ⁺ , star)
pr2 (pr2 (pr2 neg-∞-upper-ℝ) q) _ = star
```

### The upper Dedekind reals form a set

```agda
abstract
  is-set-upper-ℝ : (l : Level) → is-set (upper-ℝ l)
  is-set-upper-ℝ l =
    is-set-Σ
      ( is-set-function-type (is-trunc-Truncated-Type neg-one-𝕋))
      ( λ q → is-set-is-prop (is-prop-type-Prop (is-upper-dedekind-cut-Prop q)))
```

### Upper Dedekind cuts are closed under strict inequality on the rationals

```agda
module _
  {l : Level} (x : upper-ℝ l) (p q : ℚ)
  where

  is-in-cut-le-ℚ-upper-ℝ :
    le-ℚ p q → is-in-cut-upper-ℝ x p → is-in-cut-upper-ℝ x q
  is-in-cut-le-ℚ-upper-ℝ p<q p<x =
    backward-implication
      ( is-rounded-cut-upper-ℝ x q)
      ( intro-exists p (p<q , p<x))
```

### Upper Dedekind cuts are closed under inequality on the rationals

```agda
module _
  {l : Level} (x : upper-ℝ l) (p q : ℚ)
  where

  is-in-cut-leq-ℚ-upper-ℝ :
    leq-ℚ p q → is-in-cut-upper-ℝ x p → is-in-cut-upper-ℝ x q
  is-in-cut-leq-ℚ-upper-ℝ p≤q x<p with decide-le-leq-ℚ p q
  ... | inl p<q = is-in-cut-le-ℚ-upper-ℝ x p q p<q x<p
  ... | inr q≤p = tr (is-in-cut-upper-ℝ x) (antisymmetric-leq-ℚ p q p≤q q≤p) x<p
```

### Two upper real numbers with the same cut are equal

```agda
module _
  {l : Level} (x y : upper-ℝ l)
  where

  eq-eq-cut-upper-ℝ : cut-upper-ℝ x ＝ cut-upper-ℝ y → x ＝ y
  eq-eq-cut-upper-ℝ = eq-type-subtype is-upper-dedekind-cut-Prop

  eq-sim-cut-upper-ℝ : sim-subtype (cut-upper-ℝ x) (cut-upper-ℝ y) → x ＝ y
  eq-sim-cut-upper-ℝ =
    eq-eq-cut-upper-ℝ ∘
    antisymmetric-sim-subtype (cut-upper-ℝ x) (cut-upper-ℝ y)
```

## See also

- Lower Dedekind cuts, the dual structure, are defined in
  [`real-numbers.lower-dedekind-real-numbers`](real-numbers.lower-dedekind-real-numbers.md).
- Dedekind cuts, which form the usual real numbers, are defined in
  [`real-numbers.dedekind-real-numbers`](real-numbers.dedekind-real-numbers.md)

## References

This page follows the terminology used in the exercises of Section 11 in
{{#cite UF13}}.

{{#bibliography}}
