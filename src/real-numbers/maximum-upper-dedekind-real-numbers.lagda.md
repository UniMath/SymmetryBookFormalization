# The maximum of upper Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.maximum-upper-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.inhabited-types
open import foundation.intersections-subtypes
open import foundation.logical-equivalences
open import foundation.powersets
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import order-theory.large-join-semilattices
open import order-theory.least-upper-bounds-large-posets

open import real-numbers.inequality-upper-dedekind-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

The maximum of two
[upper Dedekind real numbers](real-numbers.upper-dedekind-real-numbers.md) `x`,
`y` is a upper Dedekind real number with cut equal to the intersection of the
cuts of `x` and `y`.

## Definition

### Binary maximum

```agda
module _
  {l1 l2 : Level} (x : upper-ℝ l1) (y : upper-ℝ l2)
  where

  cut-binary-max-upper-ℝ : subtype (l1 ⊔ l2) ℚ
  cut-binary-max-upper-ℝ = intersection-subtype (cut-upper-ℝ x) (cut-upper-ℝ y)

  max-inhabitants-in-binary-max-upper-ℝ :
    (p q : ℚ) → (is-in-cut-upper-ℝ x p) → (is-in-cut-upper-ℝ y q) →
    is-in-subtype cut-binary-max-upper-ℝ (max-ℚ p q)
  max-inhabitants-in-binary-max-upper-ℝ p q x<p y<q =
    is-in-cut-leq-ℚ-upper-ℝ x p (max-ℚ p q) (leq-left-max-ℚ p q) x<p ,
    is-in-cut-leq-ℚ-upper-ℝ y q (max-ℚ p q) (leq-right-max-ℚ p q) y<q

  is-inhabited-cut-binary-max-upper-ℝ : exists ℚ cut-binary-max-upper-ℝ
  is-inhabited-cut-binary-max-upper-ℝ =
    map-binary-exists
      ( is-in-subtype cut-binary-max-upper-ℝ)
      ( max-ℚ)
      ( max-inhabitants-in-binary-max-upper-ℝ)
      ( is-inhabited-cut-upper-ℝ x)
      ( is-inhabited-cut-upper-ℝ y)

  is-rounded-cut-binary-max-upper-ℝ :
    (q : ℚ) →
    is-in-subtype cut-binary-max-upper-ℝ q ↔
    exists ℚ (λ p → le-ℚ-Prop p q ∧ cut-binary-max-upper-ℝ p)
  pr1 (is-rounded-cut-binary-max-upper-ℝ q) (x<q , y<q) =
    map-binary-exists
      ( λ p → le-ℚ p q × is-in-subtype cut-binary-max-upper-ℝ p)
      ( max-ℚ)
      (λ px py (px<q , x<px) (py<q , y<py) →
        le-max-le-both-ℚ q px py px<q py<q ,
        max-inhabitants-in-binary-max-upper-ℝ px py x<px y<py)
      ( forward-implication (is-rounded-cut-upper-ℝ x q) x<q)
      ( forward-implication (is-rounded-cut-upper-ℝ y q) y<q)
  pr2 (is-rounded-cut-binary-max-upper-ℝ q) =
    elim-exists
      ( cut-binary-max-upper-ℝ q)
      ( λ p (p<q , x<p , y<p) →
        backward-implication
          ( is-rounded-cut-upper-ℝ x q)
          ( intro-exists p (p<q , x<p)) ,
        backward-implication
          ( is-rounded-cut-upper-ℝ y q)
          ( intro-exists p (p<q , y<p)))

  binary-max-upper-ℝ : upper-ℝ (l1 ⊔ l2)
  pr1 binary-max-upper-ℝ = cut-binary-max-upper-ℝ
  pr1 (pr2 binary-max-upper-ℝ) = is-inhabited-cut-binary-max-upper-ℝ
  pr2 (pr2 binary-max-upper-ℝ) = is-rounded-cut-binary-max-upper-ℝ
```

## Properties

### The binary maximum is a least upper bound

```agda
  is-least-binary-upper-bound-binary-max-upper-ℝ :
    is-least-binary-upper-bound-Large-Poset
      ( upper-ℝ-Large-Poset)
      ( x)
      ( y)
      ( binary-max-upper-ℝ)
  is-least-binary-upper-bound-binary-max-upper-ℝ z =
    is-greatest-binary-lower-bound-intersection-subtype
      ( cut-upper-ℝ x)
      ( cut-upper-ℝ y)
      ( cut-upper-ℝ z)
```

### The upper Dedekind reals form a large join-semilattice

```agda
has-joins-upper-ℝ : has-joins-Large-Poset upper-ℝ-Large-Poset
join-has-joins-Large-Poset has-joins-upper-ℝ = binary-max-upper-ℝ
is-least-binary-upper-bound-join-has-joins-Large-Poset has-joins-upper-ℝ =
  is-least-binary-upper-bound-binary-max-upper-ℝ

is-large-join-semilattice-upper-ℝ :
  is-large-join-semilattice-Large-Poset upper-ℝ-Large-Poset
has-joins-is-large-join-semilattice-Large-Poset
  is-large-join-semilattice-upper-ℝ = has-joins-upper-ℝ
has-bottom-element-is-large-join-semilattice-Large-Poset
  is-large-join-semilattice-upper-ℝ = has-bottom-element-upper-ℝ

upper-ℝ-Large-Join-Semilattice : Large-Join-Semilattice lsuc _⊔_
large-poset-Large-Join-Semilattice upper-ℝ-Large-Join-Semilattice =
  upper-ℝ-Large-Poset
is-large-join-semilattice-Large-Join-Semilattice
  upper-ℝ-Large-Join-Semilattice = is-large-join-semilattice-upper-ℝ
```
