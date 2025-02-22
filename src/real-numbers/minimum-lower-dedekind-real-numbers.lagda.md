# The minimum of lower Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.minimum-lower-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.intersections-subtypes
open import foundation.logical-equivalences
open import foundation.subtypes
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-meet-semilattices
open import order-theory.lower-bounds-large-posets

open import real-numbers.inequality-lower-dedekind-real-numbers
open import real-numbers.lower-dedekind-real-numbers
```

</details>

## Idea

The minimum of two
[lower Dedekind real numbers](real-numbers.lower-dedekind-real-numbers.md) `x`,
`y` is a lower Dedekind real number with cut equal to the intersection of the
cuts of `x` and `y`.

The minimum of a family of lower Dedekind real numbers is not always a lower
Dedekind real number.

## Definition

```agda
module _
  {l1 l2 : Level}
  (x : lower-ℝ l1)
  (y : lower-ℝ l2)
  where

  cut-binary-min-lower-ℝ : subtype (l1 ⊔ l2) ℚ
  cut-binary-min-lower-ℝ = intersection-subtype (cut-lower-ℝ x) (cut-lower-ℝ y)

  min-inhabitants-in-binary-min-lower-ℝ :
    (p q : ℚ) → (is-in-cut-lower-ℝ x p) → (is-in-cut-lower-ℝ y q) →
    is-in-subtype cut-binary-min-lower-ℝ (min-ℚ p q)
  min-inhabitants-in-binary-min-lower-ℝ p q p<x q<y =
    is-in-cut-leq-ℚ-lower-ℝ x (min-ℚ p q) p (leq-left-min-ℚ p q) p<x ,
        is-in-cut-leq-ℚ-lower-ℝ y (min-ℚ p q) q (leq-right-min-ℚ p q) q<y

  is-inhabited-cut-binary-min-lower-ℝ : exists ℚ cut-binary-min-lower-ℝ
  is-inhabited-cut-binary-min-lower-ℝ =
    map-binary-exists
      ( is-in-subtype cut-binary-min-lower-ℝ)
      ( min-ℚ)
      ( min-inhabitants-in-binary-min-lower-ℝ)
      ( is-inhabited-cut-lower-ℝ x)
      ( is-inhabited-cut-lower-ℝ y)

  is-rounded-cut-binary-min-lower-ℝ :
    (q : ℚ) →
    is-in-subtype cut-binary-min-lower-ℝ q ↔
    exists ℚ (λ r → le-ℚ-Prop q r ∧ cut-binary-min-lower-ℝ r)
  pr1 (is-rounded-cut-binary-min-lower-ℝ q) (q<x , q<y) =
    map-binary-exists
      ( λ r → le-ℚ q r × is-in-subtype cut-binary-min-lower-ℝ r)
      ( min-ℚ)
      ( λ rx ry (q<rx , rx<x) (q<ry , ry<y) →
        le-min-le-both-ℚ q rx ry q<rx q<ry ,
        min-inhabitants-in-binary-min-lower-ℝ rx ry rx<x ry<y)
      ( forward-implication (is-rounded-cut-lower-ℝ x q) q<x)
      ( forward-implication (is-rounded-cut-lower-ℝ y q) q<y)
  pr2 (is-rounded-cut-binary-min-lower-ℝ q) =
    elim-exists
      ( cut-binary-min-lower-ℝ q)
      ( λ r (q<r , q<x , q<y) →
        backward-implication
          ( is-rounded-cut-lower-ℝ x q)
          ( intro-exists r (q<r , q<x)) ,
        backward-implication
          ( is-rounded-cut-lower-ℝ y q)
          ( intro-exists r (q<r , q<y)))

  binary-min-lower-ℝ : lower-ℝ (l1 ⊔ l2)
  pr1 binary-min-lower-ℝ = cut-binary-min-lower-ℝ
  pr1 (pr2 binary-min-lower-ℝ) = is-inhabited-cut-binary-min-lower-ℝ
  pr2 (pr2 binary-min-lower-ℝ) = is-rounded-cut-binary-min-lower-ℝ
```

## Properties

### The binary minimum is a greatest lower bound

```agda
  is-greatest-binary-lower-bound-binary-min-lower-ℝ :
    is-greatest-binary-lower-bound-Large-Poset
      lower-ℝ-Large-Poset
      x
      y
      binary-min-lower-ℝ
  is-greatest-binary-lower-bound-binary-min-lower-ℝ z =
    is-greatest-binary-lower-bound-intersection-subtype
      ( cut-lower-ℝ x)
      ( cut-lower-ℝ y)
      ( cut-lower-ℝ z)
```

### The lower Dedekind reals form a large meet-semilattice

```agda
has-meets-lower-ℝ : has-meets-Large-Poset lower-ℝ-Large-Poset
meet-has-meets-Large-Poset has-meets-lower-ℝ = binary-min-lower-ℝ
is-greatest-binary-lower-bound-meet-has-meets-Large-Poset has-meets-lower-ℝ =
  is-greatest-binary-lower-bound-binary-min-lower-ℝ

is-large-meet-semilattice-lower-ℝ :
  is-large-meet-semilattice-Large-Poset lower-ℝ-Large-Poset
has-meets-is-large-meet-semilattice-Large-Poset
  is-large-meet-semilattice-lower-ℝ = has-meets-lower-ℝ
has-top-element-is-large-meet-semilattice-Large-Poset
  is-large-meet-semilattice-lower-ℝ = has-top-element-lower-ℝ

lower-ℝ-Large-Meet-Semilattice : Large-Meet-Semilattice lsuc _⊔_
large-poset-Large-Meet-Semilattice lower-ℝ-Large-Meet-Semilattice =
  lower-ℝ-Large-Poset
is-large-meet-semilattice-Large-Meet-Semilattice
  lower-ℝ-Large-Meet-Semilattice = is-large-meet-semilattice-lower-ℝ
```
