# The minimum of upper Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.minimum-upper-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.inhabited-types
open import foundation.logical-equivalences
open import foundation.powersets
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.unions-subtypes
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-inflattices
open import order-theory.lower-bounds-large-posets

open import real-numbers.inequality-upper-dedekind-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

The minimum of two
[upper Dedekind real numbers](real-numbers.upper-dedekind-real-numbers.md) `x`,
`y` is a upper Dedekind real number with cut equal to the union of the cuts of
`x` and `y`. Unlike the case for the
[minimum of upper Dedekind real numbers](real-numbers.minimum-upper-dedekind-real-numbers.md),
the minimum of any inhabited family of upper Dedekind real numbers, the upper
Dedekind real number by taking the union of the cuts of every element of the
family, is also a upper Dedekind real number.

## Definition

### Binary minimum

```agda
module _
  {l1 l2 : Level}
  (x : upper-ℝ l1)
  (y : upper-ℝ l2)
  where

  cut-binary-min-upper-ℝ : subtype (l1 ⊔ l2) ℚ
  cut-binary-min-upper-ℝ = union-subtype (cut-upper-ℝ x) (cut-upper-ℝ y)

  is-inhabited-cut-binary-min-upper-ℝ : exists ℚ cut-binary-min-upper-ℝ
  is-inhabited-cut-binary-min-upper-ℝ =
    map-tot-exists
      ( λ _ → inl-disjunction)
      ( is-inhabited-cut-upper-ℝ x)

  is-rounded-cut-binary-min-upper-ℝ :
    (q : ℚ) →
    is-in-subtype cut-binary-min-upper-ℝ q ↔
    exists ℚ (λ p → le-ℚ-Prop p q ∧ cut-binary-min-upper-ℝ p)
  pr1 (is-rounded-cut-binary-min-upper-ℝ q) =
    elim-disjunction
      ( ∃ ℚ (λ p → le-ℚ-Prop p q ∧ cut-binary-min-upper-ℝ p))
      ( λ q<x →
        map-tot-exists
          ( λ _ → map-product id inl-disjunction)
          ( forward-implication (is-rounded-cut-upper-ℝ x q) q<x))
      ( λ q<y →
        map-tot-exists
          ( λ _ → map-product id inr-disjunction)
          ( forward-implication (is-rounded-cut-upper-ℝ y q) q<y))
  pr2 (is-rounded-cut-binary-min-upper-ℝ q) =
    elim-exists
      ( cut-binary-min-upper-ℝ q)
      ( λ r (q<r , r<min) →
        elim-disjunction
          ( cut-binary-min-upper-ℝ q)
          ( λ r<x →
            inl-disjunction
              ( backward-implication
                ( is-rounded-cut-upper-ℝ x q)
                ( intro-exists r (q<r , r<x))))
          ( λ r<y →
            inr-disjunction
              ( backward-implication
                ( is-rounded-cut-upper-ℝ y q)
                ( intro-exists r (q<r , r<y))))
          ( r<min))

  binary-min-upper-ℝ : upper-ℝ (l1 ⊔ l2)
  pr1 binary-min-upper-ℝ = cut-binary-min-upper-ℝ
  pr1 (pr2 binary-min-upper-ℝ) = is-inhabited-cut-binary-min-upper-ℝ
  pr2 (pr2 binary-min-upper-ℝ) = is-rounded-cut-binary-min-upper-ℝ
```

### Minimum of an inhabited family of upper reals

```agda
module _
  {l1 l2 : Level}
  (A : UU l1)
  (H : is-inhabited A)
  (F : A → upper-ℝ l2)
  where

  cut-min-upper-ℝ : subtype (l1 ⊔ l2) ℚ
  cut-min-upper-ℝ = union-family-of-subtypes (cut-upper-ℝ ∘ F)

  is-inhabited-cut-min-upper-ℝ : exists ℚ cut-min-upper-ℝ
  is-inhabited-cut-min-upper-ℝ =
    rec-trunc-Prop
      ( ∃ ℚ cut-min-upper-ℝ)
      ( λ a →
        map-tot-exists
          ( λ q q∈Fa → intro-exists a q∈Fa)
          ( is-inhabited-cut-upper-ℝ (F a)))
      ( H)

  is-rounded-cut-min-upper-ℝ :
    (q : ℚ) →
    is-in-subtype cut-min-upper-ℝ q ↔
    exists ℚ (λ p → le-ℚ-Prop p q ∧ cut-min-upper-ℝ p)
  pr1 (is-rounded-cut-min-upper-ℝ q) =
    elim-exists
      ( ∃ ℚ (λ p → le-ℚ-Prop p q ∧ cut-min-upper-ℝ p))
      ( λ a q∈Fa →
        elim-exists
          ( ∃ ℚ (λ p → le-ℚ-Prop p q ∧ cut-min-upper-ℝ p))
          ( λ p (p<q , r∈Fa) → intro-exists p (p<q , intro-exists a r∈Fa))
          ( forward-implication (is-rounded-cut-upper-ℝ (F a) q) q∈Fa))
  pr2 (is-rounded-cut-min-upper-ℝ q) =
    elim-exists
      ( cut-min-upper-ℝ q)
      ( λ r (q<r , r∈min) →
        elim-exists
          ( cut-min-upper-ℝ q)
          ( λ a r∈Fa →
            intro-exists
              ( a)
              ( backward-implication
                ( is-rounded-cut-upper-ℝ (F a) q)
                ( intro-exists r (q<r , r∈Fa))))
          ( r∈min))

  min-upper-ℝ : upper-ℝ (l1 ⊔ l2)
  pr1 min-upper-ℝ = cut-min-upper-ℝ
  pr1 (pr2 min-upper-ℝ) = is-inhabited-cut-min-upper-ℝ
  pr2 (pr2 min-upper-ℝ) = is-rounded-cut-min-upper-ℝ
```

## Properties

### The minimum of two upper reals is a greatest lower bound

```agda
module _
  {l1 l2 : Level}
  (x : upper-ℝ l1)
  (y : upper-ℝ l2)
  where

  is-greatest-binary-lower-bound-binary-min-upper-ℝ :
    is-greatest-binary-lower-bound-Large-Poset
      ( upper-ℝ-Large-Poset)
      ( x)
      ( y)
      ( binary-min-upper-ℝ x y)
  pr1 (is-greatest-binary-lower-bound-binary-min-upper-ℝ z) (z≤x , z≤y) p =
    elim-disjunction (cut-upper-ℝ z p) (z≤x p) (z≤y p)
  pr1 (pr2 (is-greatest-binary-lower-bound-binary-min-upper-ℝ z) z≤min) p x<p =
    z≤min p (inl-disjunction x<p)
  pr2 (pr2 (is-greatest-binary-lower-bound-binary-min-upper-ℝ z) z≤min) p y<p =
    z≤min p (inr-disjunction y<p)
```

### The minimum of two upper reals is a lower bound

```agda
  is-binary-lower-bound-binary-min-upper-ℝ :
    is-binary-lower-bound-Large-Poset
      ( upper-ℝ-Large-Poset)
      ( x)
      ( y)
      ( binary-min-upper-ℝ x y)
  is-binary-lower-bound-binary-min-upper-ℝ =
    is-binary-lower-bound-is-greatest-binary-lower-bound-Large-Poset
      upper-ℝ-Large-Poset
      x
      y
      is-greatest-binary-lower-bound-binary-min-upper-ℝ
```
