# The maximum of lower Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.maximum-lower-dedekind-real-numbers where
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

open import order-theory.large-suplattices
open import order-theory.least-upper-bounds-large-posets
open import order-theory.upper-bounds-large-posets

open import real-numbers.inequality-lower-dedekind-real-numbers
open import real-numbers.lower-dedekind-real-numbers
```

</details>

## Idea

The maximum of two
[lower Dedekind real numbers](real-numbers.lower-dedekind-real-numbers.md) `x`,
`y` is a lower Dedekind real number with cut equal to the union of the cuts of
`x` and `y`. Unlike the case for the
[minimum of lower Dedekind real numbers](real-numbers.minimum-lower-dedekind-real-numbers.md),
the maximum of any inhabited family of lower Dedekind real numbers, the lower
Dedekind real number by taking the union of the cuts of every element of the
family, is also a lower Dedekind real number.

## Definition

### Binary maximum

```agda
module _
  {l1 l2 : Level}
  (x : lower-ℝ l1)
  (y : lower-ℝ l2)
  where

  cut-binary-max-lower-ℝ : subtype (l1 ⊔ l2) ℚ
  cut-binary-max-lower-ℝ = union-subtype (cut-lower-ℝ x) (cut-lower-ℝ y)

  is-inhabited-cut-binary-max-lower-ℝ : exists ℚ cut-binary-max-lower-ℝ
  is-inhabited-cut-binary-max-lower-ℝ =
    map-tot-exists
      ( λ _ → inl-disjunction)
      ( is-inhabited-cut-lower-ℝ x)

  is-rounded-cut-binary-max-lower-ℝ :
    (q : ℚ) →
    is-in-subtype cut-binary-max-lower-ℝ q ↔
    exists ℚ (λ r → le-ℚ-Prop q r ∧ cut-binary-max-lower-ℝ r)
  pr1 (is-rounded-cut-binary-max-lower-ℝ q) =
    elim-disjunction
      ( ∃ ℚ (λ r → le-ℚ-Prop q r ∧ cut-binary-max-lower-ℝ r))
      ( λ q<x →
        map-tot-exists
          ( λ _ → map-product id inl-disjunction)
          ( forward-implication (is-rounded-cut-lower-ℝ x q) q<x))
      ( λ q<y →
        map-tot-exists
          ( λ _ → map-product id inr-disjunction)
          ( forward-implication (is-rounded-cut-lower-ℝ y q) q<y))
  pr2 (is-rounded-cut-binary-max-lower-ℝ q) =
    elim-exists
      ( cut-binary-max-lower-ℝ q)
      ( λ r (q<r , r<max) →
        elim-disjunction
          ( cut-binary-max-lower-ℝ q)
          ( λ r<x →
            inl-disjunction
              ( backward-implication
                ( is-rounded-cut-lower-ℝ x q)
                ( intro-exists r (q<r , r<x))))
          ( λ r<y →
            inr-disjunction
              ( backward-implication
                ( is-rounded-cut-lower-ℝ y q)
                ( intro-exists r (q<r , r<y))))
          ( r<max))

  binary-max-lower-ℝ : lower-ℝ (l1 ⊔ l2)
  pr1 binary-max-lower-ℝ = cut-binary-max-lower-ℝ
  pr1 (pr2 binary-max-lower-ℝ) = is-inhabited-cut-binary-max-lower-ℝ
  pr2 (pr2 binary-max-lower-ℝ) = is-rounded-cut-binary-max-lower-ℝ
```

### Maximum of an inhabited family of lower reals

```agda
module _
  {l1 l2 : Level}
  (A : UU l1)
  (H : is-inhabited A)
  (F : A → lower-ℝ l2)
  where

  cut-max-lower-ℝ : subtype (l1 ⊔ l2) ℚ
  cut-max-lower-ℝ = union-family-of-subtypes (cut-lower-ℝ ∘ F)

  is-inhabited-cut-max-lower-ℝ : exists ℚ cut-max-lower-ℝ
  is-inhabited-cut-max-lower-ℝ =
    rec-trunc-Prop
      ( ∃ ℚ cut-max-lower-ℝ)
      ( λ a →
        map-tot-exists
          ( λ q q∈Fa → intro-exists a q∈Fa)
          ( is-inhabited-cut-lower-ℝ (F a)))
      ( H)

  is-rounded-cut-max-lower-ℝ :
    (q : ℚ) →
    is-in-subtype cut-max-lower-ℝ q ↔
    exists ℚ (λ r → le-ℚ-Prop q r ∧ cut-max-lower-ℝ r)
  pr1 (is-rounded-cut-max-lower-ℝ q) =
    elim-exists
      ( ∃ ℚ (λ r → le-ℚ-Prop q r ∧ cut-max-lower-ℝ r))
      ( λ a q∈Fa →
        elim-exists
          ( ∃ ℚ (λ r → le-ℚ-Prop q r ∧ cut-max-lower-ℝ r))
          ( λ r (q<r , r∈Fa) → intro-exists r (q<r , intro-exists a r∈Fa))
          ( forward-implication (is-rounded-cut-lower-ℝ (F a) q) q∈Fa))
  pr2 (is-rounded-cut-max-lower-ℝ q) =
    elim-exists
      ( cut-max-lower-ℝ q)
      ( λ r (q<r , r∈max) →
        elim-exists
          ( cut-max-lower-ℝ q)
          ( λ a r∈Fa →
            intro-exists
              ( a)
              ( backward-implication
                ( is-rounded-cut-lower-ℝ (F a) q)
                ( intro-exists r (q<r , r∈Fa))))
          ( r∈max))

  max-lower-ℝ : lower-ℝ (l1 ⊔ l2)
  pr1 max-lower-ℝ = cut-max-lower-ℝ
  pr1 (pr2 max-lower-ℝ) = is-inhabited-cut-max-lower-ℝ
  pr2 (pr2 max-lower-ℝ) = is-rounded-cut-max-lower-ℝ
```

## Properties

### The maximum of two lower reals is a least upper bound

```agda
module _
  {l1 l2 : Level}
  (x : lower-ℝ l1)
  (y : lower-ℝ l2)
  where

  is-least-binary-upper-bound-binary-max-lower-ℝ :
    is-least-binary-upper-bound-Large-Poset
      ( lower-ℝ-Large-Poset)
      ( x)
      ( y)
      ( binary-max-lower-ℝ x y)
  pr1 (is-least-binary-upper-bound-binary-max-lower-ℝ z) (x≤z , y≤z) p =
    elim-disjunction (cut-lower-ℝ z p) (x≤z p) (y≤z p)
  pr1 (pr2 (is-least-binary-upper-bound-binary-max-lower-ℝ z) max≤z) p p<x =
    max≤z p (inl-disjunction p<x)
  pr2 (pr2 (is-least-binary-upper-bound-binary-max-lower-ℝ z) max≤z) p p<y =
    max≤z p (inr-disjunction p<y)
```

### The maximum of two reals is an upper bound

```agda
  is-binary-upper-bound-binary-max-lower-ℝ :
    is-binary-upper-bound-Large-Poset
      ( lower-ℝ-Large-Poset)
      ( x)
      ( y)
      ( binary-max-lower-ℝ x y)
  is-binary-upper-bound-binary-max-lower-ℝ =
    is-binary-upper-bound-is-least-binary-upper-bound-Large-Poset
      lower-ℝ-Large-Poset
      x
      y
      is-least-binary-upper-bound-binary-max-lower-ℝ
```

### The maximum of an inhabited family of lower reals is a least upper bound

```agda
module _
  {l1 l2 : Level}
  (A : UU l1)
  (H : is-inhabited A)
  (F : A → lower-ℝ l2)
  where

  is-least-upper-bound-max-lower-ℝ :
    is-least-upper-bound-family-of-elements-Large-Poset
      lower-ℝ-Large-Poset
      F
      (max-lower-ℝ A H F)
  is-least-upper-bound-max-lower-ℝ z =
    is-least-upper-bound-sup-Large-Suplattice
      ( powerset-Large-Suplattice ℚ)
      ( cut-lower-ℝ ∘ F)
      ( cut-lower-ℝ z)
```
