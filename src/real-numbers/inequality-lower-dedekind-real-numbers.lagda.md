# Inequality on the lower Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.inequality-lower-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.powersets
open import foundation.propositions
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.top-elements-large-posets

open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.rational-lower-dedekind-real-numbers
```

</details>

## Idea

The
{{#concept "standard ordering" Disambiguation="lower Dedekind real numbers" Agda=leq-lower-ℝ}}
on the [lower real numbers](real-numbers.lower-dedekind-real-numbers.md) is
defined as the cut of one being a subset of the cut of the other.

## Definition

```agda
module _
  {l1 l2 : Level}
  (x : lower-ℝ l1)
  (y : lower-ℝ l2)
  where

  leq-lower-ℝ-Prop : Prop (l1 ⊔ l2)
  leq-lower-ℝ-Prop = leq-prop-subtype (cut-lower-ℝ x) (cut-lower-ℝ y)

  leq-lower-ℝ : UU (l1 ⊔ l2)
  leq-lower-ℝ = type-Prop leq-lower-ℝ-Prop
```

## Properties

### Inequality on lower Dedekind reals is a large poset

```agda
lower-ℝ-Large-Preorder : Large-Preorder lsuc _⊔_
type-Large-Preorder lower-ℝ-Large-Preorder = lower-ℝ
leq-prop-Large-Preorder lower-ℝ-Large-Preorder = leq-lower-ℝ-Prop
refl-leq-Large-Preorder lower-ℝ-Large-Preorder x =
  refl-leq-subtype (cut-lower-ℝ x)
transitive-leq-Large-Preorder lower-ℝ-Large-Preorder x y z =
  transitive-leq-subtype (cut-lower-ℝ x) (cut-lower-ℝ y) (cut-lower-ℝ z)

lower-ℝ-Large-Poset : Large-Poset lsuc _⊔_
large-preorder-Large-Poset lower-ℝ-Large-Poset = lower-ℝ-Large-Preorder
antisymmetric-leq-Large-Poset lower-ℝ-Large-Poset x y x≤y y≤x =
  eq-eq-cut-lower-ℝ
    ( x)
    ( y)
    ( antisymmetric-leq-subtype (cut-lower-ℝ x) (cut-lower-ℝ y) x≤y y≤x)
```

### If a rational is in a lower Dedekind cut, its projections is less than or equal to the corresponding lower real

```agda
module _
  {l : Level}
  (x : lower-ℝ l)
  (q : ℚ)
  where

  leq-is-in-cut-lower-real-ℚ :
    is-in-cut-lower-ℝ x q → leq-lower-ℝ (lower-real-ℚ q) x
  leq-is-in-cut-lower-real-ℚ q∈L p p<q =
    backward-implication
      ( is-rounded-cut-lower-ℝ x p)
      ( intro-exists q (p<q , q∈L))
```

### The canonical map from the rational numbers to the lower reals preserves inequality

```agda
preserves-leq-lower-real-ℚ :
  (p q : ℚ) → leq-ℚ p q → leq-lower-ℝ (lower-real-ℚ p) (lower-real-ℚ q)
preserves-leq-lower-real-ℚ p q p≤q r r<p = concatenate-le-leq-ℚ r p q r<p p≤q

reflects-leq-lower-real-ℚ :
  (p q : ℚ) → leq-lower-ℝ (lower-real-ℚ p) (lower-real-ℚ q) → leq-ℚ p q
reflects-leq-lower-real-ℚ p q r<p→r<q with decide-le-leq-ℚ q p
... | inr p≤q = p≤q
... | inl q<p = ex-falso (irreflexive-le-ℚ q (r<p→r<q q q<p))

iff-leq-lower-real-ℚ :
  (p q : ℚ) → leq-ℚ p q ↔ leq-lower-ℝ (lower-real-ℚ p) (lower-real-ℚ q)
pr1 (iff-leq-lower-real-ℚ p q) = preserves-leq-lower-real-ℚ p q
pr2 (iff-leq-lower-real-ℚ p q) = reflects-leq-lower-real-ℚ p q
```

### Infinity is the top element of the large poset of lower reals

```agda
is-top-element-∞-lower-ℝ :
  is-top-element-Large-Poset lower-ℝ-Large-Poset ∞-lower-ℝ
is-top-element-∞-lower-ℝ x q _ = star

has-top-element-lower-ℝ :
  has-top-element-Large-Poset lower-ℝ-Large-Poset
top-has-top-element-Large-Poset has-top-element-lower-ℝ = ∞-lower-ℝ
is-top-element-top-has-top-element-Large-Poset has-top-element-lower-ℝ =
  is-top-element-∞-lower-ℝ
```
