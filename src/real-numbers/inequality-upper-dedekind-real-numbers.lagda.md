# Inequality on the upper Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.inequality-upper-dedekind-real-numbers where
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
open import foundation.powersets
open import foundation.propositions
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import order-theory.bottom-elements-large-posets
open import order-theory.large-posets
open import order-theory.large-preorders

open import real-numbers.rational-upper-dedekind-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

The
{{#concept "standard ordering" Disambiguation="upper Dedekind real numbers" Agda=leq-upper-ℝ}}
on the [upper real numbers](real-numbers.upper-dedekind-real-numbers.md) is
defined as the cut of the second being a subset of the cut of the first.

## Definition

```agda
module _
  {l1 l2 : Level}
  (x : upper-ℝ l1)
  (y : upper-ℝ l2)
  where

  leq-upper-ℝ-Prop : Prop (l1 ⊔ l2)
  leq-upper-ℝ-Prop = leq-prop-subtype (cut-upper-ℝ y) (cut-upper-ℝ x)

  leq-upper-ℝ : UU (l1 ⊔ l2)
  leq-upper-ℝ = type-Prop leq-upper-ℝ-Prop
```

## Properties

### Inequality on upper Dedekind reals is a large poset

```agda
upper-ℝ-Large-Preorder : Large-Preorder lsuc _⊔_
type-Large-Preorder upper-ℝ-Large-Preorder = upper-ℝ
leq-prop-Large-Preorder upper-ℝ-Large-Preorder = leq-upper-ℝ-Prop
refl-leq-Large-Preorder upper-ℝ-Large-Preorder x =
  refl-leq-subtype (cut-upper-ℝ x)
transitive-leq-Large-Preorder upper-ℝ-Large-Preorder x y z y≤z x≤y =
  transitive-leq-subtype (cut-upper-ℝ z) (cut-upper-ℝ y) (cut-upper-ℝ x) x≤y y≤z

upper-ℝ-Large-Poset : Large-Poset lsuc _⊔_
large-preorder-Large-Poset upper-ℝ-Large-Poset = upper-ℝ-Large-Preorder
antisymmetric-leq-Large-Poset upper-ℝ-Large-Poset x y x≤y y≤x =
  eq-eq-cut-upper-ℝ
    ( x)
    ( y)
    ( antisymmetric-leq-subtype (cut-upper-ℝ x) (cut-upper-ℝ y) y≤x x≤y)
```

### If a rational is in an upper Dedekind cut, the corresponding upper real is less than or equal to the rational's projection

```agda
module _
  {l : Level}
  (x : upper-ℝ l)
  (q : ℚ)
  where

  leq-is-in-cut-upper-real-ℚ :
    is-in-cut-upper-ℝ x q → leq-upper-ℝ x (upper-real-ℚ q)
  leq-is-in-cut-upper-real-ℚ q∈L p x<p =
    backward-implication
      ( is-rounded-cut-upper-ℝ x p)
      ( intro-exists q (x<p , q∈L))
```

### The canonical map from the rational numbers to the upper reals preserves inequality

```agda
preserves-leq-upper-real-ℚ :
  (p q : ℚ) → leq-ℚ p q → leq-upper-ℝ (upper-real-ℚ p) (upper-real-ℚ q)
preserves-leq-upper-real-ℚ p q p≤q r = concatenate-leq-le-ℚ p q r p≤q

reflects-leq-upper-real-ℚ :
  (p q : ℚ) → leq-upper-ℝ (upper-real-ℚ p) (upper-real-ℚ q) → leq-ℚ p q
reflects-leq-upper-real-ℚ p q q<r→p<r with decide-le-leq-ℚ q p
... | inr p≤q = p≤q
... | inl q<p = ex-falso (irreflexive-le-ℚ p (q<r→p<r p q<p))

iff-leq-upper-real-ℚ :
  (p q : ℚ) → leq-ℚ p q ↔ leq-upper-ℝ (upper-real-ℚ p) (upper-real-ℚ q)
pr1 (iff-leq-upper-real-ℚ p q) = preserves-leq-upper-real-ℚ p q
pr2 (iff-leq-upper-real-ℚ p q) = reflects-leq-upper-real-ℚ p q
```

### Negative infinity is the bottom element of the large poset of upper reals

```agda
is-bottom-element-neg-∞-upper-ℝ :
  is-bottom-element-Large-Poset upper-ℝ-Large-Poset neg-∞-upper-ℝ
is-bottom-element-neg-∞-upper-ℝ x q _ = star

has-bottom-element-upper-ℝ :
  has-bottom-element-Large-Poset upper-ℝ-Large-Poset
bottom-has-bottom-element-Large-Poset has-bottom-element-upper-ℝ = neg-∞-upper-ℝ
is-bottom-element-bottom-has-bottom-element-Large-Poset
  has-bottom-element-upper-ℝ = is-bottom-element-neg-∞-upper-ℝ
```
