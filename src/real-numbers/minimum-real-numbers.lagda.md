# The minimum of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.minimum-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-meet-semilattices

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.minimum-lower-dedekind-real-numbers
open import real-numbers.minimum-upper-dedekind-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

The **binary minimum** of two
[Dedekind real numbers](real-numbers.dedekind-real-numbers.md) `x`, `y` is a
Dedekind real number with lower cut equal to the intersection of `x` and `y`'s
lower cuts, and upper cut equal to the union of their upper cuts.

## Definition

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  lower-real-binary-min-ℝ : lower-ℝ (l1 ⊔ l2)
  lower-real-binary-min-ℝ = binary-min-lower-ℝ (lower-real-ℝ x) (lower-real-ℝ y)

  upper-real-binary-min-ℝ : upper-ℝ (l1 ⊔ l2)
  upper-real-binary-min-ℝ = binary-min-upper-ℝ (upper-real-ℝ x) (upper-real-ℝ y)

  is-disjoint-lower-upper-binary-min-ℝ :
    is-disjoint-lower-upper-ℝ lower-real-binary-min-ℝ upper-real-binary-min-ℝ
  is-disjoint-lower-upper-binary-min-ℝ q ((q<x , q<y) , q∈U) =
    elim-disjunction
      ( empty-Prop)
      ( λ x<q → is-disjoint-cut-ℝ x q (q<x , x<q))
      ( λ y<q → is-disjoint-cut-ℝ y q (q<y , y<q))
      q∈U

  is-located-lower-upper-binary-min-ℝ :
    is-located-lower-upper-ℝ lower-real-binary-min-ℝ upper-real-binary-min-ℝ
  is-located-lower-upper-binary-min-ℝ p q p<q =
    elim-disjunction
      ( claim)
      ( λ p<x →
        elim-disjunction
          ( claim)
          (λ p<y → inl-disjunction (p<x , p<y))
          (λ y<q → inr-disjunction (inr-disjunction y<q))
          ( is-located-lower-upper-cut-ℝ y p q p<q))
      ( λ x<q → inr-disjunction (inl-disjunction x<q))
      ( is-located-lower-upper-cut-ℝ x p q p<q)
    where
      claim : Prop (l1 ⊔ l2)
      claim =
        cut-lower-ℝ lower-real-binary-min-ℝ p ∨
        cut-upper-ℝ upper-real-binary-min-ℝ q

  binary-min-ℝ : ℝ (l1 ⊔ l2)
  binary-min-ℝ =
    real-lower-upper-ℝ
      ( lower-real-binary-min-ℝ)
      ( upper-real-binary-min-ℝ)
      ( is-disjoint-lower-upper-binary-min-ℝ)
      ( is-located-lower-upper-binary-min-ℝ)
```

## Properties

### The binary minimum is a greatest lower bound

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  is-greatest-binary-lower-bound-binary-min-ℝ :
    is-greatest-binary-lower-bound-Large-Poset
      ( ℝ-Large-Poset)
      ( x)
      ( y)
      ( binary-min-ℝ x y)
  is-greatest-binary-lower-bound-binary-min-ℝ z =
    is-greatest-binary-lower-bound-binary-min-lower-ℝ
      ( lower-real-ℝ x)
      ( lower-real-ℝ y)
      ( lower-real-ℝ z)
```

### The large poset of the real numbers has meets

```agda
has-meets-ℝ-Large-Poset : has-meets-Large-Poset ℝ-Large-Poset
meet-has-meets-Large-Poset has-meets-ℝ-Large-Poset = binary-min-ℝ
is-greatest-binary-lower-bound-meet-has-meets-Large-Poset
  has-meets-ℝ-Large-Poset = is-greatest-binary-lower-bound-binary-min-ℝ
```
