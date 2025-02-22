# Minimal structured natural numbers

```agda
module elementary-number-theory.minimal-structured-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.lower-bounds-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.upper-bounds-natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Consider a type family $P$ over $\mathbb{N}$. A
{{#concept "minimal structured natural number" Agda=minimal-element-ℕ}} in $P$
is a natural number $n$ equipped with an element $p : P(n)$ such that $n$ is a
[lower bound](elementary-number-theory.lower-bounds-natural-numbers.md) for $P$.

## Definitions

### The predicate of being a minimal structured natural number

```agda
is-minimal-element-ℕ :
  {l : Level} (P : ℕ → UU l) → ℕ → UU l
is-minimal-element-ℕ P n = P n × is-lower-bound-ℕ P n
```

### Minimal elements

```agda
minimal-element-ℕ :
  {l : Level} (P : ℕ → UU l) → UU l
minimal-element-ℕ P = Σ ℕ (is-minimal-element-ℕ P)

module _
  {l : Level} (P : ℕ → UU l) (n : minimal-element-ℕ P)
  where

  nat-minimal-element-ℕ : ℕ
  nat-minimal-element-ℕ = pr1 n

  structure-minimal-element-ℕ : P nat-minimal-element-ℕ
  structure-minimal-element-ℕ = pr1 (pr2 n)

  is-lower-bound-minimal-element-ℕ : is-lower-bound-ℕ P nat-minimal-element-ℕ
  is-lower-bound-minimal-element-ℕ = pr2 (pr2 n)

  is-largest-lower-bound-minimal-element-ℕ :
    is-largest-lower-bound-ℕ P nat-minimal-element-ℕ
  is-largest-lower-bound-minimal-element-ℕ =
    is-largest-lower-bound-is-lower-bound-ℕ P
      ( nat-minimal-element-ℕ)
      ( structure-minimal-element-ℕ)
      ( is-lower-bound-minimal-element-ℕ)
```

## Properties

### The type of minimal elements of a subtype has at most one element

```agda
module _
  {l1 : Level} (P : ℕ → Prop l1)
  where

  all-elements-equal-minimal-element-ℕ :
    all-elements-equal (minimal-element-ℕ (λ n → type-Prop (P n)))
  all-elements-equal-minimal-element-ℕ
    (x , p , l) (y , q , k) =
    eq-type-subtype
      ( λ n →
        product-Prop
          ( _  , is-prop-type-Prop (P n))
          ( is-lower-bound-ℕ-Prop (type-Prop ∘ P) n))
      ( antisymmetric-leq-ℕ x y (l y q) (k x p))

  is-prop-minimal-element-ℕ :
    is-prop (minimal-element-ℕ (λ n → type-Prop (P n)))
  is-prop-minimal-element-ℕ =
    is-prop-all-elements-equal all-elements-equal-minimal-element-ℕ

  minimal-element-ℕ-Prop : Prop l1
  pr1 minimal-element-ℕ-Prop = minimal-element-ℕ (λ n → type-Prop (P n))
  pr2 minimal-element-ℕ-Prop = is-prop-minimal-element-ℕ
```

### Shifting minimal elements

If $P(0)$ is a decidable type, then we can obtain a minimal structured element
of $P$ from a minimal structured element of $n\mapsto P(n+1)$.

```agda
module _
  {l : Level} (P : ℕ → UU l)
  where

  shift-minimal-element-ℕ :
    is-decidable (P 0) → minimal-element-ℕ (P ∘ succ-ℕ) → minimal-element-ℕ P
  shift-minimal-element-ℕ (inl p) m =
    ( 0 , p , λ x _ → leq-zero-ℕ x)
  pr1 (shift-minimal-element-ℕ (inr f) m) =
    succ-ℕ (nat-minimal-element-ℕ (P ∘ succ-ℕ) m)
  pr1 (pr2 (shift-minimal-element-ℕ (inr f) m)) =
    structure-minimal-element-ℕ (P ∘ succ-ℕ) m
  pr2 (pr2 (shift-minimal-element-ℕ (inr f) m)) zero-ℕ p =
    ex-falso (f p)
  pr2 (pr2 (shift-minimal-element-ℕ (inr f) m)) (succ-ℕ x) p =
    is-lower-bound-minimal-element-ℕ (P ∘ succ-ℕ) m x p
```

### A natural number is a least upper bound if and only if it is a minimal element of the type of upper bounds

```agda
module _
  {l : Level} (P : ℕ → UU l) (n : ℕ)
  where

  is-minimal-upper-bound-is-least-upper-bound-ℕ :
    is-least-upper-bound-ℕ P n → is-minimal-element-ℕ (is-upper-bound-ℕ P) n
  pr1 (is-minimal-upper-bound-is-least-upper-bound-ℕ H) =
    is-upper-bound-is-least-upper-bound-ℕ P n H
  pr2 (is-minimal-upper-bound-is-least-upper-bound-ℕ H) m K =
    leq-is-least-upper-bound-ℕ P n H m K

  is-least-upper-bound-is-minimal-upper-bound-ℕ :
    is-minimal-element-ℕ (is-upper-bound-ℕ P) n → is-least-upper-bound-ℕ P n
  pr1 (is-least-upper-bound-is-minimal-upper-bound-ℕ H m) K =
    pr2 H m K
  pr2 (is-least-upper-bound-is-minimal-upper-bound-ℕ H m) K x p =
    transitive-leq-ℕ x n m K (pr1 H x p)
```
