# Maximal structured natural numbers

```agda
module elementary-number-theory.maximal-structured-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.lower-bounds-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.upper-bounds-natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

Consider a type family $P$ over $\mathbb{N}$. A
{{#concept "maximal structured natural number" Agda=maximal-element-ℕ}} in $P$
is a natural number $n$ equipped with an element $p : P(n)$ such that $n$ is an
[upper bound](elementary-number-theory.upper-bounds-natural-numbers.md) for $P$.

Forthermore, a
{{#concept "bounded maximal structured natural number" Agda=bounded-maximal-element-ℕ}}
in $P$ with bound $b$ is a natural number $n \leq b$ equipped with an element
$p : P(n)$ such that $n$ is an upper bound of for the type family
$x \mapsto (x \leq b) × P(x)$.

## Definitions

### The predicate of being a maximal structured natural number

```agda
is-maximal-element-ℕ :
  {l : Level} (P : ℕ → UU l) → ℕ → UU l
is-maximal-element-ℕ P n =
  P n × is-upper-bound-ℕ P n
```

### Maximal elements

```agda
maximal-element-ℕ :
  {l : Level} (P : ℕ → UU l) → UU l
maximal-element-ℕ P =
  Σ ℕ (is-maximal-element-ℕ P)

module _
  {l : Level} (P : ℕ → UU l) (n : maximal-element-ℕ P)
  where

  nat-maximal-element-ℕ : ℕ
  nat-maximal-element-ℕ = pr1 n

  structure-maximal-element-ℕ : P nat-maximal-element-ℕ
  structure-maximal-element-ℕ = pr1 (pr2 n)

  is-upper-bound-maximal-element-ℕ : is-upper-bound-ℕ P nat-maximal-element-ℕ
  is-upper-bound-maximal-element-ℕ = pr2 (pr2 n)

  is-least-upper-bound-maximal-element-ℕ :
    is-least-upper-bound-ℕ P nat-maximal-element-ℕ
  is-least-upper-bound-maximal-element-ℕ =
    is-least-upper-bound-is-upper-bound-ℕ P
      ( nat-maximal-element-ℕ)
      ( structure-maximal-element-ℕ)
      ( is-upper-bound-maximal-element-ℕ)
```

### The predicate of being a maximal bounded structured natural number

```agda
bounded-family-family-ℕ :
  {l : Level} (P : ℕ → UU l) → ℕ → ℕ → UU l
bounded-family-family-ℕ P b n = n ≤-ℕ b × P n

is-maximal-bounded-element-ℕ :
  {l : Level} (P : ℕ → UU l) → ℕ → ℕ → UU l
is-maximal-bounded-element-ℕ P b =
  is-maximal-element-ℕ (bounded-family-family-ℕ P b)
```

### Bounded maximal elements

```agda
bounded-maximal-element-ℕ :
  {l : Level} (P : ℕ → UU l) (b : ℕ) → UU l
bounded-maximal-element-ℕ P b =
  maximal-element-ℕ (bounded-family-family-ℕ P b)

module _
  {l : Level} (P : ℕ → UU l) (b : ℕ) (n : bounded-maximal-element-ℕ P b)
  where

  nat-bounded-maximal-element-ℕ : ℕ
  nat-bounded-maximal-element-ℕ = pr1 n

  upper-bound-bounded-maximal-element-ℕ : nat-bounded-maximal-element-ℕ ≤-ℕ b
  upper-bound-bounded-maximal-element-ℕ = pr1 (pr1 (pr2 n))

  structure-bounded-maximal-element-ℕ : P nat-bounded-maximal-element-ℕ
  structure-bounded-maximal-element-ℕ = pr2 (pr1 (pr2 n))

  is-upper-bound-bounded-maximal-element-ℕ :
    is-upper-bound-ℕ (bounded-family-family-ℕ P b) nat-bounded-maximal-element-ℕ
  is-upper-bound-bounded-maximal-element-ℕ = pr2 (pr2 n)

  is-least-upper-bound-bounded-maximal-element-ℕ :
    is-least-upper-bound-ℕ
      ( bounded-family-family-ℕ P b)
      ( nat-bounded-maximal-element-ℕ)
  is-least-upper-bound-bounded-maximal-element-ℕ =
    is-least-upper-bound-is-upper-bound-ℕ
      ( bounded-family-family-ℕ P b)
      ( nat-bounded-maximal-element-ℕ)
      ( upper-bound-bounded-maximal-element-ℕ ,
        structure-bounded-maximal-element-ℕ)
      ( is-upper-bound-bounded-maximal-element-ℕ)
```

## Properties

### The type of maximal elements of a subtype has at most one element

```agda
module _
  {l1 : Level} (P : ℕ → Prop l1)
  where

  all-elements-equal-maximal-element-ℕ :
    all-elements-equal (maximal-element-ℕ (λ n → type-Prop (P n)))
  all-elements-equal-maximal-element-ℕ
    (x , p , l) (y , q , k) =
    eq-type-subtype
      ( λ n →
        product-Prop
          ( _  , is-prop-type-Prop (P n))
          ( is-upper-bound-ℕ-Prop (type-Prop ∘ P) n))
      ( antisymmetric-leq-ℕ x y (k x p) (l y q))

  is-prop-maximal-element-ℕ :
    is-prop (maximal-element-ℕ (λ n → type-Prop (P n)))
  is-prop-maximal-element-ℕ =
    is-prop-all-elements-equal all-elements-equal-maximal-element-ℕ

  maximal-element-ℕ-Prop : Prop l1
  pr1 maximal-element-ℕ-Prop = maximal-element-ℕ (λ n → type-Prop (P n))
  pr2 maximal-element-ℕ-Prop = is-prop-maximal-element-ℕ
```

### A natural number is a largest lower bound if and only if it is a maximal element of the type of lower bounds

```agda
module _
  {l : Level} (P : ℕ → UU l) (n : ℕ)
  where

  is-maximal-lower-bound-is-largest-lower-bound-ℕ :
    is-largest-lower-bound-ℕ P n → is-maximal-element-ℕ (is-lower-bound-ℕ P) n
  pr1 (is-maximal-lower-bound-is-largest-lower-bound-ℕ H) =
    is-lower-bound-is-largest-lower-bound-ℕ P n H
  pr2 (is-maximal-lower-bound-is-largest-lower-bound-ℕ H) m K =
    leq-is-largest-lower-bound-ℕ P n H m K

  is-largest-lower-bound-is-maximal-lower-bound-ℕ :
    is-maximal-element-ℕ (is-lower-bound-ℕ P) n → is-largest-lower-bound-ℕ P n
  pr1 (is-largest-lower-bound-is-maximal-lower-bound-ℕ H m) K =
    pr2 H m K
  pr2 (is-largest-lower-bound-is-maximal-lower-bound-ℕ H m) K x p =
    transitive-leq-ℕ m n x (pr1 H x p) K
```
