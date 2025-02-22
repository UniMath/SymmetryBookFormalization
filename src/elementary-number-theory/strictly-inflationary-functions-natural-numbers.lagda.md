# Strictly inflationary functions on the natural numbers

```agda
module
  elementary-number-theory.strictly-inflationary-functions-natural-numbers
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-types
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.decidable-maps
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.identity-types
open import foundation.universe-levels

open import order-theory.strictly-inflationary-maps-strict-preorders

open import univalent-combinatorics.dependent-pair-types
```

</details>

## Idea

A function $f : \mathbb{N} \to \mathbb{N}$ is a
{{#concept "strictly inflationary function" Disambiguation="natural numbers" Agda=is-strictly-inflationary-ℕ}}
if the implication

$$
  (x < y) \to (f(x) < f(y))
$$

holds for every $x,y:\mathbb{N}$. If $f$ is a strictly inflationary function on
the natural numbers such that $f(0) \leq b$ for some natural number $b$, then
there is a maximal natural number $k$ such that $f(k) \leq b$.

## Definitions

### The predicate of being a strictly inflationary map on the natural numbers

```agda
is-strictly-inflationary-map-ℕ : (ℕ → ℕ) → UU lzero
is-strictly-inflationary-map-ℕ =
  is-strictly-inflationary-map-Strict-Preorder ℕ-Strict-Preorder
```

### Strictly inflationary maps on the natural numbers

```agda
strictly-inflationary-map-ℕ : UU lzero
strictly-inflationary-map-ℕ =
  strictly-inflationary-map-Strict-Preorder ℕ-Strict-Preorder

map-strictly-inflationary-map-ℕ :
  strictly-inflationary-map-ℕ → ℕ → ℕ
map-strictly-inflationary-map-ℕ =
  map-strictly-inflationary-map-Strict-Preorder ℕ-Strict-Preorder

is-strictly-inflationary-strictly-inflationary-map-ℕ :
  (f : strictly-inflationary-map-ℕ) →
  is-strictly-inflationary-map-ℕ (map-strictly-inflationary-map-ℕ f)
is-strictly-inflationary-strictly-inflationary-map-ℕ =
  is-strictly-inflationary-strictly-inflationary-map-Strict-Preorder
    ℕ-Strict-Preorder

fiber-strictly-inflationary-map-ℕ :
  (f : strictly-inflationary-map-ℕ) → ℕ → UU lzero
fiber-strictly-inflationary-map-ℕ f = fiber (map-strictly-inflationary-map-ℕ f)
```

## Properties

### Strictly inflationary maps on the natural numbers are inflationary

```agda
is-inflationary-strictly-inflationary-map-ℕ :
  (f : strictly-inflationary-map-ℕ)
  (n : ℕ) → n ≤-ℕ map-strictly-inflationary-map-ℕ f n
is-inflationary-strictly-inflationary-map-ℕ f n =
  leq-le-ℕ n
    ( map-strictly-inflationary-map-ℕ f n)
    ( is-strictly-inflationary-strictly-inflationary-map-ℕ f n)
```

### Strictly inflationary maps are decidable

```agda
is-decidable-map-is-strictly-inflationary-map-ℕ :
  {f : ℕ → ℕ} → is-strictly-inflationary-map-ℕ f → is-decidable-map f
is-decidable-map-is-strictly-inflationary-map-ℕ {f} H n =
  is-decidable-iff
    ( λ (x , K , p) → (x , p))
    ( λ (x , p) → (x , concatenate-le-eq-ℕ x (f x) n (H x) p , p))
    ( is-decidable-strictly-bounded-Σ-ℕ' n
      ( λ x → f x ＝ n)
      ( λ x → has-decidable-equality-ℕ (f x) n))

is-decidable-map-strictly-inflationary-map-ℕ :
  (f : strictly-inflationary-map-ℕ) →
  is-decidable-map (map-strictly-inflationary-map-ℕ f)
is-decidable-map-strictly-inflationary-map-ℕ (f , H) n =
  is-decidable-map-is-strictly-inflationary-map-ℕ H n
```
