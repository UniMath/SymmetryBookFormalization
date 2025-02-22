# Inflationary functions on the natural numbers

```agda
module
  elementary-number-theory.inflationary-functions-natural-numbers
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.universe-levels

open import order-theory.inflationary-maps-posets
```

</details>

## Idea

A function $f : \mathbb{N} \to \mathbb{N}$ is an
{{#concept "inflationary function" Disambiguation="natural numbers" Agda=is-inflationary-ℕ}}
if the implication

$$
  (x \leq y) \to (f(x) \leq f(y))
$$

holds for every $x,y:\mathbb{N}$. If $f$ is an inflationary function on the
natural numbers such that $f(0) \leq b$ for some natural number $b$, then there
is a maximal natural number $k$ such that $f(k) \leq b$.

## Definitions

### The predicate of being an inflationary map on the natural numbers

```agda
is-inflationary-ℕ : (ℕ → ℕ) → UU lzero
is-inflationary-ℕ =
  is-inflationary-map-Poset ℕ-Poset
```

### Inflationary maps on the natural numbers

```agda
inflationary-map-ℕ : UU lzero
inflationary-map-ℕ =
  inflationary-map-Poset ℕ-Poset

map-inflationary-map-ℕ :
  inflationary-map-ℕ → ℕ → ℕ
map-inflationary-map-ℕ =
  map-inflationary-map-Poset ℕ-Poset

is-inflationary-inflationary-map-ℕ :
  (f : inflationary-map-ℕ) →
  is-inflationary-ℕ (map-inflationary-map-ℕ f)
is-inflationary-inflationary-map-ℕ =
  is-inflationary-inflationary-map-Poset ℕ-Poset

fiber-inflationary-map-ℕ :
  (f : inflationary-map-ℕ) → ℕ → UU lzero
fiber-inflationary-map-ℕ f = fiber (map-inflationary-map-ℕ f)
```

## Properties

### Being a value of an inflationary map is decidable

```agda
is-decidable-fiber-inflationary-map-ℕ :
  (f : inflationary-map-ℕ) →
  is-decidable-fam (fiber-inflationary-map-ℕ f)
is-decidable-fiber-inflationary-map-ℕ = {!!}
```

### For any inflationary map $f$ with $f(0) \leq b$, there is a maximal number $k$ such that $f(k) \leq b$
