# Lower bounds for structured natural numbers

```agda
module elementary-number-theory.lower-bounds-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-empty-type
open import foundation.universe-levels
```

</details>

## Idea

Consider a type family $P$ over the
[natural numbers](elementary-number-theory.natural-numbers.md). A
{{#concept "structured natural number"}} is simply a natural number $n$ equipped
with an element $P(n)$. In this file we consider various upper bounds for
structured natural numbers, and relations between them. This file builds the
prerequisite infrastructure for the
[well-ordering principle](elementary-number-theory.well-ordering-principle-natural-numbers.md)
of the natural numbers, and its direct consequences.

- A natural number $n$ is said to be a
  {{#concept "lower bound" Disambiguation="structured natural numbers" Agda=is-lower-bound-ℕ}}
  if there is a function from $P(x)$ to the type $n \leq x$ for all
  $x : \mathbb{N}$.
- A natural number $n$ is said to be a
  {{#concept "strict lower bound" Disambiguation="structured natural numbers" Agda=is-strict-lower-bound-ℕ}}
  if there is a function from $P(x)$ to the type $n < x$ for all
  $x : \mathbb{N}$.
- A natural number $n$ is said to be a
  {{#concept "largest lower bound" Disambiguation="structured natural numbers" Agda=is-largest-lower-bound-ℕ}}
  if any natural number $x$ is a lower bound if and only if $x \leq n$.
- A natural number $n$ is said to be a
  {{#concept "largest strict lower bound" Disambiguation="structured natural numbers" Agda=is-largest-strict-lower-bound-ℕ}}
  if any natural number $x$ is a strict lower bound if and only if $x \leq n$.

## Definitions

### Lower bounds

```agda
is-lower-bound-ℕ :
  {l : Level} (P : ℕ → UU l) → ℕ → UU l
is-lower-bound-ℕ P n =
  (m : ℕ) → P m → n ≤-ℕ m
```

### Strict lower bounds

```agda
is-strict-lower-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) → UU l
is-strict-lower-bound-ℕ P n =
  (m : ℕ) → P m → n <-ℕ m
```

### Largest lower bounds

```agda
is-largest-lower-bound-ℕ :
  {l : Level} (P : ℕ → UU l) → ℕ → UU l
is-largest-lower-bound-ℕ P n =
  (x : ℕ) → is-lower-bound-ℕ P x ↔ x ≤-ℕ n

is-lower-bound-is-largest-lower-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) →
  is-largest-lower-bound-ℕ P n → is-lower-bound-ℕ P n
is-lower-bound-is-largest-lower-bound-ℕ P n H =
  backward-implication (H n) (refl-leq-ℕ n)

leq-is-largest-lower-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) →
  is-largest-lower-bound-ℕ P n →
  (m : ℕ) → is-lower-bound-ℕ P m → m ≤-ℕ n
leq-is-largest-lower-bound-ℕ P n H m =
  forward-implication (H m)
```

### Largest strict lower bounds

```agda
is-largest-strict-lower-bound-ℕ :
  {l : Level} (P : ℕ → UU l) → ℕ → UU l
is-largest-strict-lower-bound-ℕ P n =
  (x : ℕ) → is-strict-lower-bound-ℕ P x ↔ x ≤-ℕ n
```

## Properties

### Being a lower bound is a property

```agda
module _
  {l : Level} (P : ℕ → UU l)
  where

  is-prop-is-lower-bound-ℕ :
    (n : ℕ) → is-prop (is-lower-bound-ℕ P n)
  is-prop-is-lower-bound-ℕ n =
    is-prop-Π (λ x → is-prop-function-type (is-prop-leq-ℕ n x))

  is-lower-bound-ℕ-Prop :
    (n : ℕ) → Prop l
  pr1 (is-lower-bound-ℕ-Prop n) = is-lower-bound-ℕ P n
  pr2 (is-lower-bound-ℕ-Prop n) = is-prop-is-lower-bound-ℕ n
```

### Being a strict lower bound is a property

```agda
module _
  {l : Level} (P : ℕ → UU l)
  where

  is-prop-is-strict-lower-bound-ℕ :
    (n : ℕ) → is-prop (is-strict-lower-bound-ℕ P n)
  is-prop-is-strict-lower-bound-ℕ n =
    is-prop-Π (λ x → is-prop-function-type (is-prop-le-ℕ n x))

  is-strict-lower-bound-ℕ-Prop :
    (n : ℕ) → Prop l
  pr1 (is-strict-lower-bound-ℕ-Prop n) = is-strict-lower-bound-ℕ P n
  pr2 (is-strict-lower-bound-ℕ-Prop n) = is-prop-is-strict-lower-bound-ℕ n
```

### Being a largest lower bound is a property

```agda
module _
  {l : Level} (P : ℕ → UU l)
  where

  is-prop-is-largest-lower-bound-ℕ :
    (n : ℕ) → is-prop (is-largest-lower-bound-ℕ P n)
  is-prop-is-largest-lower-bound-ℕ n =
    is-prop-Π
      ( λ x → is-prop-iff-Prop (is-lower-bound-ℕ-Prop P x) (leq-ℕ-Prop x n))

  is-largest-lower-bound-ℕ-Prop :
    (n : ℕ) → Prop l
  pr1 (is-largest-lower-bound-ℕ-Prop n) = is-largest-lower-bound-ℕ P n
  pr2 (is-largest-lower-bound-ℕ-Prop n) = is-prop-is-largest-lower-bound-ℕ n
```

### Being a largest strict lower bound is a property

```agda
module _
  {l : Level} (P : ℕ → UU l)
  where

  is-prop-is-largest-strict-lower-bound-ℕ :
    (n : ℕ) → is-prop (is-largest-strict-lower-bound-ℕ P n)
  is-prop-is-largest-strict-lower-bound-ℕ n =
    is-prop-Π
      ( λ x →
        is-prop-iff-Prop (is-strict-lower-bound-ℕ-Prop P x) (leq-ℕ-Prop x n))

  is-largest-strict-lower-bound-ℕ-Prop :
    (n : ℕ) → Prop l
  pr1 (is-largest-strict-lower-bound-ℕ-Prop n) =
    is-largest-strict-lower-bound-ℕ P n
  pr2 (is-largest-strict-lower-bound-ℕ-Prop n) =
    is-prop-is-largest-strict-lower-bound-ℕ n
```

### A strict lower bound is a lower bound

```agda
is-lower-bound-is-strict-lower-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) →
  is-strict-lower-bound-ℕ P n → is-lower-bound-ℕ P n
is-lower-bound-is-strict-lower-bound-ℕ P n H x p =
  leq-le-ℕ n x (H x p)
```

### Any two largest lower bounds are equal

```agda
eq-is-largest-lower-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (m n : ℕ) →
  is-largest-lower-bound-ℕ P m → is-largest-lower-bound-ℕ P n → m ＝ n
eq-is-largest-lower-bound-ℕ P m n H K =
  antisymmetric-leq-ℕ m n
    ( leq-is-largest-lower-bound-ℕ P n K m
      ( is-lower-bound-is-largest-lower-bound-ℕ P m H))
    ( leq-is-largest-lower-bound-ℕ P m H n
      ( is-lower-bound-is-largest-lower-bound-ℕ P n K))
```

### If $n$ is a largest lower bound, then $n + 1$ is not a largest lower bound

```agda
is-largest-lower-bound-succ-is-largest-lower-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) →
  is-largest-lower-bound-ℕ P n → ¬ is-largest-lower-bound-ℕ P (succ-ℕ n)
is-largest-lower-bound-succ-is-largest-lower-bound-ℕ P n H K =
  has-no-fixed-points-succ-ℕ n
    ( eq-is-largest-lower-bound-ℕ P (succ-ℕ n) n K H)
```

### If $n + 1$ is a lower bound and $P (n + 1)$ is empty, then $n$ is a lower bound

```agda
increase-is-lower-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) →
  is-lower-bound-ℕ P n → ¬ P n → is-lower-bound-ℕ P (succ-ℕ n)
increase-is-lower-bound-ℕ P n H f m p =
  map-left-unit-law-coproduct-is-empty
    ( n ＝ m)
    ( succ-ℕ n ≤-ℕ m)
    ( λ α → f (tr P (inv α) p))
    ( decide-leq-ℕ n m (H m p))
```

### Any successor natural number $n + 1$ such that $P (n + 1)$ is empty is not a largest lower bound

```agda
is-not-largest-lower-bound-is-empty-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) →
  ¬ P n → ¬ is-largest-lower-bound-ℕ P n
is-not-largest-lower-bound-is-empty-ℕ P n f H =
  neg-succ-leq-ℕ n
    ( leq-is-largest-lower-bound-ℕ P
      ( n)
      ( H)
      ( succ-ℕ n)
      ( increase-is-lower-bound-ℕ P n
        ( is-lower-bound-is-largest-lower-bound-ℕ P n H)
        ( f)))
```

### The type $P$ at the largest lower bound is nonempty

```agda
is-nonempty-structure-is-in-family-is-largest-lower-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) →
  is-largest-lower-bound-ℕ P n → is-nonempty (P n)
is-nonempty-structure-is-in-family-is-largest-lower-bound-ℕ P n H f =
  is-not-largest-lower-bound-is-empty-ℕ P n f H
```

### Any largest lower bound of a family of decidable types over $\mathbb{N}$ is structured in $P$

```agda
structure-largest-lower-bound-is-decidable-fam-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) →
  (n : ℕ) → is-largest-lower-bound-ℕ P n → P n
structure-largest-lower-bound-is-decidable-fam-ℕ P d n H =
  double-negation-elim-is-decidable
    ( d n)
    ( is-nonempty-structure-is-in-family-is-largest-lower-bound-ℕ P n H)
```

### Any lower bound equipped with structure is a largest lower bound

```agda
is-largest-lower-bound-is-lower-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) →
  P n → is-lower-bound-ℕ P n → is-largest-lower-bound-ℕ P n
pr1 (is-largest-lower-bound-is-lower-bound-ℕ P n p H m) K = K n p
pr2 (is-largest-lower-bound-is-lower-bound-ℕ P n p H m) K x q =
  transitive-leq-ℕ m n x (H x q) K
```
