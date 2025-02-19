# Upper bounds for structured natural numbers

```agda
module elementary-number-theory.upper-bounds-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.coproduct-types
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

- A natural number $n$ is said to be an
  {{#concept "upper bound" Disambiguation="structured natural numbers" Agda=is-upper-bound-ℕ}}
  if there is a function from $P(x)$ to the type $x \leq n$ for all
  $x : \mathbb{N}$.
- A natural number $n$ is said to be a
  {{#concept "strict upper bound" Disambiguation="structured natural numbers" Agda=is-strict-upper-bound-ℕ}}
  if there is a function from $P(x)$ to the type $x < n$ for all
  $x : \mathbb{N}$.
- A natural number $n$ is said to be a
  {{#concept "least upper bound" Disambiguation="structured natural numbers" Agda=is-least-upper-bound-ℕ}}
  if any natural number $x$ is an upper bound if and only if $n \leq x$.
- A natural number $n$ is said to be a
  {{#concept "least strict upper bound" Disambiguation="structured natural numbers" Agda=is-least-strict-upper-bound-ℕ}}
  if any natural number $x$ is a strict upper bound if and only if $n \leq x$.

## Definitions

### Upper bounds

```agda
is-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) → ℕ → UU l
is-upper-bound-ℕ P n =
  (m : ℕ) → P m → m ≤-ℕ n
```

### Strict upper bounds

```agda
is-strict-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) → UU l
is-strict-upper-bound-ℕ P n =
  (m : ℕ) → P m → m <-ℕ n
```

### Least upper bounds

```agda
is-least-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) → ℕ → UU l
is-least-upper-bound-ℕ P n =
  (x : ℕ) → is-upper-bound-ℕ P x ↔ n ≤-ℕ x

is-upper-bound-is-least-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) →
  is-least-upper-bound-ℕ P n → is-upper-bound-ℕ P n
is-upper-bound-is-least-upper-bound-ℕ P n H =
  backward-implication (H n) (refl-leq-ℕ n)

leq-is-least-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) →
  is-least-upper-bound-ℕ P n →
  (m : ℕ) → is-upper-bound-ℕ P m → n ≤-ℕ m
leq-is-least-upper-bound-ℕ P n H m =
  forward-implication (H m)
```

### Least strict upper bounds

```agda
is-least-strict-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) → ℕ → UU l
is-least-strict-upper-bound-ℕ P n =
  (x : ℕ) → is-strict-upper-bound-ℕ P x ↔ n ≤-ℕ x
```

## Properties

### Being an upper bound is a property

```agda
module _
  {l : Level} (P : ℕ → UU l)
  where

  is-prop-is-upper-bound-ℕ :
    (n : ℕ) → is-prop (is-upper-bound-ℕ P n)
  is-prop-is-upper-bound-ℕ n =
    is-prop-Π (λ x → is-prop-function-type (is-prop-leq-ℕ x n))

  is-upper-bound-ℕ-Prop :
    (n : ℕ) → Prop l
  pr1 (is-upper-bound-ℕ-Prop n) = is-upper-bound-ℕ P n
  pr2 (is-upper-bound-ℕ-Prop n) = is-prop-is-upper-bound-ℕ n
```

### Being a strict upper bound is a property

```agda
module _
  {l : Level} (P : ℕ → UU l)
  where

  is-prop-is-strict-upper-bound-ℕ :
    (n : ℕ) → is-prop (is-strict-upper-bound-ℕ P n)
  is-prop-is-strict-upper-bound-ℕ n =
    is-prop-Π (λ x → is-prop-function-type (is-prop-le-ℕ x n))

  is-strict-upper-bound-ℕ-Prop :
    (n : ℕ) → Prop l
  pr1 (is-strict-upper-bound-ℕ-Prop n) = is-strict-upper-bound-ℕ P n
  pr2 (is-strict-upper-bound-ℕ-Prop n) = is-prop-is-strict-upper-bound-ℕ n
```

### Being a least upper bound is a property

```agda
module _
  {l : Level} (P : ℕ → UU l)
  where

  is-prop-is-least-upper-bound-ℕ :
    (n : ℕ) → is-prop (is-least-upper-bound-ℕ P n)
  is-prop-is-least-upper-bound-ℕ n =
    is-prop-Π
      ( λ x → is-prop-iff-Prop (is-upper-bound-ℕ-Prop P x) (leq-ℕ-Prop n x))

  is-least-upper-bound-ℕ-Prop :
    (n : ℕ) → Prop l
  pr1 (is-least-upper-bound-ℕ-Prop n) = is-least-upper-bound-ℕ P n
  pr2 (is-least-upper-bound-ℕ-Prop n) = is-prop-is-least-upper-bound-ℕ n
```

### Being a least strict upper bound is a property

```agda
module _
  {l : Level} (P : ℕ → UU l)
  where

  is-prop-is-least-strict-upper-bound-ℕ :
    (n : ℕ) → is-prop (is-least-strict-upper-bound-ℕ P n)
  is-prop-is-least-strict-upper-bound-ℕ n =
    is-prop-Π
      ( λ x →
        is-prop-iff-Prop (is-strict-upper-bound-ℕ-Prop P x) (leq-ℕ-Prop n x))

  is-least-strict-upper-bound-ℕ-Prop :
    (n : ℕ) → Prop l
  pr1 (is-least-strict-upper-bound-ℕ-Prop n) =
    is-least-strict-upper-bound-ℕ P n
  pr2 (is-least-strict-upper-bound-ℕ-Prop n) =
    is-prop-is-least-strict-upper-bound-ℕ n
```

### A strict upper bound is an upper bound

```agda
is-upper-bound-is-strict-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) →
  is-strict-upper-bound-ℕ P n → is-upper-bound-ℕ P n
is-upper-bound-is-strict-upper-bound-ℕ P n H x p =
  leq-le-ℕ x n (H x p)
```

### Any two least upper bounds are equal

```agda
eq-is-least-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (m n : ℕ) →
  is-least-upper-bound-ℕ P m → is-least-upper-bound-ℕ P n → m ＝ n
eq-is-least-upper-bound-ℕ P m n H K =
  antisymmetric-leq-ℕ m n
    ( leq-is-least-upper-bound-ℕ P m H n
      ( is-upper-bound-is-least-upper-bound-ℕ P n K))
    ( leq-is-least-upper-bound-ℕ P n K m
      ( is-upper-bound-is-least-upper-bound-ℕ P m H))
```

### If $n + 1$ is a least upper bound, then $n$ is not a least upper bound

```agda
is-not-least-upper-bound-is-least-upper-bound-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) →
  is-least-upper-bound-ℕ P (succ-ℕ n) → ¬ (is-least-upper-bound-ℕ P n)
is-not-least-upper-bound-is-least-upper-bound-succ-ℕ P n H K =
  has-no-fixed-points-succ-ℕ n (eq-is-least-upper-bound-ℕ P (succ-ℕ n) n H K)
```

### If $n + 1$ is an upper bound and $P (n + 1)$ is empty, then $n$ is an upper bound

```agda
decrease-is-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) →
  is-upper-bound-ℕ P (succ-ℕ n) → ¬ P (succ-ℕ n) → is-upper-bound-ℕ P n
decrease-is-upper-bound-ℕ P n H f m p =
  map-right-unit-law-coproduct-is-empty
    ( m ≤-ℕ n)
    ( m ＝ succ-ℕ n)
    ( λ α → f (tr P α p))
    ( decide-leq-succ-ℕ m n (H m p))
```

### Any successor natural number $n + 1$ such that $P (n + 1)$ is empty is not a least upper bound

```agda
is-not-least-upper-bound-is-empty-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) →
  ¬ P (succ-ℕ n) → ¬ is-least-upper-bound-ℕ P (succ-ℕ n)
is-not-least-upper-bound-is-empty-succ-ℕ P n f H =
  neg-succ-leq-ℕ n
    ( leq-is-least-upper-bound-ℕ P
      ( succ-ℕ n)
      ( H)
      ( n)
      ( decrease-is-upper-bound-ℕ P n
        ( is-upper-bound-is-least-upper-bound-ℕ P (succ-ℕ n) H)
        ( f)))
```

### Given a structured natural number, any natural number $n$ such that $P(n)$ is empty is not least upper bound

```agda
is-not-least-upper-bound-is-empty-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) →
  (m : ℕ) → P m → ¬ (P n) → ¬ is-least-upper-bound-ℕ P n
is-not-least-upper-bound-is-empty-ℕ P zero-ℕ m p f H =
  f ( tr P
      ( is-zero-leq-zero-ℕ m (is-upper-bound-is-least-upper-bound-ℕ P 0 H m p))
      ( p))
is-not-least-upper-bound-is-empty-ℕ P (succ-ℕ n) m p f H =
  is-not-least-upper-bound-is-empty-succ-ℕ P n f H
```

### Given a number with an element in $P$, the type $P$ at the least upper bound is nonempty

```agda
is-nonempty-structure-is-in-family-is-least-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) →
  is-least-upper-bound-ℕ P n → (m : ℕ) → P m → is-nonempty (P n)
is-nonempty-structure-is-in-family-is-least-upper-bound-ℕ P n H m p f =
  is-not-least-upper-bound-is-empty-ℕ P n m p f H
```

### Given a structured number in a decidable type family $P$, the least upper bound is structured in $P$

```agda
structure-least-upper-bound-is-decidable-fam-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) →
  (n : ℕ) → is-least-upper-bound-ℕ P n → (m : ℕ) → P m → P n
structure-least-upper-bound-is-decidable-fam-ℕ P d n H m p =
  double-negation-elim-is-decidable
    ( d n)
    ( is-nonempty-structure-is-in-family-is-least-upper-bound-ℕ P n H m p)
```

### Any upper bound equipped with structure is a least upper bound

```agda
is-least-upper-bound-is-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (n : ℕ) →
  P n → is-upper-bound-ℕ P n → is-least-upper-bound-ℕ P n
pr1 (is-least-upper-bound-is-upper-bound-ℕ P n p H m) K = K n p
pr2 (is-least-upper-bound-is-upper-bound-ℕ P n p H m) K x q =
  transitive-leq-ℕ x n m K (H x q)
```

### Any element greater than an upper bound is an upper bound

```agda
is-upper-bound-leq-is-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) →
  (b : ℕ) → is-upper-bound-ℕ P b →
  (n : ℕ) → b ≤-ℕ n → is-upper-bound-ℕ P n
is-upper-bound-leq-is-upper-bound-ℕ P b H n K x p =
  transitive-leq-ℕ x b n K (H x p)
```

### Being an upper bound of a decidable type family is decidable, given an upper bound

The type family `is-upper-bound-ℕ P` is an example of a type family `Q` over the
natural numbers satisfying

```text
  Q b → Π (n : ℕ), is-decidable (Q n)
```

for any natural number `b`.

```agda
is-decidable-is-upper-bound-ℕ' :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) →
  (b : ℕ) → is-upper-bound-ℕ P b → is-decidable (P b) →
  (n : ℕ) → is-decidable (is-upper-bound-ℕ P n)
is-decidable-is-upper-bound-ℕ' P d zero-ℕ H e n =
  inl (is-upper-bound-leq-is-upper-bound-ℕ P 0 H n (leq-zero-ℕ n))
is-decidable-is-upper-bound-ℕ' P d (succ-ℕ b) H (inl p) n =
  is-decidable-iff'
    ( inv-iff (is-least-upper-bound-is-upper-bound-ℕ P (succ-ℕ b) p H n))
    ( is-decidable-leq-ℕ (succ-ℕ b) n)
is-decidable-is-upper-bound-ℕ' P d (succ-ℕ b) H (inr f) =
  is-decidable-is-upper-bound-ℕ' P d b
    ( decrease-is-upper-bound-ℕ P b H f)
    ( d b)

is-decidable-is-upper-bound-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) →
  (b : ℕ) → is-upper-bound-ℕ P b →
  (n : ℕ) → is-decidable (is-upper-bound-ℕ P n)
is-decidable-is-upper-bound-ℕ P d b H =
  is-decidable-is-upper-bound-ℕ' P d b H (d b)
```
