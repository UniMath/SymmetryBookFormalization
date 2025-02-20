# Finite elements in the type of increasing binary sequences

```agda
module set-theory.finite-elements-increasing-binary-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.decidable-total-order-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.constant-maps
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation-stable-equality
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.inequality-booleans
open import foundation.inhabited-types
open import foundation.injective-maps
open import foundation.logical-operations-booleans
open import foundation.maybe
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.tight-apartness-relations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.identity-types

open import order-theory.order-preserving-maps-posets

open import set-theory.cantor-space
open import set-theory.increasing-binary-sequences
```

</details>

## Idea

An [increasing binary sequence](set-theory.increasing-binary-sequences.md) `x`
is a
{{#concept "finite" Disambiguation="element of the type of increasing binary sequences" Agda=is-finite-ℕ∞↑}}
element if there [exists](foundation.existential-quantification.md) a
[natural number](elementary-number-theory.natural-numbers.md) `n : ℕ` such that
`xₙ` is true.

## Definitions

### Finite boundedness of increasing binary sequences

An increasing binary sequence `x` is _bounded_ by a natural number `n` if `x n`
is true.

```agda
leq-decidable-prop-ℕ-ℕ∞↑ : ℕ∞↑ → ℕ → Decidable-Prop lzero
leq-decidable-prop-ℕ-ℕ∞↑ x n = is-true-Decidable-Prop (sequence-ℕ∞↑ x n)

leq-prop-ℕ-ℕ∞↑ : ℕ∞↑ → ℕ → Prop lzero
leq-prop-ℕ-ℕ∞↑ x n = prop-Decidable-Prop (leq-decidable-prop-ℕ-ℕ∞↑ x n)

leq-ℕ-ℕ∞↑ : ℕ∞↑ → ℕ → UU lzero
leq-ℕ-ℕ∞↑ x n = type-Decidable-Prop (leq-decidable-prop-ℕ-ℕ∞↑ x n)

infix 30 _≤-ℕ∞↑-ℕ_
_≤-ℕ∞↑-ℕ_ : ℕ∞↑ → ℕ → UU lzero
_≤-ℕ∞↑-ℕ_ = leq-ℕ-ℕ∞↑

is-prop-leq-ℕ-ℕ∞↑ : (x : ℕ∞↑) (n : ℕ) → is-prop (x ≤-ℕ∞↑-ℕ n)
is-prop-leq-ℕ-ℕ∞↑ x n =
  is-prop-type-Decidable-Prop (leq-decidable-prop-ℕ-ℕ∞↑ x n)

is-decidable-leq-ℕ-ℕ∞↑ : (x : ℕ∞↑) (n : ℕ) → is-decidable (x ≤-ℕ∞↑-ℕ n)
is-decidable-leq-ℕ-ℕ∞↑ x n =
  is-decidable-Decidable-Prop (leq-decidable-prop-ℕ-ℕ∞↑ x n)
```

### Strict finite boundedness below of increasing binary sequences

An increasing binary sequence `x` is _bounded below_ by a natural number `n` if
`x n` is false.

```agda
le-decidable-prop-ℕ∞↑-ℕ : ℕ → ℕ∞↑ → Decidable-Prop lzero
le-decidable-prop-ℕ∞↑-ℕ n x = is-false-Decidable-Prop (sequence-ℕ∞↑ x n)

le-prop-ℕ∞↑-ℕ : ℕ → ℕ∞↑ → Prop lzero
le-prop-ℕ∞↑-ℕ n x = prop-Decidable-Prop (le-decidable-prop-ℕ∞↑-ℕ n x)

le-ℕ∞↑-ℕ : ℕ → ℕ∞↑ → UU lzero
le-ℕ∞↑-ℕ x n = type-Decidable-Prop (le-decidable-prop-ℕ∞↑-ℕ x n)

infix 30 _<-ℕ-ℕ∞↑_
_<-ℕ-ℕ∞↑_ : ℕ → ℕ∞↑ → UU lzero
_<-ℕ-ℕ∞↑_ = le-ℕ∞↑-ℕ

is-prop-le-ℕ∞↑-ℕ : (n : ℕ) (x : ℕ∞↑) → is-prop (n <-ℕ-ℕ∞↑ x)
is-prop-le-ℕ∞↑-ℕ n x =
  is-prop-type-Decidable-Prop (le-decidable-prop-ℕ∞↑-ℕ n x)

is-decidable-le-ℕ∞↑-ℕ : (n : ℕ) (x : ℕ∞↑) → is-decidable (n <-ℕ-ℕ∞↑ x)
is-decidable-le-ℕ∞↑-ℕ n x =
  is-decidable-Decidable-Prop (le-decidable-prop-ℕ∞↑-ℕ n x)
```

```agda
is-positive-ℕ∞↑ : ℕ∞↑ → UU lzero
is-positive-ℕ∞↑ x = 0 <-ℕ-ℕ∞↑ x
```

### Bounds on the size of a finite element in increasing binary sequences

```agda
upper-bound-ℕ∞↑ : ℕ∞↑ → UU lzero
upper-bound-ℕ∞↑ x = Σ ℕ (x ≤-ℕ∞↑-ℕ_)
```

### Least upper bounds on the size of a finite element in increasing binary sequences

```agda
least-upper-bound-ℕ∞↑ : ℕ∞↑ → UU lzero
least-upper-bound-ℕ∞↑ x =
  Σ (upper-bound-ℕ∞↑ x) (λ n → (m : upper-bound-ℕ∞↑ x) → pr1 n ≤-ℕ pr1 m)

all-elements-equal-least-upper-bound-ℕ∞↑ :
  (x : ℕ∞↑) → all-elements-equal (least-upper-bound-ℕ∞↑ x)
all-elements-equal-least-upper-bound-ℕ∞↑
  (x , X) ((n , p) , H) ((m , q) , K) =
  eq-pair-Σ
    ( eq-pair-Σ
      ( antisymmetric-leq-ℕ n m (H (m , q)) (K (n , p)))
      ( eq-is-prop (is-set-bool (x m) true)))
    ( eq-is-prop (is-prop-Π λ u → is-prop-leq-ℕ m (pr1 u)))

is-prop-least-upper-bound-ℕ∞↑ : (x : ℕ∞↑) → is-prop (least-upper-bound-ℕ∞↑ x)
is-prop-least-upper-bound-ℕ∞↑ x =
  is-prop-all-elements-equal (all-elements-equal-least-upper-bound-ℕ∞↑ x)

least-upper-bound-prop-ℕ∞↑ : ℕ∞↑ → Prop lzero
least-upper-bound-prop-ℕ∞↑ x =
  ( least-upper-bound-ℕ∞↑ x , is-prop-least-upper-bound-ℕ∞↑ x)
```

### The predicate on an increasing binary sequence of being a finite element

```agda
is-finite-prop-ℕ∞↑ : ℕ∞↑ → Prop lzero
is-finite-prop-ℕ∞↑ = is-inhabited-Prop ∘ upper-bound-ℕ∞↑

is-finite-ℕ∞↑ :
  ℕ∞↑ → UU lzero
is-finite-ℕ∞↑ =
  type-Prop ∘ is-finite-prop-ℕ∞↑

is-prop-is-finite-ℕ∞↑ :
  (x : ℕ∞↑) →
  is-prop (is-finite-ℕ∞↑ x)
is-prop-is-finite-ℕ∞↑ =
  is-prop-type-Prop ∘ is-finite-prop-ℕ∞↑
```

### The canonical inclusion of the natural numbers into increasing binary sequences

```agda
inclusion-ℕ∞↑ : ℕ → ℕ∞↑
inclusion-ℕ∞↑ = rec-ℕ (zero-ℕ∞↑) (λ _ → succ-ℕ∞↑)

upper-bound-inclusion-ℕ∞↑ :
  (n : ℕ) → upper-bound-ℕ∞↑ (inclusion-ℕ∞↑ n)
upper-bound-inclusion-ℕ∞↑ zero-ℕ =
  ( 0 , refl)
upper-bound-inclusion-ℕ∞↑ (succ-ℕ n) =
  ( succ-ℕ (pr1 (upper-bound-inclusion-ℕ∞↑ n)) ,
    pr2 (upper-bound-inclusion-ℕ∞↑ n))

is-finite-inclusion-ℕ∞↑ : (n : ℕ) → is-finite-ℕ∞↑ (inclusion-ℕ∞↑ n)
is-finite-inclusion-ℕ∞↑ n = unit-trunc-Prop (upper-bound-inclusion-ℕ∞↑ n)
```

## Properties

### Infinity is not finitely bounded

```agda
is-not-finitely-bounded-infinity-ℕ∞↑ : (n : ℕ) → ¬ (infinity-ℕ∞↑ ≤-ℕ∞↑-ℕ n)
is-not-finitely-bounded-infinity-ℕ∞↑ n ()
```

### If an increasing binary sequence is not finitely bounded then it is infinite

```agda
module _
  (x : ℕ∞↑) (H : (n : ℕ) → ¬ (x ≤-ℕ∞↑-ℕ n))
  where

  Eq-infinity-is-not-finitely-bounded-ℕ∞↑ : sequence-ℕ∞↑ x ~ const ℕ false
  Eq-infinity-is-not-finitely-bounded-ℕ∞↑ n =
    is-false-is-not-true (sequence-ℕ∞↑ x n) (H n)

  eq-infinity-is-not-finitely-bounded-ℕ∞↑ : x ＝ infinity-ℕ∞↑
  eq-infinity-is-not-finitely-bounded-ℕ∞↑ =
    eq-Eq-ℕ∞↑ (Eq-infinity-is-not-finitely-bounded-ℕ∞↑)
```

### If an increasing binary sequence has an upper bound there exists a unique least upper bound

```agda
-- least-upper-bound-upper-bound-ℕ∞↑ :
--   (x : ℕ∞↑) →
--   upper-bound-ℕ∞↑ x →
--   least-upper-bound-ℕ∞↑ x
-- least-upper-bound-upper-bound-ℕ∞↑ x H = {!   !}
```

### If an increasing binary sequence is strictly bounded below by a natural number, then it is positive

```agda
le-le-succ-ℕ∞↑-ℕ : (x : ℕ∞↑) (n : ℕ) → (succ-ℕ n) <-ℕ-ℕ∞↑ x → n <-ℕ-ℕ∞↑ x
le-le-succ-ℕ∞↑-ℕ x n =
  is-false-is-false-leq-bool (is-increasing-sequence-ℕ∞↑ x n)

is-positive-le-ℕ∞↑-ℕ : (x : ℕ∞↑) (n : ℕ) → n <-ℕ-ℕ∞↑ x → is-positive-ℕ∞↑ x
is-positive-le-ℕ∞↑-ℕ x 0 p = p
is-positive-le-ℕ∞↑-ℕ x (succ-ℕ n) p =
  is-positive-le-ℕ∞↑-ℕ x n (le-le-succ-ℕ∞↑-ℕ x n p)
```

### If an increasing binary sequence is bounded above by a finite number, then it is bounded above by any larger finite number

```agda
abstract
  leq-succ-leq-ℕ-ℕ∞↑ : (x : ℕ∞↑) (n : ℕ) → x ≤-ℕ∞↑-ℕ n → x ≤-ℕ∞↑-ℕ (succ-ℕ n)
  leq-succ-leq-ℕ-ℕ∞↑ x n =
    is-true-is-true-leq-bool (is-increasing-sequence-ℕ∞↑ x n)

abstract
  leq-leq-zero-ℕ-ℕ∞↑ : (x : ℕ∞↑) (n : ℕ) → x ≤-ℕ∞↑-ℕ 0 → x ≤-ℕ∞↑-ℕ n
  leq-leq-zero-ℕ-ℕ∞↑ x 0 s = s
  leq-leq-zero-ℕ-ℕ∞↑ x (succ-ℕ i) s =
    contrapositive-is-false-bool
      ( is-false-is-false-leq-bool (is-increasing-sequence-ℕ∞↑ x i))
      ( leq-leq-zero-ℕ-ℕ∞↑ x i s)

abstract
  concatenate-right-leq-ℕ-ℕ∞↑ :
    (x : ℕ∞↑) (n m : ℕ) → n ≤-ℕ m → x ≤-ℕ∞↑-ℕ n → x ≤-ℕ∞↑-ℕ m
  concatenate-right-leq-ℕ-ℕ∞↑ x 0 m p = leq-leq-zero-ℕ-ℕ∞↑ x m
  concatenate-right-leq-ℕ-ℕ∞↑ x (succ-ℕ n) (succ-ℕ m) =
    concatenate-right-leq-ℕ-ℕ∞↑ (shift-left-ℕ∞↑ x) n m
```
