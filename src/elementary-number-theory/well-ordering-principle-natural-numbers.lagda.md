# The well-ordering principle of the natural numbers

```agda
module elementary-number-theory.well-ordering-principle-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-types
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.lower-bounds-natural-numbers
open import elementary-number-theory.maximal-structured-natural-numbers
open import elementary-number-theory.minimal-structured-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.upper-bounds-natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.hilberts-epsilon-operators
open import foundation.identity-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "well-ordering principle of the natural numbers" WDID=Q2488476 WD="well-ordering principle"}}
asserts that for every family of
[decidable types](foundation.decidable-types.md) over ℕ equipped with a natural
number `n` and an element `p : P n`, we can find a least natural number `n₀`
with an element `p₀ : P n₀`.

The well-ordering principle has some useful consequences:

- For any family `P` of decidable types equipped with a natural number `n ≥ b`
  and an element `p : P n` we can find a least natural number `n₀ ≥ b` with an
  element `p₀ : P n₀`.
- For any family `P` of decidable types equipped with an element `n ≤ b` and an
  element `p : P n` we can find a largest natural number `n₁ ≤ b` with an
  element `p₁ : P n₁`.
- For any
  [strictly inflationary map](order-theory.inflationary-maps-strictly-ordered-types.md)
  `f : ℕ → ℕ` such that `f 0 ≤ b` we can find a largest natural number `n₁` such
  that `f n₁ ≤ b`.

## Theorems

### The Well-Ordering Principle

```agda
well-ordering-principle-ℕ' :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) → is-decidable (P 0) →
  (n : ℕ) → P n → minimal-element-ℕ P
well-ordering-principle-ℕ' P d (inl p0) n p =
  ( 0 , p0 , λ m _ → leq-zero-ℕ m)
well-ordering-principle-ℕ' P d (inr f) zero-ℕ p =
  ex-falso (f p)
well-ordering-principle-ℕ' P d (inr f) (succ-ℕ n) p =
  shift-minimal-element-ℕ P
    ( inr f)
    ( well-ordering-principle-ℕ' (P ∘ succ-ℕ) (d ∘ succ-ℕ) (d 1) n p)

module _
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) {n : ℕ} (p : P n)
  where

  well-ordering-principle-ℕ :
    minimal-element-ℕ P
  well-ordering-principle-ℕ =
    well-ordering-principle-ℕ' P d (d 0) n p

  nat-well-ordering-principle-ℕ :
    ℕ
  nat-well-ordering-principle-ℕ =
    nat-minimal-element-ℕ P well-ordering-principle-ℕ

  structure-nat-well-ordering-principle-ℕ :
    P nat-well-ordering-principle-ℕ
  structure-nat-well-ordering-principle-ℕ =
    structure-minimal-element-ℕ P well-ordering-principle-ℕ

  is-lower-bound-nat-well-ordering-principle-ℕ :
    is-lower-bound-ℕ P nat-well-ordering-principle-ℕ
  is-lower-bound-nat-well-ordering-principle-ℕ =
    is-lower-bound-minimal-element-ℕ P well-ordering-principle-ℕ

  is-largest-lower-bound-nat-well-ordering-principle-ℕ :
    is-largest-lower-bound-ℕ P nat-well-ordering-principle-ℕ
  is-largest-lower-bound-nat-well-ordering-principle-ℕ =
    is-largest-lower-bound-minimal-element-ℕ P well-ordering-principle-ℕ
```

## Properties

### The well-ordering principle returns `0` if `P 0` holds

```agda
is-zero-well-ordering-principle-ℕ' :
  {l : Level} (P : ℕ → UU l)
  (d : is-decidable-fam P) (d0 : is-decidable (P 0)) →
  (n : ℕ) (p : P n) → P 0 →
  is-zero-ℕ (nat-minimal-element-ℕ P (well-ordering-principle-ℕ' P d d0 n p))
is-zero-well-ordering-principle-ℕ' P d (inl x) n p p0 = refl
is-zero-well-ordering-principle-ℕ' P d (inr f) n p p0 = ex-falso (f p0)

is-zero-well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) →
  {n : ℕ} (p : P n) → P 0 → is-zero-ℕ (nat-well-ordering-principle-ℕ P d p)
is-zero-well-ordering-principle-ℕ P d p p0 =
  is-zero-well-ordering-principle-ℕ' P d (d 0) _ p p0
```

### Every decidable type family over `ℕ` equipped with an instance of an element with an upper bound has a bounded maximal element

```agda
module _
  {l : Level} (P : ℕ → UU l) (d : (x : ℕ) → is-decidable (P x)) (b : ℕ)
  where

  minimal-upper-bound-bounded-family-ℕ :
    minimal-element-ℕ (is-upper-bound-ℕ (bounded-family-family-ℕ P b))
  minimal-upper-bound-bounded-family-ℕ =
    well-ordering-principle-ℕ
      ( is-upper-bound-ℕ (bounded-family-family-ℕ P b))
      ( is-decidable-is-upper-bound-ℕ
        ( bounded-family-family-ℕ P b)
        ( λ x → is-decidable-product (is-decidable-leq-ℕ x b) (d x))
        ( b)
        ( λ x → pr1))
      ( λ x → pr1)

  nat-bounded-maximal-element-instance-ℕ :
    ℕ
  nat-bounded-maximal-element-instance-ℕ =
    nat-minimal-element-ℕ
      ( is-upper-bound-ℕ (bounded-family-family-ℕ P b))
      ( minimal-upper-bound-bounded-family-ℕ)

  is-upper-bound-bounded-maximal-element-instance-ℕ :
    is-upper-bound-ℕ
      ( bounded-family-family-ℕ P b)
      ( nat-bounded-maximal-element-instance-ℕ)
  is-upper-bound-bounded-maximal-element-instance-ℕ =
    structure-minimal-element-ℕ
      ( is-upper-bound-ℕ (bounded-family-family-ℕ P b))
      ( minimal-upper-bound-bounded-family-ℕ)

  is-largest-lower-bound-minimal-upper-bound-bounded-family-ℕ :
    is-largest-lower-bound-ℕ
      ( is-upper-bound-ℕ (bounded-family-family-ℕ P b))
      ( nat-bounded-maximal-element-instance-ℕ)
  is-largest-lower-bound-minimal-upper-bound-bounded-family-ℕ =
    is-largest-lower-bound-minimal-element-ℕ
      ( is-upper-bound-ℕ (bounded-family-family-ℕ P b))
      ( minimal-upper-bound-bounded-family-ℕ)

  upper-bound-nat-bounded-maximal-element-instance-ℕ :
    nat-bounded-maximal-element-instance-ℕ ≤-ℕ b
  upper-bound-nat-bounded-maximal-element-instance-ℕ =
    is-lower-bound-is-largest-lower-bound-ℕ
      ( is-upper-bound-ℕ (bounded-family-family-ℕ P b))
      ( nat-bounded-maximal-element-instance-ℕ)
      ( is-largest-lower-bound-minimal-upper-bound-bounded-family-ℕ)
      ( b)
      ( λ x → pr1)

  is-least-upper-bound-nat-bounded-maximal-element-instance-ℕ :
    is-least-upper-bound-ℕ
      ( bounded-family-family-ℕ P b)
      ( nat-bounded-maximal-element-instance-ℕ)
  pr1 (is-least-upper-bound-nat-bounded-maximal-element-instance-ℕ x) =
    is-lower-bound-is-largest-lower-bound-ℕ
      ( is-upper-bound-ℕ (bounded-family-family-ℕ P b))
      ( nat-bounded-maximal-element-instance-ℕ)
      ( is-largest-lower-bound-minimal-upper-bound-bounded-family-ℕ)
      ( x)
  pr2 (is-least-upper-bound-nat-bounded-maximal-element-instance-ℕ x) =
    is-upper-bound-leq-is-upper-bound-ℕ
      ( bounded-family-family-ℕ P b)
      ( nat-bounded-maximal-element-instance-ℕ)
      ( is-upper-bound-bounded-maximal-element-instance-ℕ)
      ( x)

  structure-bounded-maximal-element-instance-ℕ :
    (m : ℕ) → m ≤-ℕ b → P m →
    P nat-bounded-maximal-element-instance-ℕ
  structure-bounded-maximal-element-instance-ℕ m H p =
    pr2
      ( structure-least-upper-bound-is-decidable-fam-ℕ
        ( bounded-family-family-ℕ P b)
        ( λ x → is-decidable-product (is-decidable-leq-ℕ x b) (d x))
        ( nat-bounded-maximal-element-instance-ℕ)
        ( is-least-upper-bound-nat-bounded-maximal-element-instance-ℕ)
        ( m)
        ( H , p))

  bounded-maximal-element-instance-ℕ :
    (m : ℕ) → m ≤-ℕ b → P m → bounded-maximal-element-ℕ P b
  pr1 (bounded-maximal-element-instance-ℕ m H p) =
    nat-bounded-maximal-element-instance-ℕ
  pr1 (pr2 (bounded-maximal-element-instance-ℕ m H p)) =
    ( upper-bound-nat-bounded-maximal-element-instance-ℕ ,
      structure-bounded-maximal-element-instance-ℕ m H p)
  pr2 (pr2 (bounded-maximal-element-instance-ℕ m H p)) =
    is-upper-bound-bounded-maximal-element-instance-ℕ
```

### The ε-operator for decidable subtypes of ℕ

```agda
ε-operator-decidable-subtype-ℕ :
  {l1 : Level} (P : ℕ → Prop l1)
  (d : (x : ℕ) → is-decidable (type-Prop (P x))) →
  ε-operator-Hilbert (type-subtype P)
ε-operator-decidable-subtype-ℕ {l1} P d t =
  tot
    ( λ x → pr1)
    ( apply-universal-property-trunc-Prop t
      ( minimal-element-ℕ-Prop P)
      ( λ (n , p) → well-ordering-principle-ℕ (type-Prop ∘ P) d p))
```
