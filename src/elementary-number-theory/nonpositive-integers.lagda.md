# The nonpositive integers

```agda
module elementary-number-theory.nonpositive-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-subtypes
open import foundation.decidable-type-families
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

The [integers](elementary-number-theory.integers.md) are defined as a
[disjoint sum](foundation-core.coproduct-types.md) of three components. A single
element component containing the integer _zero_, and two copies of the
[natural numbers](elementary-number-theory.natural-numbers.md), one copy for the
[negative integers](elementary-number-theory.negative-integers.md) and one copy
for the [positive integers](elementary-number-theory.positive-integers.md).
Arranged on a number line, we have

```text
  ⋯  -4  -3  -2  -1   0   1   2   3   4   ⋯
  <---+---+---+---]   |   [---+---+---+--->
```

The {{#concept "nonpositive" Disambiguation="integer" Agda=is-nonpositive-ℤ}}
integers are `zero-ℤ` and the negative component of the integers.

## Definitions

### Nonnpositive integers

```agda
is-nonpositive-ℤ : ℤ → UU lzero
is-nonpositive-ℤ (inl k) = unit
is-nonpositive-ℤ (inr (inl x)) = unit
is-nonpositive-ℤ (inr (inr x)) = empty

is-prop-is-nonpositive-ℤ : (x : ℤ) → is-prop (is-nonpositive-ℤ x)
is-prop-is-nonpositive-ℤ (inl x) = is-prop-unit
is-prop-is-nonpositive-ℤ (inr (inl x)) = is-prop-unit
is-prop-is-nonpositive-ℤ (inr (inr x)) = is-prop-empty

subtype-nonpositive-ℤ : subtype lzero ℤ
subtype-nonpositive-ℤ x = (is-nonpositive-ℤ x , is-prop-is-nonpositive-ℤ x)

nonpositive-ℤ : UU lzero
nonpositive-ℤ = type-subtype subtype-nonpositive-ℤ

is-nonpositive-eq-ℤ :
  {x y : ℤ} → x ＝ y → is-nonpositive-ℤ x → is-nonpositive-ℤ y
is-nonpositive-eq-ℤ = tr is-nonpositive-ℤ

module _
  (p : nonpositive-ℤ)
  where

  int-nonpositive-ℤ : ℤ
  int-nonpositive-ℤ = pr1 p

  is-nonpositive-int-nonpositive-ℤ : is-nonpositive-ℤ int-nonpositive-ℤ
  is-nonpositive-int-nonpositive-ℤ = pr2 p
```

### Nonpositive constants

```agda
zero-nonpositive-ℤ : nonpositive-ℤ
zero-nonpositive-ℤ = (zero-ℤ , star)

neg-one-nonpositive-ℤ : nonpositive-ℤ
neg-one-nonpositive-ℤ = (neg-one-ℤ , star)
```

## Properties

### Nonpositivity is decidable

```agda
is-decidable-is-nonpositive-ℤ : is-decidable-family is-nonpositive-ℤ
is-decidable-is-nonpositive-ℤ (inl x) = inl star
is-decidable-is-nonpositive-ℤ (inr (inl x)) = inl star
is-decidable-is-nonpositive-ℤ (inr (inr x)) = inr id

decidable-subtype-nonpositive-ℤ : decidable-subtype lzero ℤ
decidable-subtype-nonpositive-ℤ x =
  ( is-nonpositive-ℤ x ,
    is-prop-is-nonpositive-ℤ x ,
    is-decidable-is-nonpositive-ℤ x)
```

### The nonpositive integers form a set

```agda
is-set-nonpositive-ℤ : is-set nonpositive-ℤ
is-set-nonpositive-ℤ =
  is-set-emb
    ( emb-subtype subtype-nonpositive-ℤ)
    ( is-set-ℤ)
```

### The only nonpositive integer with a nonpositive negative is zero

```agda
is-zero-is-nonpositive-neg-is-nonpositive-ℤ :
  {x : ℤ} → is-nonpositive-ℤ x → is-nonpositive-ℤ (neg-ℤ x) → is-zero-ℤ x
is-zero-is-nonpositive-neg-is-nonpositive-ℤ {inr (inl star)} nonneg nonpos =
  refl
```

### The predecessor of a nonpositive integer is nonpositive

```agda
is-nonpositive-pred-is-nonpositive-ℤ :
  {x : ℤ} → is-nonpositive-ℤ x → is-nonpositive-ℤ (pred-ℤ x)
is-nonpositive-pred-is-nonpositive-ℤ {inl x} H = H
is-nonpositive-pred-is-nonpositive-ℤ {inr (inl x)} H = H

pred-nonpositive-ℤ : nonpositive-ℤ → nonpositive-ℤ
pred-nonpositive-ℤ (x , H) = pred-ℤ x , is-nonpositive-pred-is-nonpositive-ℤ H
```

### The canonical equivalence between natural numbers and positive integers

```agda
nonpositive-int-ℕ : ℕ → nonpositive-ℤ
nonpositive-int-ℕ = rec-ℕ zero-nonpositive-ℤ (λ _ → pred-nonpositive-ℤ)

nat-nonpositive-ℤ : nonpositive-ℤ → ℕ
nat-nonpositive-ℤ (inl x , H) = succ-ℕ x
nat-nonpositive-ℤ (inr x , H) = zero-ℕ

eq-nat-nonpositive-pred-nonpositive-ℤ :
  (x : nonpositive-ℤ) →
  nat-nonpositive-ℤ (pred-nonpositive-ℤ x) ＝ succ-ℕ (nat-nonpositive-ℤ x)
eq-nat-nonpositive-pred-nonpositive-ℤ (inl x , H) = refl
eq-nat-nonpositive-pred-nonpositive-ℤ (inr (inl x) , H) = refl

is-section-nat-nonpositive-ℤ :
  (x : nonpositive-ℤ) → nonpositive-int-ℕ (nat-nonpositive-ℤ x) ＝ x
is-section-nat-nonpositive-ℤ (inl zero-ℕ , H) = refl
is-section-nat-nonpositive-ℤ (inl (succ-ℕ x) , H) =
  ap pred-nonpositive-ℤ (is-section-nat-nonpositive-ℤ (inl x , H))
is-section-nat-nonpositive-ℤ (inr (inl x) , H) = refl

is-retraction-nat-nonpositive-ℤ :
  (n : ℕ) → nat-nonpositive-ℤ (nonpositive-int-ℕ n) ＝ n
is-retraction-nat-nonpositive-ℤ zero-ℕ = refl
is-retraction-nat-nonpositive-ℤ (succ-ℕ n) =
  eq-nat-nonpositive-pred-nonpositive-ℤ (nonpositive-int-ℕ n) ∙
  ap succ-ℕ (is-retraction-nat-nonpositive-ℤ n)

is-equiv-nonpositive-int-ℕ : is-equiv nonpositive-int-ℕ
pr1 (pr1 is-equiv-nonpositive-int-ℕ) = nat-nonpositive-ℤ
pr2 (pr1 is-equiv-nonpositive-int-ℕ) = is-section-nat-nonpositive-ℤ
pr1 (pr2 is-equiv-nonpositive-int-ℕ) = nat-nonpositive-ℤ
pr2 (pr2 is-equiv-nonpositive-int-ℕ) = is-retraction-nat-nonpositive-ℤ

equiv-nonpositive-int-ℕ : ℕ ≃ nonpositive-ℤ
pr1 equiv-nonpositive-int-ℕ = nonpositive-int-ℕ
pr2 equiv-nonpositive-int-ℕ = is-equiv-nonpositive-int-ℕ
```

## See also

- The relations between nonpositive and positive, nonnegative and negative
  integers are derived in
  [`positive-and-negative-integers`](elementary-number-theory.positive-and-negative-integers.md)
