# The nonnegative integers

```agda
module elementary-number-theory.nonnegative-integers where
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

The {{#concept "nonnegative" Disambiguation="integer" Agda=is-nonnegative-ℤ}}
integers are `zero-ℤ` and the positive component of the integers.

## Definitions

### Nonnegative integers

```agda
is-nonnegative-ℤ : ℤ → UU lzero
is-nonnegative-ℤ (inl x) = empty
is-nonnegative-ℤ (inr x) = unit

is-prop-is-nonnegative-ℤ : (x : ℤ) → is-prop (is-nonnegative-ℤ x)
is-prop-is-nonnegative-ℤ (inl x) = is-prop-empty
is-prop-is-nonnegative-ℤ (inr x) = is-prop-unit

subtype-nonnegative-ℤ : subtype lzero ℤ
subtype-nonnegative-ℤ x = (is-nonnegative-ℤ x , is-prop-is-nonnegative-ℤ x)

nonnegative-ℤ : UU lzero
nonnegative-ℤ = type-subtype subtype-nonnegative-ℤ

is-nonnegative-eq-ℤ :
  {x y : ℤ} → x ＝ y → is-nonnegative-ℤ x → is-nonnegative-ℤ y
is-nonnegative-eq-ℤ = tr is-nonnegative-ℤ

module _
  (p : nonnegative-ℤ)
  where

  int-nonnegative-ℤ : ℤ
  int-nonnegative-ℤ = pr1 p

  is-nonnegative-int-nonnegative-ℤ : is-nonnegative-ℤ int-nonnegative-ℤ
  is-nonnegative-int-nonnegative-ℤ = pr2 p
```

### Nonnegative integer constants

```agda
zero-nonnegative-ℤ : nonnegative-ℤ
zero-nonnegative-ℤ = (zero-ℤ , star)

one-nonnegative-ℤ : nonnegative-ℤ
one-nonnegative-ℤ = (one-ℤ , star)
```

## Properties

### Nonnegativity is decidable

```agda
is-decidable-is-nonnegative-ℤ : is-decidable-family is-nonnegative-ℤ
is-decidable-is-nonnegative-ℤ (inl x) = inr id
is-decidable-is-nonnegative-ℤ (inr x) = inl star

decidable-subtype-nonnegative-ℤ : decidable-subtype lzero ℤ
decidable-subtype-nonnegative-ℤ x =
  ( is-nonnegative-ℤ x ,
    is-prop-is-nonnegative-ℤ x ,
    is-decidable-is-nonnegative-ℤ x)
```

### The nonnegative integers form a set

```agda
is-set-nonnegative-ℤ : is-set nonnegative-ℤ
is-set-nonnegative-ℤ =
  is-set-emb
    ( emb-subtype subtype-nonnegative-ℤ)
    ( is-set-ℤ)
```

### The only nonnegative integer with a nonnegative negative is zero

```agda
is-zero-is-nonnegative-neg-is-nonnegative-ℤ :
  {x : ℤ} → is-nonnegative-ℤ x → is-nonnegative-ℤ (neg-ℤ x) → is-zero-ℤ x
is-zero-is-nonnegative-neg-is-nonnegative-ℤ {inr (inl star)} nonneg nonpos =
  refl
```

### The successor of a nonnegative integer is nonnegative

```agda
is-nonnegative-succ-is-nonnegative-ℤ :
  {x : ℤ} → is-nonnegative-ℤ x → is-nonnegative-ℤ (succ-ℤ x)
is-nonnegative-succ-is-nonnegative-ℤ {inr (inl x)} H = H
is-nonnegative-succ-is-nonnegative-ℤ {inr (inr x)} H = H

succ-nonnegative-ℤ : nonnegative-ℤ → nonnegative-ℤ
succ-nonnegative-ℤ (x , H) = succ-ℤ x , is-nonnegative-succ-is-nonnegative-ℤ H
```

### The integer image of a natural number is nonnegative

```agda
is-nonnegative-int-ℕ : (n : ℕ) → is-nonnegative-ℤ (int-ℕ n)
is-nonnegative-int-ℕ zero-ℕ = star
is-nonnegative-int-ℕ (succ-ℕ n) = star
```

### The canonical equivalence between natural numbers and nonnegative integers

```agda
nonnegative-int-ℕ : ℕ → nonnegative-ℤ
nonnegative-int-ℕ n = int-ℕ n , is-nonnegative-int-ℕ n

nat-nonnegative-ℤ : nonnegative-ℤ → ℕ
nat-nonnegative-ℤ (inr (inl x) , H) = zero-ℕ
nat-nonnegative-ℤ (inr (inr x) , H) = succ-ℕ x

eq-nat-nonnegative-succ-nonnnegative-ℤ :
  (x : nonnegative-ℤ) →
  nat-nonnegative-ℤ (succ-nonnegative-ℤ x) ＝ succ-ℕ (nat-nonnegative-ℤ x)
eq-nat-nonnegative-succ-nonnnegative-ℤ (inr (inl x) , H) = refl
eq-nat-nonnegative-succ-nonnnegative-ℤ (inr (inr x) , H) = refl

is-section-nat-nonnegative-ℤ :
  (x : nonnegative-ℤ) → nonnegative-int-ℕ (nat-nonnegative-ℤ x) ＝ x
is-section-nat-nonnegative-ℤ ((inr (inl star)) , H) = refl
is-section-nat-nonnegative-ℤ ((inr (inr x)) , H) = refl

is-retraction-nat-nonnegative-ℤ :
  (n : ℕ) → nat-nonnegative-ℤ (nonnegative-int-ℕ n) ＝ n
is-retraction-nat-nonnegative-ℤ zero-ℕ = refl
is-retraction-nat-nonnegative-ℤ (succ-ℕ n) = refl

is-equiv-nat-nonnegative-ℤ : is-equiv nat-nonnegative-ℤ
pr1 (pr1 is-equiv-nat-nonnegative-ℤ) = nonnegative-int-ℕ
pr2 (pr1 is-equiv-nat-nonnegative-ℤ) = is-retraction-nat-nonnegative-ℤ
pr1 (pr2 is-equiv-nat-nonnegative-ℤ) = nonnegative-int-ℕ
pr2 (pr2 is-equiv-nat-nonnegative-ℤ) = is-section-nat-nonnegative-ℤ

is-equiv-nonnegative-int-ℕ : is-equiv nonnegative-int-ℕ
pr1 (pr1 is-equiv-nonnegative-int-ℕ) = nat-nonnegative-ℤ
pr2 (pr1 is-equiv-nonnegative-int-ℕ) = is-section-nat-nonnegative-ℤ
pr1 (pr2 is-equiv-nonnegative-int-ℕ) = nat-nonnegative-ℤ
pr2 (pr2 is-equiv-nonnegative-int-ℕ) = is-retraction-nat-nonnegative-ℤ

equiv-nonnegative-int-ℕ : ℕ ≃ nonnegative-ℤ
pr1 equiv-nonnegative-int-ℕ = nonnegative-int-ℕ
pr2 equiv-nonnegative-int-ℕ = is-equiv-nonnegative-int-ℕ
```

## See also

- The relations between nonnegative and positive, negative and nonpositive
  integers are derived in
  [`positive-and-negative-integers`](elementary-number-theory.positive-and-negative-integers.md)
