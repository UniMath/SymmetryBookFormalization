---
title: Bounded sums of arithmetic functions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.bounded-sums-arithmetic-functions where

open import elementary-number-theory.arithmetic-functions using
  ( type-arithmetic-functions-Ring)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
open import elementary-number-theory.nonzero-natural-numbers using
  ( nonzero-ℕ; succ-nonzero-ℕ; one-nonzero-ℕ)

open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-propositions using
  ( decidable-Prop; type-decidable-Prop; is-decidable-type-decidable-Prop)
open import foundation.decidable-types using (is-decidable)
open import foundation.functions using (_∘_)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import ring-theory.rings using (Ring; type-Ring; zero-Ring; add-Ring)
```

## Idea

Given a decidable predicate `P` on the nonzero natural numbers, and a map `f` from the nonzero natural numbers in `P` into a ring `R`, the bounded sum is a summation of the values of `f` up to an upper bound `b`.

## Definition

```agda
module _
  {l : Level} (R : Ring l)
  where

  restricted-arithmetic-function-Ring :
    {l' : Level} (P : nonzero-ℕ → decidable-Prop l') → UU (l ⊔ l')
  restricted-arithmetic-function-Ring P =
    (x : nonzero-ℕ) → type-decidable-Prop (P x) → type-Ring R

  shift-arithmetic-function-Ring :
    type-arithmetic-functions-Ring R → type-arithmetic-functions-Ring R
  shift-arithmetic-function-Ring f = f ∘ succ-nonzero-ℕ

  shift-restricted-arithmetic-function-Ring :
    {l' : Level} (P : nonzero-ℕ → decidable-Prop l') →
    restricted-arithmetic-function-Ring P →
    restricted-arithmetic-function-Ring (P ∘ succ-nonzero-ℕ)
  shift-restricted-arithmetic-function-Ring P f = f ∘ succ-nonzero-ℕ

  case-one-bounded-sum-arithmetic-function-Ring :
    {l' : Level} → (P : decidable-Prop l') →
    is-decidable (type-decidable-Prop P) →
    (type-decidable-Prop P → type-Ring R) → type-Ring R
  case-one-bounded-sum-arithmetic-function-Ring P (inl x) f = f x
  case-one-bounded-sum-arithmetic-function-Ring P (inr x) f =
    zero-Ring R

  bounded-sum-arithmetic-function-Ring :
    (b : ℕ) {l' : Level} (P : nonzero-ℕ → decidable-Prop l')
    (f : restricted-arithmetic-function-Ring P) → type-Ring R
  bounded-sum-arithmetic-function-Ring zero-ℕ P f = zero-Ring R
  bounded-sum-arithmetic-function-Ring (succ-ℕ zero-ℕ) P f =
    case-one-bounded-sum-arithmetic-function-Ring
      ( P one-nonzero-ℕ)
      ( is-decidable-type-decidable-Prop (P one-nonzero-ℕ))
      ( f one-nonzero-ℕ)
  bounded-sum-arithmetic-function-Ring (succ-ℕ (succ-ℕ b)) P f =
    add-Ring R
      ( case-one-bounded-sum-arithmetic-function-Ring
        ( P one-nonzero-ℕ)
        ( is-decidable-type-decidable-Prop (P one-nonzero-ℕ))
        ( f one-nonzero-ℕ))
      ( bounded-sum-arithmetic-function-Ring
        ( succ-ℕ b)
        ( P ∘ succ-nonzero-ℕ)
        ( f ∘ succ-nonzero-ℕ))
```
