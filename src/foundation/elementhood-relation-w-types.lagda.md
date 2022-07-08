---
title: The elementhood relation on W-types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.elementhood-relation-w-types where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using (is-empty)
open import foundation.fibers-of-maps using (fib)
open import foundation.identity-types using (tr; inv; refl)
open import foundation.universe-levels using (Level; UU; _⊔_)
open import foundation.w-types using (𝕎; component-𝕎; tree-𝕎)
```

## Idea

We say that a tree `S` is an element of a tree `tree-𝕎 x α` if `S` can be equipped with an element `y : B x` such that `α y = S`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  _∈-𝕎_ : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  x ∈-𝕎 y = fib (component-𝕎 y) x

  _∉-𝕎_ : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  x ∉-𝕎 y = is-empty (x ∈-𝕎 y)
```

## Properties

```agda
irreflexive-∈-𝕎 :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (x : 𝕎 A B) → x ∉-𝕎 x
irreflexive-∈-𝕎 {A = A} {B = B} (tree-𝕎 x α) (pair y p) =
  irreflexive-∈-𝕎 (α y) (tr (λ z → (α y) ∈-𝕎 z) (inv p) (pair y refl))
```
