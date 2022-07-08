---
title: Binary equivalences
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.binary-equivalences where

open import foundation-core.cartesian-product-types using (_×_)
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.embeddings using (is-emb)
open import foundation-core.equivalences using (is-equiv; is-emb-is-equiv)
open import foundation-core.universe-levels using (Level; UU; _⊔_)
```

## Idea

A binary operation `f : A → B → C` is said to be a binary equivalence if the functions `λ x → f x b` and `λ y → f a y` are equivalences for each `a : A` and `b : B` respectively.

```agda
{- Binary equivalences and binary embeddings -}

fix-left :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  A → B → C
fix-left f a = f a

fix-right :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  B → A → C
fix-right f b a = f a b

is-binary-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (A → B → C) → UU (l1 ⊔ l2 ⊔ l3)
is-binary-equiv {A = A} {B = B} f =
  ((b : B) → is-equiv (fix-right f b)) × ((a : A) → is-equiv (fix-left f a))

is-equiv-fix-left :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  is-binary-equiv f → {a : A} → is-equiv (fix-left f a)
is-equiv-fix-left f H {a} = pr2 H a

is-equiv-fix-right :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  is-binary-equiv f → {b : B} → is-equiv (fix-right f b)
is-equiv-fix-right f H {b} = pr1 H b
```
