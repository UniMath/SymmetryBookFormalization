---
title: 2-Types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.2-types where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.truncated-types using
  ( is-trunc; truncated-type-succ-Truncated-Type)
open import foundation.truncation-levels using (two-𝕋)
open import foundation.universe-levels using (Level; UU; lsuc)
```

## Definition

A 2-type is a type that is 2-truncated

```
is-2-type : {l : Level} → UU l → UU l
is-2-type = is-trunc (two-𝕋)

UU-2-Type : (l : Level) → UU (lsuc l)
UU-2-Type l = Σ (UU l) is-2-type

type-2-Type :
  {l : Level} → UU-2-Type l → UU l
type-2-Type = pr1

abstract
  is-2-type-type-2-Type :
    {l : Level} (A : UU-2-Type l) → is-2-type (type-2-Type A)
  is-2-type-type-2-Type = pr2
```
