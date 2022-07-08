---
title: Alkanes
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module organic-chemistry.alkanes where

open import foundation.universe-levels

open import organic-chemistry.saturated-carbons
open import organic-chemistry.hydrocarbons
```

## Idea

An **alkane** is a hydrocarbon that only has saturated carbons, i.e., it does not have any double or triple carbon-carbon bonds.

## Definition

```agda
is-alkane-hydrocarbon : hydrocarbon → UU
is-alkane-hydrocarbon H = ∀ c → is-saturated-carbon-hydrocarbon H c
```
