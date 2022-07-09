---
title: Examples of higher groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.examples-higher-groups where

open import foundation.connected-components-universes
open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.mere-equivalences
open import foundation.universe-levels

open import group-theory.higher-groups

open import structured-types.pointed-types

open import synthetic-homotopy-theory.circle
```

```agda
module _
  where

  classifying-type-ℤ-∞-Group : UU lzero
  classifying-type-ℤ-∞-Group = 𝕊¹

  shape-ℤ-∞-Group : 𝕊¹
  shape-ℤ-∞-Group = base-𝕊¹

  classifying-pointed-type-ℤ-∞-Group : Pointed-Type lzero
  classifying-pointed-type-ℤ-∞-Group =
    pair
      classifying-type-ℤ-∞-Group
      shape-ℤ-∞-Group

  ℤ-∞-Group : ∞-Group lzero
  ℤ-∞-Group =
    pair
      classifying-pointed-type-ℤ-∞-Group
      is-path-connected-𝕊¹

module _
  {l : Level} (X : UU l)
  where

  classifying-type-symmetric-∞-Group : UU (lsuc l)
  classifying-type-symmetric-∞-Group = component-UU X

  shape-symmetric-∞-Group : classifying-type-symmetric-∞-Group
  shape-symmetric-∞-Group =
    pair X (refl-mere-equiv X)

  classifying-pointed-type-symmetric-∞-Group : Pointed-Type (lsuc l)
  classifying-pointed-type-symmetric-∞-Group =
    pair
      classifying-type-symmetric-∞-Group
      shape-symmetric-∞-Group

  is-path-connected-classifying-type-symmetric-∞-Group :
    is-path-connected classifying-type-symmetric-∞-Group
  is-path-connected-classifying-type-symmetric-∞-Group =
    is-path-connected-component-UU X
  
  symmetric-∞-Group : ∞-Group (lsuc l)
  symmetric-∞-Group =
    pair
      classifying-pointed-type-symmetric-∞-Group
      is-path-connected-classifying-type-symmetric-∞-Group
```
