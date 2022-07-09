---
title: Subgroups of concrete groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.subgroups-concrete-groups where

open import foundation.0-maps
open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.faithful-maps
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.concrete-group-actions
open import group-theory.concrete-groups
open import group-theory.orbits-concrete-group-actions
open import group-theory.transitive-concrete-group-actions

open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
```

## Idea

A subgroup of a concrete group `G` is a pointed transitive `G`-set.

## Definition

```agda
subgroup-action-Concrete-Group :
  {l1 : Level} (l2 : Level) (G : Concrete-Group l1) →
  classifying-type-Concrete-Group G → UU (l1 ⊔ lsuc l2)
subgroup-action-Concrete-Group l2 G u =
  Σ ( transitive-action-Concrete-Group l2 G)
    ( λ X → type-Set (action-transitive-action-Concrete-Group G X u))

subgroup-Concrete-Group :
  {l1 : Level} (l2 : Level) (G : Concrete-Group l1) → UU (l1 ⊔ lsuc l2)
subgroup-Concrete-Group l2 G =
  subgroup-action-Concrete-Group l2 G (shape-Concrete-Group G)

module _
  {l1 l2 : Level} (G : Concrete-Group l1) (H : subgroup-Concrete-Group l2 G)
  where

  transitive-action-subgroup-Concrete-Group :
    transitive-action-Concrete-Group l2 G
  transitive-action-subgroup-Concrete-Group = pr1 H

  action-subgroup-Concrete-Group : action-Concrete-Group l2 G
  action-subgroup-Concrete-Group =
    action-transitive-action-Concrete-Group G
      transitive-action-subgroup-Concrete-Group

  coset-subgroup-Concrete-Group : UU-Set l2
  coset-subgroup-Concrete-Group =
    action-subgroup-Concrete-Group (shape-Concrete-Group G)

  type-coset-subgroup-Concrete-Group : UU l2
  type-coset-subgroup-Concrete-Group = type-Set coset-subgroup-Concrete-Group

  is-transitive-action-subgroup-Concrete-Group :
    is-transitive-action-Concrete-Group G action-subgroup-Concrete-Group
  is-transitive-action-subgroup-Concrete-Group =
    is-transitive-transitive-action-Concrete-Group G
      transitive-action-subgroup-Concrete-Group

  classifying-type-subgroup-Concrete-Group : UU (l1 ⊔ l2)
  classifying-type-subgroup-Concrete-Group =
    orbit-action-Concrete-Group G action-subgroup-Concrete-Group

  shape-subgroup-Concrete-Group : classifying-type-subgroup-Concrete-Group
  pr1 shape-subgroup-Concrete-Group = shape-Concrete-Group G
  pr2 shape-subgroup-Concrete-Group = pr2 H

  classifying-pointed-type-subgroup-Concrete-Group : Pointed-Type (l1 ⊔ l2)
  pr1 classifying-pointed-type-subgroup-Concrete-Group =
    classifying-type-subgroup-Concrete-Group
  pr2 classifying-pointed-type-subgroup-Concrete-Group =
    shape-subgroup-Concrete-Group

  is-connected-classifying-type-subgroup-Concrete-Group :
    is-path-connected classifying-type-subgroup-Concrete-Group
  is-connected-classifying-type-subgroup-Concrete-Group =
    is-transitive-action-subgroup-Concrete-Group

  classifying-inclusion-subgroup-Concrete-Group :
    classifying-type-subgroup-Concrete-Group →
    classifying-type-Concrete-Group G
  classifying-inclusion-subgroup-Concrete-Group = pr1

  preserves-shape-classifying-inclusion-subgroup-Concrete-Group :
    classifying-inclusion-subgroup-Concrete-Group
      shape-subgroup-Concrete-Group ＝
    shape-Concrete-Group G
  preserves-shape-classifying-inclusion-subgroup-Concrete-Group = refl

  classifying-pointed-inclusion-subgroup-Concrete-Group :
    classifying-pointed-type-subgroup-Concrete-Group →*
    classifying-pointed-type-Concrete-Group G
  pr1 classifying-pointed-inclusion-subgroup-Concrete-Group =
    classifying-inclusion-subgroup-Concrete-Group
  pr2 classifying-pointed-inclusion-subgroup-Concrete-Group =
    preserves-shape-classifying-inclusion-subgroup-Concrete-Group

  is-0-map-classifying-inclusion-subgroup-Concrete-Group :
    is-0-map classifying-inclusion-subgroup-Concrete-Group
  is-0-map-classifying-inclusion-subgroup-Concrete-Group =
    is-0-map-pr1 (λ u → is-set-type-Set (action-subgroup-Concrete-Group u))

  is-faithful-classifying-inclusion-subgroup-Concrete-Group :
    is-faithful classifying-inclusion-subgroup-Concrete-Group
  is-faithful-classifying-inclusion-subgroup-Concrete-Group =
    is-faithful-is-0-map is-0-map-classifying-inclusion-subgroup-Concrete-Group

  type-subgroup-Concrete-Group : UU (l1 ⊔ l2)
  type-subgroup-Concrete-Group =
    type-Ω classifying-pointed-type-subgroup-Concrete-Group

  concrete-group-subgroup-Concrete-Group :
    Concrete-Group (l1 ⊔ l2)
  pr1 (pr1 concrete-group-subgroup-Concrete-Group) =
    classifying-pointed-type-subgroup-Concrete-Group
  pr2 (pr1 concrete-group-subgroup-Concrete-Group) =
    is-connected-classifying-type-subgroup-Concrete-Group
  pr2 concrete-group-subgroup-Concrete-Group =
    is-set-is-emb
      ( map-Ω
        ( classifying-pointed-type-subgroup-Concrete-Group)
        ( classifying-pointed-type-Concrete-Group G)
        ( classifying-pointed-inclusion-subgroup-Concrete-Group))
      ( is-emb-map-Ω
        ( classifying-pointed-type-subgroup-Concrete-Group)
        ( classifying-pointed-type-Concrete-Group G)
        ( classifying-pointed-inclusion-subgroup-Concrete-Group)
        ( is-faithful-classifying-inclusion-subgroup-Concrete-Group))
      ( is-set-type-Concrete-Group G)

  hom-inclusion-subgroup-Concrete-Group :
    hom-Concrete-Group concrete-group-subgroup-Concrete-Group G
  pr1 hom-inclusion-subgroup-Concrete-Group =
    classifying-inclusion-subgroup-Concrete-Group
  pr2 hom-inclusion-subgroup-Concrete-Group =
    preserves-shape-classifying-inclusion-subgroup-Concrete-Group
```
