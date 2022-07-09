---
title: Embeddings of groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.embeddings-groups where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)

open import group-theory.homomorphisms-groups using
  ( type-hom-Group; map-hom-Group)
open import group-theory.groups using (Group; type-Group)
open import group-theory.subgroups using
  ( Subgroup; group-Subgroup; inclusion-group-Subgroup;
    is-emb-inclusion-group-Subgroup)
```

## Idea

Embeddings of groups are group homomorphisms of which the underlying map is an embedding

## Definitions

### Embeddings of groups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  is-emb-hom-Group : (type-hom-Group G H) → UU (l1 ⊔ l2)
  is-emb-hom-Group h = is-emb (map-hom-Group G H h)

  emb-Group : UU (l1 ⊔ l2)
  emb-Group = Σ (type-hom-Group G H) is-emb-hom-Group

  hom-emb-Group : emb-Group → type-hom-Group G H
  hom-emb-Group = pr1

  map-emb-hom-Group : emb-Group → type-Group G → type-Group H
  map-emb-hom-Group f = map-hom-Group G H (hom-emb-Group f)

  is-emb-map-emb-hom-Group : (f : emb-Group) → is-emb (map-emb-hom-Group f)
  is-emb-map-emb-hom-Group = pr2
```

### The type of all embeddings into a group

```agda
emb-Group-Slice :
  (l : Level) {l1 : Level} (G : Group l1) → UU ((lsuc l) ⊔ l1)
emb-Group-Slice l G =
  Σ ( Group l) (λ H → emb-Group H G)

emb-group-slice-Subgroup :
  { l1 l2 : Level} (G : Group l1) →
  Subgroup l2 G → emb-Group-Slice (l1 ⊔ l2) G
emb-group-slice-Subgroup G P =
  pair
    ( group-Subgroup G P)
    ( pair
      ( inclusion-group-Subgroup G P)
      ( is-emb-inclusion-group-Subgroup G P))
```

