# Sort by insertion for lists

```agda
module lists.sort-by-insertion-lists where
```

<details><summary>Imports</summary>

```agda
open import finite-group-theory.permutations-standard-finite-types

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.vectors


open import lists.arrays
open import lists.lists
open import lists.permutation-lists
open import lists.sort-by-insertion-vectors
open import lists.sorted-lists
open import lists.sorting-algorithms-lists

open import order-theory.decidable-total-orders
```

</details>

## Idea

We use the definition of sort by insertion for vectors
([`lists.sort-by-insertion-vectors`](lists.sort-by-insertion-vectors.md)) and we
adapt it for lists.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Decidable-Total-Order l1 l2)
  where

  insertion-sort-list :
    list (type-Decidable-Total-Order X) → list (type-Decidable-Total-Order X)
  insertion-sort-list l =
    list-vec (length-list l) (insertion-sort-vec X (vec-list l))
```

## Properties

### Sort by insertion is a sort

```agda
  is-sort-insertion-sort-list :
    is-sort-list X insertion-sort-list
  is-sort-insertion-sort-list =
    is-sort-list-is-sort-vec
      ( X)
      ( insertion-sort-vec X)
      ( is-sort-insertion-sort-vec X)

  is-permutation-insertion-sort-list : is-permutation-list insertion-sort-list
  is-permutation-insertion-sort-list = pr1 (is-sort-insertion-sort-list)

  permutation-insertion-sort-list :
    (l : list (type-Decidable-Total-Order X)) →
    permutation (length-list l)
  permutation-insertion-sort-list =
    permutation-list-is-sort-list
      X
      insertion-sort-list
      is-sort-insertion-sort-list

  eq-permute-list-permutation-insertion-sort-list :
    (l : list (type-Decidable-Total-Order X)) →
    insertion-sort-list l ＝ permute-list l (permutation-insertion-sort-list l)
  eq-permute-list-permutation-insertion-sort-list =
    eq-permute-list-permutation-is-sort-list
      X
      insertion-sort-list
      is-sort-insertion-sort-list

  is-sorting-insertion-sort-list :
    (l : list (type-Decidable-Total-Order X)) →
    is-sorted-list X (insertion-sort-list l)
  is-sorting-insertion-sort-list = pr2 (is-sort-insertion-sort-list)
```
