# Sorting algorithms for vectors

```agda
module lists.sorting-algorithms-vectors where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.universe-levels

open import linear-algebra.vectors

open import lists.permutation-vectors
open import lists.sorted-vectors

open import order-theory.decidable-total-orders
```

</details>

## Idea

A function `f` on vectors is a **sort** if `f` is a permutation and if for every
vector `v`, `f v` is sorted.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Decidable-Total-Order l1 l2)
  where

  is-sort-vec :
    (f :
      {n : ℕ} →
      vec (type-Decidable-Total-Order X) n →
      vec (type-Decidable-Total-Order X) n) →
    UU (l1 ⊔ l2)
  is-sort-vec f =
    (n : ℕ) →
    is-permutation-vec n f ×
    ((v : vec (type-Decidable-Total-Order X) n) → is-sorted-vec X (f v))
```
