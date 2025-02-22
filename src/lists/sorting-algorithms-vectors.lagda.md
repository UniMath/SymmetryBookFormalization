# Sorting algorithms for vectors

```agda
module lists.sorting-algorithms-vectors where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
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
  {l1 l2 : Level}
  (X : Decidable-Total-Order l1 l2)
  (f :
      {n : ℕ} →
      vec (type-Decidable-Total-Order X) n →
      vec (type-Decidable-Total-Order X) n)
  where

  is-sort-vec :
    UU (l1 ⊔ l2)
  is-sort-vec =
    (n : ℕ) →
    is-permutation-vec n f ×
    ((v : vec (type-Decidable-Total-Order X) n) → is-sorted-vec X (f v))

  is-permutation-vec-is-sort-vec :
    is-sort-vec → (n : ℕ) → is-permutation-vec n f
  is-permutation-vec-is-sort-vec S n = pr1 (S n)

  permutation-vec-is-sort-vec :
    is-sort-vec → (n : ℕ) → vec (type-Decidable-Total-Order X) n → permutation n
  permutation-vec-is-sort-vec S n v =
    permutation-is-permutation-vec n f (is-permutation-vec-is-sort-vec S n) v

  eq-permute-vec-permutation-is-sort-vec :
    (S : is-sort-vec) (n : ℕ) (v : vec (type-Decidable-Total-Order X) n) →
    f v ＝ permute-vec n v (permutation-vec-is-sort-vec S n v)
  eq-permute-vec-permutation-is-sort-vec S n v =
    eq-permute-vec-permutation-is-permutation-vec
      ( n)
      ( f)
      ( is-permutation-vec-is-sort-vec S n) v

  is-sorting-vec-is-sort-vec :
    is-sort-vec → (n : ℕ) →
    (v : vec (type-Decidable-Total-Order X) n) → is-sorted-vec X (f v)
  is-sorting-vec-is-sort-vec S n = pr2 (S n)
```
