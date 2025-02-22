# Sorted vectors

```agda
module lists.sorted-vectors where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors

open import lists.permutation-vectors

open import order-theory.decidable-total-orders

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We define a sorted vector to be a vector such that for every pair of consecutive
elements `x` and `y`, the inequality `x ≤ y` holds.

## Definitions

### The proposition that a vector is sorted

```agda
module _
  {l1 l2 : Level} (X : Decidable-Total-Order l1 l2)
  where

  is-sorted-vec-Prop :
    {n : ℕ} → vec (type-Decidable-Total-Order X) n → Prop l2
  is-sorted-vec-Prop {0} v = raise-unit-Prop l2
  is-sorted-vec-Prop {1} v = raise-unit-Prop l2
  is-sorted-vec-Prop {succ-ℕ (succ-ℕ n)} (x ∷ y ∷ v) =
    product-Prop
      ( leq-Decidable-Total-Order-Prop X x y)
      ( is-sorted-vec-Prop (y ∷ v))

  is-sorted-vec :
    {n : ℕ} → vec (type-Decidable-Total-Order X) n → UU l2
  is-sorted-vec l = type-Prop (is-sorted-vec-Prop l)
```

### The proposition that an element is less than or equal to every element in a vector

```agda
  is-least-element-vec-Prop :
    {n : ℕ} → type-Decidable-Total-Order X →
    vec (type-Decidable-Total-Order X) n → Prop l2
  is-least-element-vec-Prop {0} x v = raise-unit-Prop l2
  is-least-element-vec-Prop {succ-ℕ n} x (y ∷ v) =
    product-Prop
      ( leq-Decidable-Total-Order-Prop X x y)
      ( is-least-element-vec-Prop x v)

  is-least-element-vec :
    {n : ℕ} → type-Decidable-Total-Order X →
    vec (type-Decidable-Total-Order X) n → UU l2
  is-least-element-vec x v = type-Prop (is-least-element-vec-Prop x v)
```

## Properties

### If a vector is sorted, then its tail is also sorted

```agda
  is-sorted-tail-is-sorted-vec :
    {n : ℕ} →
    (v : vec (type-Decidable-Total-Order X) (succ-ℕ n)) →
    is-sorted-vec v → is-sorted-vec (tail-vec v)
  is-sorted-tail-is-sorted-vec {zero-ℕ} (x ∷ empty-vec) s = raise-star
  is-sorted-tail-is-sorted-vec {succ-ℕ n} (x ∷ y ∷ v) s = pr2 s

  is-leq-head-head-tail-is-sorted-vec :
    {n : ℕ} → (v : vec (type-Decidable-Total-Order X) (succ-ℕ (succ-ℕ n))) →
    is-sorted-vec v →
    leq-Decidable-Total-Order X (head-vec v) (head-vec (tail-vec v))
  is-leq-head-head-tail-is-sorted-vec (x ∷ y ∷ v) s = pr1 s
```

### If a vector `v' ＝ y ∷ v` is sorted then for all elements `x` less than or equal to `y`, `x` is less than or equal to every element in the vector

```agda
  is-least-element-vec-is-leq-head-sorted-vec :
    {n : ℕ}
    (x : type-Decidable-Total-Order X)
    (v : vec (type-Decidable-Total-Order X) (succ-ℕ n)) →
    is-sorted-vec v → leq-Decidable-Total-Order X x (head-vec v) →
    is-least-element-vec x v
  is-least-element-vec-is-leq-head-sorted-vec {zero-ℕ} x (y ∷ v) s p =
    p , raise-star
  is-least-element-vec-is-leq-head-sorted-vec {succ-ℕ n} x (y ∷ v) s p =
    p ,
    ( is-least-element-vec-is-leq-head-sorted-vec
      ( x)
      ( v)
      ( is-sorted-tail-is-sorted-vec (y ∷ v) s)
      ( transitive-leq-Decidable-Total-Order
        ( X)
        ( x)
        ( y)
        ( head-vec v)
        ( is-leq-head-head-tail-is-sorted-vec (y ∷ v) s)
        ( p)))
```

### An equivalent definition of being sorted

```agda
  is-sorted-least-element-vec-Prop :
    {n : ℕ} → vec (type-Decidable-Total-Order X) n → Prop l2
  is-sorted-least-element-vec-Prop {0} v = raise-unit-Prop l2
  is-sorted-least-element-vec-Prop {1} v = raise-unit-Prop l2
  is-sorted-least-element-vec-Prop {succ-ℕ (succ-ℕ n)} (x ∷ v) =
    product-Prop
      ( is-least-element-vec-Prop x v)
      ( is-sorted-least-element-vec-Prop v)

  is-sorted-least-element-vec :
    {n : ℕ} → vec (type-Decidable-Total-Order X) n → UU l2
  is-sorted-least-element-vec v =
    type-Prop (is-sorted-least-element-vec-Prop v)

  is-sorted-least-element-vec-is-sorted-vec :
    {n : ℕ}
    (v : vec (type-Decidable-Total-Order X) n) →
    is-sorted-vec v → is-sorted-least-element-vec v
  is-sorted-least-element-vec-is-sorted-vec {0} v x = raise-star
  is-sorted-least-element-vec-is-sorted-vec {1} v x = raise-star
  is-sorted-least-element-vec-is-sorted-vec
    {succ-ℕ (succ-ℕ n)}
    ( x ∷ y ∷ v)
    ( p , q) =
    is-least-element-vec-is-leq-head-sorted-vec x (y ∷ v) q p ,
    is-sorted-least-element-vec-is-sorted-vec (y ∷ v) q

  is-sorted-vec-is-sorted-least-element-vec :
    {n : ℕ}
    (v : vec (type-Decidable-Total-Order X) n) →
    is-sorted-least-element-vec v →
    is-sorted-vec v
  is-sorted-vec-is-sorted-least-element-vec {0} v x = raise-star
  is-sorted-vec-is-sorted-least-element-vec {1} v x = raise-star
  is-sorted-vec-is-sorted-least-element-vec
    {succ-ℕ (succ-ℕ n)}
    (x ∷ y ∷ v)
    (p , q) =
    ( pr1 p) ,
    ( is-sorted-vec-is-sorted-least-element-vec (y ∷ v) q)
```

### If the tail of a vector `v` is sorted and `x ≤ head-vec v`, then `v` is sorted

```agda
  is-sorted-vec-is-sorted-tail-is-leq-head-vec :
    {n : ℕ}
    (v : vec (type-Decidable-Total-Order X) (succ-ℕ (succ-ℕ n))) →
    is-sorted-vec (tail-vec v) →
    (leq-Decidable-Total-Order X (head-vec v) (head-vec (tail-vec v))) →
    is-sorted-vec v
  is-sorted-vec-is-sorted-tail-is-leq-head-vec (x ∷ y ∷ v) s p = p , s
```

### If an element `x` is less than or equal to every element of a vector `v`, then it is less than or equal to every element of every permutation of `v`

```agda
  is-least-element-functional-vec-Prop :
    (n : ℕ)
    (x : type-Decidable-Total-Order X)
    (fv : functional-vec (type-Decidable-Total-Order X) n) →
    Prop l2
  is-least-element-functional-vec-Prop n x fv =
    Π-Prop (Fin n) (λ k → leq-Decidable-Total-Order-Prop X x (fv k))

  is-least-element-functional-vec :
    (n : ℕ)
    (x : type-Decidable-Total-Order X)
    (fv : functional-vec (type-Decidable-Total-Order X) n) →
    UU l2
  is-least-element-functional-vec n x fv =
    type-Prop (is-least-element-functional-vec-Prop n x fv)

  is-least-element-permute-functional-vec :
    (n : ℕ)
    (x : type-Decidable-Total-Order X)
    (fv : functional-vec (type-Decidable-Total-Order X) n)
    (a : permutation n) →
    is-least-element-functional-vec n x fv →
    is-least-element-functional-vec n x (fv ∘ map-equiv a)
  is-least-element-permute-functional-vec n x fv a p k =
    p (map-equiv a k)

  is-least-element-vec-is-least-element-functional-vec :
    (n : ℕ)
    (x : type-Decidable-Total-Order X)
    (fv : functional-vec (type-Decidable-Total-Order X) n) →
    is-least-element-functional-vec n x fv →
    is-least-element-vec x (listed-vec-functional-vec n fv)
  is-least-element-vec-is-least-element-functional-vec 0 x fv p = raise-star
  is-least-element-vec-is-least-element-functional-vec (succ-ℕ n) x fv p =
    (p (inr star)) ,
    ( is-least-element-vec-is-least-element-functional-vec
      ( n)
      ( x)
      ( tail-functional-vec n fv)
      ( p ∘ inl))

  is-least-element-functional-vec-is-least-element-vec :
    (n : ℕ)
    (x : type-Decidable-Total-Order X)
    (v : vec (type-Decidable-Total-Order X) n) →
    is-least-element-vec x v →
    is-least-element-functional-vec n x (functional-vec-vec n v)
  is-least-element-functional-vec-is-least-element-vec
    ( succ-ℕ n)
    ( x)
    ( y ∷ v)
    ( p , q)
    ( inl k) =
    is-least-element-functional-vec-is-least-element-vec n x v q k
  is-least-element-functional-vec-is-least-element-vec
    ( succ-ℕ n)
    ( x)
    ( y ∷ v)
    ( p , q)
    ( inr star) =
    p

  is-least-element-permute-vec :
    {n : ℕ}
    (x : type-Decidable-Total-Order X)
    (v : vec (type-Decidable-Total-Order X) n)
    (a : permutation n) →
    is-least-element-vec x v →
    is-least-element-vec x (permute-vec n v a)
  is-least-element-permute-vec {n} x v a p =
    is-least-element-vec-is-least-element-functional-vec
      ( n)
      ( x)
      ( functional-vec-vec n v ∘ map-equiv a)
      ( is-least-element-permute-functional-vec
        ( n)
        ( x)
        ( functional-vec-vec n v)
        ( a)
        ( is-least-element-functional-vec-is-least-element-vec n x v p))
```
