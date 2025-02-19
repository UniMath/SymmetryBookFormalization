# Arrays

```agda
module lists.arrays where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors

open import lists.elementhood-relation-lists
open import lists.lists

open import univalent-combinatorics.involution-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

An {{#concept "array" Agda=array}} is a pair consisting of a [natural number](elementary-number-theory.natural-numbers.md) `n`, and a [functional vector](linear-algebra.vectors.md) of `n` elements of `A`. The concept of array is [equivalent](foundation-core.equivalences.md) to the concept of [list](lists.lists.md).

## Definitions

### Arrays

```agda
array : {l : Level} → UU l → UU l
array A = Σ ℕ (λ n → functional-vec A n)

module _
  {l : Level} {A : UU l}
  where

  length-array : array A → ℕ
  length-array = pr1

  functional-vec-array : (t : array A) → Fin (length-array t) → A
  functional-vec-array = pr2

  empty-array : array A
  pr1 (empty-array) = zero-ℕ
  pr2 (empty-array) ()

  is-empty-array-Prop : array A → Prop lzero
  is-empty-array-Prop (zero-ℕ , t) = unit-Prop
  is-empty-array-Prop (succ-ℕ n , t) = empty-Prop

  is-empty-array : array A → UU lzero
  is-empty-array = type-Prop ∘ is-empty-array-Prop

  is-nonempty-array-Prop : array A → Prop lzero
  is-nonempty-array-Prop (zero-ℕ , t) = empty-Prop
  is-nonempty-array-Prop (succ-ℕ n , t) = unit-Prop

  is-nonempty-array : array A → UU lzero
  is-nonempty-array = type-Prop ∘ is-nonempty-array-Prop

  head-array : (t : array A) → is-nonempty-array t → A
  head-array (succ-ℕ n , f) _ = f (inr star)

  tail-array : (t : array A) → is-nonempty-array t → array A
  tail-array (succ-ℕ n , f) _ = n , f ∘ inl

  cons-array : A → array A → array A
  cons-array a t =
    ( succ-ℕ (length-array t) ,
      rec-coproduct (functional-vec-array t) (λ _ → a))

  revert-array : array A → array A
  revert-array (n , t) = (n , λ k → t (opposite-Fin n k))
```

## Properties

```agda
module _
  {l : Level} {A : UU l}
  where

  list-array : array A → list A
  list-array (n , t) = list-vec n (listed-vec-functional-vec n t)

  array-list : list A → array A
  array-list l =
    ( length-list l , functional-vec-vec (length-list l) (vec-list l))

  is-section-array-list : (list-array ∘ array-list) ~ id
  is-section-array-list nil = refl
  is-section-array-list (cons x l) = ap (cons x) (is-section-array-list l)

  is-retraction-array-list : (array-list ∘ list-array) ~ id
  is-retraction-array-list (n , t) =
    ap
      ( λ (n , v) → (n , functional-vec-vec n v))
      ( is-retraction-vec-list (n , listed-vec-functional-vec n t)) ∙
    eq-pair-eq-fiber (is-retraction-functional-vec-vec n t)

  equiv-list-array : array A ≃ list A
  pr1 equiv-list-array = list-array
  pr2 equiv-list-array =
    is-equiv-is-invertible
      array-list
      is-section-array-list
      is-retraction-array-list

  equiv-array-list : list A ≃ array A
  pr1 equiv-array-list = array-list
  pr2 equiv-array-list =
    is-equiv-is-invertible
      list-array
      is-retraction-array-list
      is-section-array-list
```

### Computational rules of the equivalence between arrays and lists

```agda
  compute-length-list-list-vec :
    (n : ℕ) (v : vec A n) →
    length-list (list-vec n v) ＝ n
  compute-length-list-list-vec zero-ℕ v = refl
  compute-length-list-list-vec (succ-ℕ n) (x ∷ v) =
    ap succ-ℕ (compute-length-list-list-vec n v)

  compute-length-list-list-array :
    (t : array A) → length-list (list-array t) ＝ length-array t
  compute-length-list-list-array t =
    compute-length-list-list-vec
      ( length-array t)
      ( listed-vec-functional-vec (length-array t) (functional-vec-array t))
```

### An element `x` is in a vector `v` iff it is in `list-vec n v`

```agda
  is-in-list-is-in-vec-list :
    (l : list A) (x : A) →
    x ∈-vec (vec-list l) → x ∈-list l
  is-in-list-is-in-vec-list (cons y l) .y (is-head .y .(vec-list l)) =
    is-head y l
  is-in-list-is-in-vec-list (cons y l) x (is-in-tail .x .y .(vec-list l) I) =
    is-in-tail x y l (is-in-list-is-in-vec-list l x I)

  is-in-vec-list-is-in-list :
    (l : list A) (x : A) →
    x ∈-list l → x ∈-vec (vec-list l)
  is-in-vec-list-is-in-list (cons x l) x (is-head .x l) =
    is-head x (vec-list l)
  is-in-vec-list-is-in-list (cons y l) x (is-in-tail .x .y l I) =
    is-in-tail x y (vec-list l) (is-in-vec-list-is-in-list l x I)
```

### Link between `fold-list` and `fold-vec`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (b : B)
  (μ : A → (B → B))
  where
  htpy-fold-list-fold-vec :
    (l : list A) →
    fold-vec b μ (vec-list l) ＝ fold-list b μ l
  htpy-fold-list-fold-vec nil = refl
  htpy-fold-list-fold-vec (cons x l) =
    ap (μ x) (htpy-fold-list-fold-vec l)
```
