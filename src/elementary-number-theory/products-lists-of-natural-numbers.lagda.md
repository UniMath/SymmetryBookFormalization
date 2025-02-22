# Products of lists of natural numbers

```agda
module elementary-number-theory.products-lists-of-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types

open import lists.concatenation-lists
open import lists.lists
open import lists.permutation-lists
open import lists.universal-quantification-lists
```

</details>

## Idea

Given a [list](lists.lists.md) of
[natural numbers](elementary-number-theory.natural-numbers.md) $l$, we define
the {{#concept "product" Disambiguation="list of natural numbers"}} of the
elements of $l$ by recursively multiplying all its elements.

## Definitions

### The product of the elements of a list

```agda
mul-list-ℕ :
  list ℕ → ℕ
mul-list-ℕ = fold-list 1 mul-ℕ
```

## Properties

### The product of any list of natural numbers greater than one is greater than one

```agda
leq-one-mul-list-ℕ :
  (l : list ℕ) (H : for-all-list l (leq-ℕ 1)) → 1 ≤-ℕ mul-list-ℕ l
leq-one-mul-list-ℕ nil H = refl-leq-ℕ 1
leq-one-mul-list-ℕ (cons n l) (H , K) =
  preserves-order-mul-ℕ 1 n 1 (mul-list-ℕ l) H (leq-one-mul-list-ℕ l K)
```

### `mul-list-ℕ` is permutation invariant

```agda
permutation-invariant-mul-list-ℕ :
  (l : list ℕ) (t : permutation (length-list l)) →
  mul-list-ℕ l ＝ mul-list-ℕ (permute-list l t)
permutation-invariant-mul-list-ℕ =
  permutation-invariant-fold-list 1 mul-ℕ left-swap-mul-ℕ
```

### `mul-list-ℕ` of a concatenation of lists

```agda
compute-mul-concat-list-ℕ :
  (p q : list ℕ) →
  mul-list-ℕ (concat-list p q) ＝ mul-list-ℕ p *ℕ mul-list-ℕ q
compute-mul-concat-list-ℕ nil q =
  inv (left-unit-law-add-ℕ (mul-list-ℕ q))
compute-mul-concat-list-ℕ (cons x p) q =
  ap (mul-ℕ x) (compute-mul-concat-list-ℕ p q) ∙
  inv (associative-mul-ℕ x (mul-list-ℕ p) (mul-list-ℕ q))
```
