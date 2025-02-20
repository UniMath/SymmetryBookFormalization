# The Kolakoski sequence

```agda
module elementary-number-theory.kolakoski-sequence where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strong-induction-natural-numbers

open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.logical-operations-booleans
```

</details>

## Idea

The
{{#concept "Kolakoski sequence" WD="Kolakoski sequence" WDID=Q6427013 Agda=kolakoski}}

```text
1,2,2,1,1,2,1,2,2,1,2,2,1,1,...
```

is a self-referential sequence of `1`s and `2`s which is the flattening of a
sequence

```text
(1),(2,2),(1,1),(2),(1),(2,2),(1,1)
```

of sequences of repeated `1`s and `2`s such that the n-th element in the
Kolakoski sequence describes the length of the n-th element of the above
sequence of sequences.

## Definition

The following definition of the Kolakoski sequence is due to Léo Elouan.

```agda
kolakoski-helper-inductive :
  (n : ℕ) →
  ((i : ℕ) → i ≤-ℕ n → bool × (bool × (Σ ℕ (λ j → j ≤-ℕ i)))) →
  bool × (bool × (Σ ℕ (λ j → j ≤-ℕ (succ-ℕ n))))
kolakoski-helper-inductive n f with f n (refl-leq-ℕ n)
... | b , false , i , H = b , true , i , preserves-leq-succ-ℕ i n H
... | b , true , i , H with f i H
... | true , true , j , K = neg-bool b , true , succ-ℕ i , H
... | true , false , j , K = neg-bool b , false , succ-ℕ i , H
... | false , true , j , K = neg-bool b , false , succ-ℕ i , H
... | false , false , j , K = neg-bool b , true , succ-ℕ i , H

kolakoski-helper : (n : ℕ) → bool × (bool × Σ ℕ (λ i → i ≤-ℕ n))
kolakoski-helper =
  strong-ind-ℕ
    ( λ n → bool × (bool × Σ ℕ (λ j → j ≤-ℕ n)))
    ( false , true , 0 , refl-leq-ℕ 0)
    ( λ n f → kolakoski-helper-inductive n f)

kolakoski : ℕ → ℕ
kolakoski n with pr1 (kolakoski-helper n)
... | true = 2
... | false = 1
```

## External links

- [A000002](https://oeis.org/A000002) in the OEIS
