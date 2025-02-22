# The Collatz conjecture

```agda
module elementary-number-theory.collatz-conjecture where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Statement

```agda
collatz : ℕ → ℕ
collatz n with is-decidable-div-ℕ 2 n
... | inl (pair y p) = y
... | inr f = succ-ℕ (3 *ℕ n)

iterate-collatz : ℕ → ℕ → ℕ
iterate-collatz zero-ℕ n = n
iterate-collatz (succ-ℕ k) n = collatz (iterate-collatz k n)

Collatz-conjecture : UU lzero
Collatz-conjecture =
  (n : ℕ) → is-nonzero-ℕ n → Σ ℕ (λ k → is-one-ℕ (iterate-collatz k n))
```
