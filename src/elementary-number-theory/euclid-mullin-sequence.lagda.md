# The Euclid–Mullin sequence

```agda
module elementary-number-theory.euclid-mullin-sequence where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nontrivial-divisors-natural-numbers
open import elementary-number-theory.products-of-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.strong-induction-natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unit-type

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "Euclid–Mullin sequence" Agda=euclid-mullin-ℕ WDID=Q5406148 WD="Euclid-Mullin sequence"}}
is a [sequence](foundation.sequences.md) of
[natural numbers](elementary-number-theory.natural-numbers.md), which is defined
by
[strong induction](elementary-number-theory.strong-induction-natural-numbers.md)
by

```text
  euclid-mullin-ℕ 0 := 2,
```

and `euclid-mullin-ℕ (n + 1)` is the least
[prime factor](elementary-number-theory.prime-numbers.md) of the product of all
previous entries in the Euclid–Mullin sequence plus one.

## Definitions

### The Euclid–Mullin sequence

```agda
euclid-mullin-ℕ : ℕ → ℕ
euclid-mullin-ℕ =
  strong-rec-ℕ
    ( 2)
    ( λ n f →
      nat-least-nontrivial-divisor-ℕ'
        ( succ-ℕ
          ( Π-ℕ
            ( succ-ℕ n)
            ( λ i → f (nat-Fin (succ-ℕ n) i) (upper-bound-nat-Fin n i)))))

compute-euclid-mullin-0-ℕ : euclid-mullin-ℕ 0 ＝ 2
compute-euclid-mullin-0-ℕ = refl

compute-euclid-mullin-1-ℕ : euclid-mullin-ℕ 1 ＝ 3
compute-euclid-mullin-1-ℕ = refl

compute-euclid-mullin-2-ℕ : euclid-mullin-ℕ 2 ＝ 7
compute-euclid-mullin-2-ℕ = refl
```

The following computations also type-check, but take a very long time to
terminate.

```text
compute-euclid-mullin-3-ℕ : euclid-mullin-ℕ 3 ＝ 43
compute-euclid-mullin-3-ℕ = refl

compute-euclid-mullin-4-ℕ : euclid-mullin-ℕ 4 ＝ 13
compute-euclid-mullin-4-ℕ = refl

compute-euclid-mullin-5-ℕ : euclid-mullin-ℕ 5 ＝ 53
compute-euclid-mullin-5-ℕ = refl

compute-euclid-mullin-6-ℕ : euclid-mullin-ℕ 6 ＝ 5
compute-euclid-mullin-6-ℕ = refl

compute-euclid-mullin-7-ℕ : euclid-mullin-ℕ 7 ＝ 6221671
compute-euclid-mullin-7-ℕ = refl

compute-euclid-mullin-8-ℕ : euclid-mullin-ℕ 8 ＝ 38709183810571
compute-euclid-mullin-8-ℕ = refl
```
