# The square pyramidal numbers

```agda
module elementary-number-theory.square-pyramidal-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.pronic-numbers
open import elementary-number-theory.squares-natural-numbers
open import elementary-number-theory.sums-of-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.transport-along-identifications

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The $n$th
{{#concept "square pyramidal number" Agda=square-pyramidal-number-ℕ OEIS=A000330 WDID=Q18949 WD="square pyramidal number"}}
is the [sum](elementary-number-theory.sums-of-natural-numbers.md) of
[squares](elementary-number-theory.squares-natural-numbers.md)

$$
  1^2 + 2^2 + \cdots + n^2.
$$

A common exercise in mathematical induction states that the $n$th square
pyramidal number is equal to

$$
  \frac{n(n+1)(2n+1)}{6}.
$$

The sequence of square pyramidal numbers is listed as A000330 in the
[OEIS](literature.oeis.md) {{#cite OEIS}}.

## Definitions

### The square pyramidal numbers

```agda
square-pyramidal-number-ℕ : ℕ → ℕ
square-pyramidal-number-ℕ n =
  sum-Fin-ℕ (succ-ℕ n) (λ i → square-ℕ (nat-Fin (succ-ℕ n) i))
```

## Properties

### Computing the square pyramidal numbers

We will prove the identity

$$
  \sum_{k=0}^n k^2 ＝ \frac{n(n+1)(2n+1)}{6}.
$$

In order to prove this, we first show that the sequence $a_n := n(n+1)(2n+1)$
satisfies the recurrence

$$
  a_{n+1} = a_n + 6(n+1)^2.
$$

By this recurrence it follows that each $a_n$ is
[divisible](elementary-number-theory.divisibility-natural-numbers.md) by $6$,
and that $a_n$ is $6$ times the $n$th pyramidal number.

The computation of the square pyramidal numbers is a common exercise in
elementary number theory texts, such as exercise 1 of section 1.2 in
{{#cite Andrews94}}.

```agda
dividend-square-pyramidal-number-ℕ : ℕ → ℕ
dividend-square-pyramidal-number-ℕ n = pronic-number-ℕ n *ℕ odd-number-ℕ n

dividend-square-pyramidal-number-succ-ℕ :
  (n : ℕ) →
  dividend-square-pyramidal-number-ℕ (succ-ℕ n) ＝
  dividend-square-pyramidal-number-ℕ n +ℕ 6 *ℕ square-ℕ (succ-ℕ n)
dividend-square-pyramidal-number-succ-ℕ n =
  ( associative-mul-ℕ
    ( succ-ℕ n)
    ( succ-ℕ (succ-ℕ n))
    ( odd-number-ℕ (succ-ℕ n))) ∙
  ( ap
    ( succ-ℕ n *ℕ_)
    ( ( ap
        ( succ-ℕ (succ-ℕ n) *ℕ_)
        ( ap succ-ℕ (left-distributive-mul-add-ℕ 2 n 1))) ∙
      ( left-distributive-mul-add-ℕ (succ-ℕ (succ-ℕ n)) (odd-number-ℕ n) 2) ∙
      ( ( ap-add-ℕ
          ( right-distributive-mul-add-ℕ n 2 (odd-number-ℕ n))
          ( ( commutative-mul-ℕ (succ-ℕ (succ-ℕ n)) 2) ∙
            ( left-distributive-mul-add-ℕ 2 (succ-ℕ n) 1))) ∙
        ( associative-add-ℕ
          ( n *ℕ odd-number-ℕ n)
          ( 2 *ℕ odd-number-ℕ n)
          ( 2 *ℕ succ-ℕ n +ℕ 2) ∙
          ( ap
            ( n *ℕ odd-number-ℕ n +ℕ_)
            ( ( left-swap-add-ℕ (2 *ℕ odd-number-ℕ n) (2 *ℕ succ-ℕ n) 2) ∙
              ( ap
                ( 2 *ℕ succ-ℕ n +ℕ_)
                ( inv (left-distributive-mul-add-ℕ 2 (odd-number-ℕ n) 1))) ∙
              ( ap
                ( 2 *ℕ succ-ℕ n +ℕ_)
                ( ( ap (2 *ℕ_) (inv (left-distributive-mul-add-ℕ 2 n 1))) ∙
                  ( inv (associative-mul-ℕ 2 2 (succ-ℕ n))))) ∙
              ( inv (right-distributive-mul-add-ℕ 2 4 (succ-ℕ n))))))))) ∙
  ( left-distributive-mul-add-ℕ
    ( succ-ℕ n)
    ( n *ℕ odd-number-ℕ n)
    ( 6 *ℕ succ-ℕ n)) ∙
  ( ap-add-ℕ
    ( ( left-swap-mul-ℕ (succ-ℕ n) n (odd-number-ℕ n)) ∙
      ( inv (associative-mul-ℕ n (succ-ℕ n) (odd-number-ℕ n))))
    ( left-swap-mul-ℕ (succ-ℕ n) 6 (succ-ℕ n)))

div-6-dividend-square-pyramidal-number-ℕ :
  (n : ℕ) → div-ℕ 6 (dividend-square-pyramidal-number-ℕ n)
div-6-dividend-square-pyramidal-number-ℕ zero-ℕ = div-zero-ℕ 6
div-6-dividend-square-pyramidal-number-ℕ (succ-ℕ n) =
  tr
    ( div-ℕ 6)
    ( inv (dividend-square-pyramidal-number-succ-ℕ n))
    ( div-add-ℕ 6
      ( dividend-square-pyramidal-number-ℕ n)
      ( 6 *ℕ square-ℕ (succ-ℕ n))
      ( div-6-dividend-square-pyramidal-number-ℕ n)
      ( div-mul-ℕ' (square-ℕ (succ-ℕ n)) 6 6 (refl-div-ℕ 6)))

value-square-pyramidal-number-ℕ : ℕ → ℕ
value-square-pyramidal-number-ℕ n =
  quotient-div-ℕ 6
    ( dividend-square-pyramidal-number-ℕ n)
    ( div-6-dividend-square-pyramidal-number-ℕ n)

eq-value-square-pyramidal-number-ℕ :
  (n : ℕ) →
  6 *ℕ value-square-pyramidal-number-ℕ n ＝ dividend-square-pyramidal-number-ℕ n
eq-value-square-pyramidal-number-ℕ n =
  eq-quotient-div-ℕ' 6
    ( dividend-square-pyramidal-number-ℕ n)
    ( div-6-dividend-square-pyramidal-number-ℕ n)

compute-square-pyramidal-number-ℕ' :
  (n : ℕ) →
  6 *ℕ square-pyramidal-number-ℕ n ＝ dividend-square-pyramidal-number-ℕ n
compute-square-pyramidal-number-ℕ' zero-ℕ = refl
compute-square-pyramidal-number-ℕ' (succ-ℕ n) =
  ( left-distributive-mul-add-ℕ 6
    ( square-pyramidal-number-ℕ n)
    ( square-ℕ (succ-ℕ n))) ∙
  ( ap (_+ℕ 6 *ℕ square-ℕ (succ-ℕ n)) (compute-square-pyramidal-number-ℕ' n)) ∙
  ( inv (dividend-square-pyramidal-number-succ-ℕ n))

compute-square-pyramidal-number-ℕ :
  (n : ℕ) → square-pyramidal-number-ℕ n ＝ value-square-pyramidal-number-ℕ n
compute-square-pyramidal-number-ℕ n =
  is-injective-left-mul-ℕ 6
    ( is-nonzero-succ-ℕ 5)
    ( ( compute-square-pyramidal-number-ℕ' n) ∙
      ( inv (eq-value-square-pyramidal-number-ℕ n)))
```

## References

{{#bibliography}}
