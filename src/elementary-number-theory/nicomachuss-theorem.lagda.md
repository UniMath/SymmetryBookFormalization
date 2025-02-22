# Nicomachus's Theorem

```agda
module elementary-number-theory.nicomachuss-theorem where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.cubes-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.pronic-numbers
open import elementary-number-theory.squares-natural-numbers
open import elementary-number-theory.sums-of-natural-numbers
open import elementary-number-theory.triangular-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.transport-along-identifications

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

{{#concept "Nicomachus's Theorem" Agda=nicomachuss-theorem-ℕ WDID=Q2197859 WD="squared triangular number"}}
asserts that the [sum](elementary-number-theory.sums-natural-numbers.md) from
`k ＝ 0` to `n` of the
[cube](elemenatary-number-theory.cubes-natural-numbers.md) `k³` is
[equal to](foundation-core.identity-types.md) the
[square](elementary-number-theory.squares-natural-numbers.md) of the `n`th
[triangular number](elementary-number-theory.triangular-numbers.md), i.e., it
asserts that

$$
  \sum_{k=0}^n k^3 = \left(\sum_{k=0}^n k \right)^2.
$$

This identity is a common exercise in introductory sections on mathematical
induction. As such, it can be found as exercise 2 in section 1.2 of
{{#cite Andrews94}}, or exercise 2(c) of section 1.2 in {{#cite Leveque12volI}}.

**Proof.** Recall that the $n$th triangular number is $n(n+1)/2$. We will prove
by induction that

$$
  4\sum_{k=0}^n k^3 = 4\left(\sum_{k=0}^n k \right)^2.
$$

This allows us to avoid carrying along division by 4 throughout the proof. In
the base case we have

$$
  4\sum_{k=0}^0 k^3 = 4·0^3 = 4·0^2 = 4(0·1/2)^2.
$$

For the inductive step, assume that the identity holds for `n`. Then we have

$$
  4\sum_{k=0}^{n+1} k^3 = (n(n+1))^2 + 4(n+1)^3 = ((n+1)(n+2))^2,
$$

where the last step follows by algebra. This completes the proof.

## Properties

### The square of the pronic number of a successor

We have `((n + 1) _ (n + 2))² ＝ (n _ (n + 1))² + 4 \* (n + 1)³

```agda
compute-square-pronic-number-succ-ℕ :
  (n : ℕ) →
  square-ℕ (pronic-number-ℕ (succ-ℕ n)) ＝
  square-ℕ (pronic-number-ℕ n) +ℕ 4 *ℕ cube-ℕ (succ-ℕ n)
compute-square-pronic-number-succ-ℕ n =
  ( ap square-ℕ (commutative-mul-ℕ (succ-ℕ n) (succ-ℕ (succ-ℕ n)))) ∙
  ( distributive-square-mul-ℕ (succ-ℕ (succ-ℕ n)) (succ-ℕ n)) ∙
  ( ap (_*ℕ (square-ℕ (succ-ℕ n))) (square-succ-succ-ℕ' n)) ∙
  ( right-distributive-mul-add-ℕ
    ( square-ℕ n)
    ( 4 *ℕ succ-ℕ n)
    ( square-ℕ (succ-ℕ n))) ∙
  ( ap-add-ℕ
    ( inv (distributive-square-mul-ℕ n (succ-ℕ n)))
    ( associative-mul-ℕ 4 (succ-ℕ n) (square-ℕ (succ-ℕ n)) ∙
      ap (mul-ℕ 4) (commutative-mul-ℕ (succ-ℕ n) (square-ℕ (succ-ℕ n)))))
```

### Nicomachus's theorem

```agda
nicomachuss-theorem-ℕ' :
  (n : ℕ) →
  4 *ℕ sum-Fin-ℕ (succ-ℕ n) (λ i → cube-ℕ (nat-Fin (succ-ℕ n) i)) ＝
  4 *ℕ square-ℕ (triangular-number-ℕ n)
nicomachuss-theorem-ℕ' zero-ℕ = refl
nicomachuss-theorem-ℕ' (succ-ℕ n) =
  ( left-distributive-mul-add-ℕ 4
    ( sum-Fin-ℕ (succ-ℕ n) (λ i → cube-ℕ (nat-Fin (succ-ℕ n) i)))
    ( cube-ℕ (succ-ℕ n))) ∙
  ( ap
    ( _+ℕ 4 *ℕ cube-ℕ (succ-ℕ n))
    ( ( nicomachuss-theorem-ℕ' n) ∙
      ( inv (distributive-square-mul-ℕ 2 (triangular-number-ℕ n))) ∙
      ( ap square-ℕ (compute-triangular-number-ℕ' n)))) ∙
  ( inv (compute-square-pronic-number-succ-ℕ n)) ∙
  ( ap square-ℕ (inv (compute-triangular-number-ℕ' (succ-ℕ n)))) ∙
  ( distributive-square-mul-ℕ 2 (triangular-number-ℕ (succ-ℕ n)))

nicomachuss-theorem-ℕ :
  (n : ℕ) →
  sum-Fin-ℕ (succ-ℕ n) (λ i → cube-ℕ (nat-Fin (succ-ℕ n) i)) ＝
  square-ℕ (triangular-number-ℕ n)
nicomachuss-theorem-ℕ n =
  is-injective-left-mul-ℕ 4
    ( is-nonzero-four-ℕ)
    ( nicomachuss-theorem-ℕ' n)
```

## References

{{#bibliography}}
