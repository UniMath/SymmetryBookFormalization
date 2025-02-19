# The triangular numbers

```agda
module elementary-number-theory.triangular-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.pronic-numbers
open import elementary-number-theory.sums-of-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
```

</details>

## Idea

The $n$th {{#concept "triangular number" Agda=triangular-number-ℕ}} is the
[sum](elementary-number-theory.sums-of-natural-numbers.md) of the
[natural numbers](elementary-number-theory.natural-numbers.md) up to $n$.
Alternatively, the triangular numbers can be defined inductively by

```text
  T 0 := 0
  T (n + 1) := T n + (n + 1).
```

A classic inductive proof, which is often used as the first example when
introducing students to mathematical induction, establishes the famous fact that

```text
  T n = n(n + 1)/2.
```

In other words, the $n$th triangular number is half the $n$th
[pronic number](elementary-number-theory.pronic-numbers.md).

## Definition

### The sum definition of the triangular numbers

```agda
triangular-number-ℕ : ℕ → ℕ
triangular-number-ℕ n = bounded-sum-ℕ n (λ x H → x)
```

### The inductive definition of the triangular numbers

```agda
inductive-triangular-number-ℕ : ℕ → ℕ
inductive-triangular-number-ℕ 0 = 0
inductive-triangular-number-ℕ (succ-ℕ n) =
  inductive-triangular-number-ℕ n +ℕ succ-ℕ n
```

## Properties

### The two definitions of triangular numbers are the same

```agda
compute-inductive-triangular-number-ℕ :
  (n : ℕ) → inductive-triangular-number-ℕ n ＝ triangular-number-ℕ n
compute-inductive-triangular-number-ℕ zero-ℕ = refl
compute-inductive-triangular-number-ℕ (succ-ℕ n) =
  ap (add-ℕ' (succ-ℕ n)) (compute-inductive-triangular-number-ℕ n)
```

### The $n$th triangular number is $\frac{1}{2}n(n+1)$

**Proof.** The claim is equivalent to the claim that

$$
  2 \cdot \left(\sum_{i\leq n} i\right) = n(n+1).
$$

We prove this claim to avoid an early division by two, and the proof is by
induction on $n$. In the base case both sides of the equality are $0$. For the
inductive step, assume that $2 \cdot \sum_{i\leq n} i ＝ n(n+1)$. Then we can
compute

$$
2 \cdot \sum_{i\leq n+1} i = 2 \cdot \left(\sum_{i\leq n} i\right)+ 2(n+1) = n(n+1) + ((n+1) + (n+1)) = (n+1)(n+2).
$$

```agda
value-triangular-number-ℕ : ℕ → ℕ
value-triangular-number-ℕ n =
  quotient-div-ℕ 2 (pronic-number-ℕ n) (is-even-pronic-number-ℕ n)

compute-triangular-number-ℕ' :
  (n : ℕ) → 2 *ℕ triangular-number-ℕ n ＝ pronic-number-ℕ n
compute-triangular-number-ℕ' zero-ℕ = refl
compute-triangular-number-ℕ' (succ-ℕ n) =
  left-distributive-mul-add-ℕ 2 (triangular-number-ℕ n) (succ-ℕ n) ∙
  ap-add-ℕ (compute-triangular-number-ℕ' n) (left-two-law-mul-ℕ (succ-ℕ n)) ∙
  inv (associative-add-ℕ (n *ℕ succ-ℕ n) (succ-ℕ n) (succ-ℕ n)) ∙
  inv (right-successor-law-mul-ℕ (succ-ℕ n) (succ-ℕ n))

compute-triangular-number-ℕ :
  (n : ℕ) →
  triangular-number-ℕ n ＝
  quotient-div-ℕ 2 (pronic-number-ℕ n) (is-even-pronic-number-ℕ n)
compute-triangular-number-ℕ n =
  is-injective-left-mul-ℕ 2
    ( is-nonzero-two-ℕ)
    ( compute-triangular-number-ℕ' n ∙
      inv (eq-quotient-div-ℕ 2 (n *ℕ succ-ℕ n) (is-even-pronic-number-ℕ n)) ∙
      commutative-mul-ℕ (value-triangular-number-ℕ n) 2)
```

## See also

- [Nicomachus's Theorem](elementary-number-theory.nicomachuss-theorem.md)
