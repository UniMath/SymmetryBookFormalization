# Nonzero natural numbers

```agda
module elementary-number-theory.nonzero-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.propositions
open import foundation.sections
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

A [natural number](elementary-number-theory.natural-numbers.md) `n` is said to
be **nonzero** if the [proposition](foundation.propositions.md)

```text
  n ≠ 0
```

holds. This condition was already defined in the file
[`elementary-number-theory.natural-numbers`](elementary-number-theory.natural-numbers.md).
The type of nonzero natural numbers consists of natural numbers equipped with a
proof that they are nonzero.

## Definitions

### The type of nonzero natural numbers

```agda
nonzero-ℕ : UU lzero
nonzero-ℕ = Σ ℕ is-nonzero-ℕ

ℕ⁺ : UU lzero
ℕ⁺ = nonzero-ℕ

nat-nonzero-ℕ : nonzero-ℕ → ℕ
nat-nonzero-ℕ = pr1

nat-ℕ⁺ = nat-nonzero-ℕ

is-nonzero-nat-nonzero-ℕ : (n : nonzero-ℕ) → is-nonzero-ℕ (nat-nonzero-ℕ n)
is-nonzero-nat-nonzero-ℕ = pr2

eq-nonzero-ℕ : {m n : nonzero-ℕ} → nat-nonzero-ℕ m ＝ nat-nonzero-ℕ n → m ＝ n
eq-nonzero-ℕ m=n = eq-pair-Σ m=n (eq-is-prop is-prop-nonequal)
```

### The nonzero natural number `1`

```agda
one-nonzero-ℕ : nonzero-ℕ
pr1 one-nonzero-ℕ = 1
pr2 one-nonzero-ℕ = is-nonzero-one-ℕ

one-ℕ⁺ = one-nonzero-ℕ
```

### The successor function on the nonzero natural numbers

```agda
succ-nonzero-ℕ : nonzero-ℕ → nonzero-ℕ
pr1 (succ-nonzero-ℕ (pair x _)) = succ-ℕ x
pr2 (succ-nonzero-ℕ (pair x _)) = is-nonzero-succ-ℕ x
```

### The successor function from the natural numbers to the nonzero natural numbers

```agda
succ-nonzero-ℕ' : ℕ → nonzero-ℕ
pr1 (succ-nonzero-ℕ' n) = succ-ℕ n
pr2 (succ-nonzero-ℕ' n) = is-nonzero-succ-ℕ n
```

### The predecessor function from the nonzero natural numbers to the natural numbers

```agda
pred-nonzero-ℕ : nonzero-ℕ → ℕ
pred-nonzero-ℕ (succ-ℕ n , _) = n
pred-nonzero-ℕ (zero-ℕ , H) = ex-falso (H refl)

pred-ℕ⁺ = pred-nonzero-ℕ

is-section-succ-nonzero-ℕ' : is-section succ-nonzero-ℕ' pred-nonzero-ℕ
is-section-succ-nonzero-ℕ' (zero-ℕ , H) = ex-falso (H refl)
is-section-succ-nonzero-ℕ' n⁺@(succ-ℕ n , _) = eq-nonzero-ℕ refl

is-section-pred-nonzero-ℕ : is-section pred-nonzero-ℕ succ-nonzero-ℕ'
is-section-pred-nonzero-ℕ n = refl
```

### The quotient of a nonzero natural number by a divisor

```agda
quotient-div-nonzero-ℕ :
  (d : ℕ) (x : nonzero-ℕ) (H : div-ℕ d (pr1 x)) → nonzero-ℕ
pr1 (quotient-div-nonzero-ℕ d (pair x K) H) = quotient-div-ℕ d x H
pr2 (quotient-div-nonzero-ℕ d (pair x K) H) = is-nonzero-quotient-div-ℕ H K
```

### Addition of nonzero natural numbers

```agda
add-nonzero-ℕ : nonzero-ℕ → nonzero-ℕ → nonzero-ℕ
pr1 (add-nonzero-ℕ (p , p≠0) (q , q≠0)) = p +ℕ q
pr2 (add-nonzero-ℕ (succ-ℕ p , H) (succ-ℕ q , K)) ()
pr2 (add-nonzero-ℕ (succ-ℕ p , H) (zero-ℕ , K)) = ex-falso (K refl)
pr2 (add-nonzero-ℕ (zero-ℕ , H) (q , K)) = ex-falso (H refl)

_+ℕ⁺_ = add-nonzero-ℕ
```

### Multiplication of nonzero natural numbers

```agda
mul-nonzero-ℕ : nonzero-ℕ → nonzero-ℕ → nonzero-ℕ
pr1 (mul-nonzero-ℕ (p , p≠0) (q , q≠0)) = p *ℕ q
pr2 (mul-nonzero-ℕ (p , p≠0) (q , q≠0)) pq=0 =
  rec-coproduct p≠0 q≠0 (is-zero-summand-is-zero-mul-ℕ p q pq=0)

_*ℕ⁺_ = mul-nonzero-ℕ
```

### Strict inequality on nonzero natural numbers

```agda
le-ℕ⁺ : ℕ⁺ → ℕ⁺ → UU lzero
le-ℕ⁺ (p , _) (q , _) = le-ℕ p q
```

### Inequality on nonzero natural numbers

```agda
leq-ℕ⁺ : ℕ⁺ → ℕ⁺ → UU lzero
leq-ℕ⁺ (p , _) (q , _) = leq-ℕ p q
```

### Addition of nonzero natural numbers is a strictly inflationary map

```agda
le-left-add-nat-ℕ⁺ : (m : ℕ) (n : ℕ⁺) → le-ℕ m (m +ℕ nat-ℕ⁺ n)
le-left-add-nat-ℕ⁺ m (n , n≠0) =
  tr
    ( λ p → le-ℕ p (m +ℕ n))
    ( right-unit-law-add-ℕ m)
    ( preserves-le-left-add-ℕ m zero-ℕ n (le-is-nonzero-ℕ n n≠0))
```

### The predecessor function from the nonzero natural numbers reflects inequality

```agda
reflects-leq-pred-nonzero-ℕ :
  (m n : ℕ⁺) → leq-ℕ (pred-ℕ⁺ m) (pred-ℕ⁺ n) → leq-ℕ⁺ m n
reflects-leq-pred-nonzero-ℕ (succ-ℕ m , _) (succ-ℕ n , _) m≤n = m≤n
reflects-leq-pred-nonzero-ℕ (zero-ℕ , H) _ = ex-falso (H refl)
reflects-leq-pred-nonzero-ℕ (succ-ℕ _ , _) (zero-ℕ , H) = ex-falso (H refl)
```
