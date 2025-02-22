# Parity of the integers

```agda
module elementary-number-theory.parity-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.unit-similarity-integers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.negation
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

{{#concept "Parity" WD="parity" WDID=Q141160}}
[partitions](foundation.partitions.md) the
[integers](elementary-number-theory.integers.md) into two
[classes](foundation.equivalence-relations.md): the
{{#concept "even" Disambiguation="integer" Agda=is-even-ℤ WD="even number" WDID=Q13366104}}
and the
{{#concept "odd" Disambiguation="integer" Agda=is-odd-ℤ WD="odd number" WDID=Q13366129}}
integers. Even integers are those that are
[divisible](elementary-number-theory.divisibility-integers.md) by two, and odd
integers are those that aren't.

## Definitions

### Even integers

```agda
is-even-ℤ : ℤ → UU lzero
is-even-ℤ a = div-ℤ (int-ℕ 2) a
```

### The bi-infinite sequence of even integers

```agda
even-integer-ℤ : ℤ → ℤ
even-integer-ℤ a = int-ℕ 2 *ℤ a
```

### Odd integers

```agda
is-odd-ℤ : ℤ → UU lzero
is-odd-ℤ a = ¬ (is-even-ℤ a)
```

### The bi-infinite sequence of odd integers

```agda
odd-integer-ℤ : ℤ → ℤ
odd-integer-ℤ a = int-ℕ 2 *ℤ a +ℤ one-ℤ
```

### The type of odd expansions of an integer

```agda
has-odd-expansion-ℤ : ℤ → UU lzero
has-odd-expansion-ℤ = fiber odd-integer-ℤ
```

## Properties

### Even integers are closed under equality

```agda
is-even-eq-ℤ : {a b : ℤ} → a ＝ b → is-even-ℤ b → is-even-ℤ a
is-even-eq-ℤ refl H = H

is-even-eq-ℤ' : {a b : ℤ} → a ＝ b → is-even-ℤ a → is-even-ℤ b
is-even-eq-ℤ' refl H = H
```

### Odd integers are closed under equality

```agda
is-odd-eq-ℤ : {a b : ℤ} → a ＝ b → is-odd-ℤ b → is-odd-ℤ a
is-odd-eq-ℤ refl H = H

is-odd-eq-ℤ' : {a b : ℤ} → a ＝ b → is-odd-ℤ a → is-odd-ℤ b
is-odd-eq-ℤ' refl H = H
```

### A natural number is even if and only if it is even as an integer

```agda
is-even-int-is-even-ℕ : (n : ℕ) → is-even-ℕ n → is-even-ℤ (int-ℕ n)
is-even-int-is-even-ℕ n H = div-int-div-ℕ H

is-even-is-even-int-ℕ : (n : ℕ) → is-even-ℤ (int-ℕ n) → is-even-ℕ n
is-even-is-even-int-ℕ n H = div-div-int-ℕ H
```

### A natural number is odd if and only if it is odd as an integer

```agda
is-odd-int-is-odd-ℕ : (n : ℕ) → is-odd-ℕ n → is-odd-ℤ (int-ℕ n)
is-odd-int-is-odd-ℕ n H K = H (is-even-is-even-int-ℕ n K)

is-odd-is-odd-int-ℕ : (n : ℕ) → is-odd-ℤ (int-ℕ n) → is-odd-ℕ n
is-odd-is-odd-int-ℕ n H K = H (is-even-int-is-even-ℕ n K)
```

### An integer is even if and only if its absolute value is an even integer

```agda
is-even-int-abs-is-even-ℤ :
  (a : ℤ) → is-even-ℤ a → is-even-ℤ (int-abs-ℤ a)
is-even-int-abs-is-even-ℤ a =
  div-sim-unit-ℤ
    ( refl-sim-unit-ℤ (int-ℕ 2))
    ( symmetric-sim-unit-ℤ (int-abs-ℤ a) a (sim-unit-abs-ℤ a))

is-even-is-even-int-abs-ℤ :
  (a : ℤ) → is-even-ℤ (int-abs-ℤ a) → is-even-ℤ a
is-even-is-even-int-abs-ℤ a =
  div-sim-unit-ℤ
    ( refl-sim-unit-ℤ (int-ℕ 2))
    ( sim-unit-abs-ℤ a)

is-even-abs-is-even-ℤ :
  (a : ℤ) → is-even-ℤ a → is-even-ℕ (abs-ℤ a)
is-even-abs-is-even-ℤ a H =
  is-even-is-even-int-ℕ (abs-ℤ a) (is-even-int-abs-is-even-ℤ a H)

is-even-is-even-abs-ℤ :
  (a : ℤ) → is-even-ℕ (abs-ℤ a) → is-even-ℤ a
is-even-is-even-abs-ℤ a H =
  is-even-is-even-int-abs-ℤ a (is-even-int-is-even-ℕ (abs-ℤ a) H)
```

### An integer is odd if and only if its absolute value is an odd integer

```agda
is-odd-int-abs-is-odd-ℤ : (a : ℤ) → is-odd-ℤ a → is-odd-ℤ (int-abs-ℤ a)
is-odd-int-abs-is-odd-ℤ a H K = H (is-even-is-even-int-abs-ℤ a K)

is-odd-is-odd-int-abs-ℤ : (a : ℤ) → is-odd-ℤ (int-abs-ℤ a) → is-odd-ℤ a
is-odd-is-odd-int-abs-ℤ a H K = H (is-even-int-abs-is-even-ℤ a K)

is-odd-abs-is-odd-ℤ : (a : ℤ) → is-odd-ℤ a → is-odd-ℕ (abs-ℤ a)
is-odd-abs-is-odd-ℤ a H K = H (is-even-is-even-abs-ℤ a K)

is-odd-is-odd-abs-ℤ : (a : ℤ) → is-odd-ℕ (abs-ℤ a) → is-odd-ℤ a
is-odd-is-odd-abs-ℤ a H K = H (is-even-abs-is-even-ℤ a K)
```

### Being even or odd is decidable

```agda
is-decidable-is-even-ℤ :
  (a : ℤ) → is-decidable (is-even-ℤ a)
is-decidable-is-even-ℤ a =
  is-decidable-iff
    ( is-even-is-even-abs-ℤ a)
    ( is-even-abs-is-even-ℤ a)
    ( is-decidable-is-even-ℕ (abs-ℤ a))

is-decidable-is-odd-ℤ : (a : ℤ) → is-decidable (is-odd-ℤ a)
is-decidable-is-odd-ℤ a = is-decidable-neg (is-decidable-is-even-ℤ a)
```

### An integer is even if and only if it is not odd

```agda
is-even-is-not-odd-ℤ :
  (a : ℤ) → ¬ (is-odd-ℤ a) → is-even-ℤ a
is-even-is-not-odd-ℤ a =
  double-negation-elim-is-decidable (is-decidable-is-even-ℤ a)
```

### `0` is an even integer

```agda
is-even-zero-ℤ : is-even-ℤ zero-ℤ
is-even-zero-ℤ = is-even-int-is-even-ℕ 0 is-even-zero-ℕ
```

### `1` is an odd integer

```agda
is-odd-one-ℤ : is-odd-ℤ one-ℤ
is-odd-one-ℤ = is-odd-int-is-odd-ℕ 1 is-odd-one-ℕ
```

### `-1` is an odd integer

```agda
is-odd-neg-one-ℤ : is-odd-ℤ neg-one-ℤ
is-odd-neg-one-ℤ H =
  is-odd-one-ℤ (div-left-summand-ℤ (int-ℕ 2) one-ℤ neg-one-ℤ H is-even-zero-ℤ)
```

### An integer `x` is even if and only if `x + 2` is even

```agda
is-even-is-even-add-two-ℤ :
  (a : ℤ) → is-even-ℤ (a +ℤ int-ℕ 2) → is-even-ℤ a
is-even-is-even-add-two-ℤ a =
  div-left-summand-ℤ (int-ℕ 2) a (int-ℕ 2) (refl-div-ℤ (int-ℕ 2))

is-even-add-two-is-even-ℤ :
  (a : ℤ) → is-even-ℤ a → is-even-ℤ (a +ℤ int-ℕ 2)
is-even-add-two-is-even-ℤ a H =
  div-add-ℤ (int-ℕ 2) a (int-ℕ 2) H (refl-div-ℤ (int-ℕ 2))
```

### An integer `x` is odd if and only if `x + 2` is odd

```agda
is-odd-is-odd-add-two-ℤ : (a : ℤ) → is-odd-ℤ (a +ℤ int-ℕ 2) → is-odd-ℤ a
is-odd-is-odd-add-two-ℤ a H K = H (is-even-add-two-is-even-ℤ a K)

is-odd-add-two-is-odd-ℤ : (a : ℤ) → is-odd-ℤ a → is-odd-ℤ (a +ℤ int-ℕ 2)
is-odd-add-two-is-odd-ℤ a H K = H (is-even-is-even-add-two-ℤ a K)
```

### Either `a` or `a + 1` is even

```agda
is-even-or-is-even-add-one-int-ℕ :
  (n : ℕ) → is-even-ℤ (int-ℕ n) + is-even-ℤ (int-ℕ n +ℤ one-ℤ)
is-even-or-is-even-add-one-int-ℕ n =
  map-coproduct
    ( is-even-int-is-even-ℕ n)
    ( tr is-even-ℤ (inv (add-int-ℕ n 1)) ∘ is-even-int-is-even-ℕ (succ-ℕ n))
    ( is-even-or-is-even-succ-ℕ n)

is-even-or-is-even-add-one-ℤ :
  (a : ℤ) → is-even-ℤ a + is-even-ℤ (a +ℤ one-ℤ)
is-even-or-is-even-add-one-ℤ (inl zero-ℕ) = inr is-even-zero-ℤ
is-even-or-is-even-add-one-ℤ (inl (succ-ℕ x)) = {!!}
is-even-or-is-even-add-one-ℤ (inr (inl star)) = inl is-even-zero-ℤ
is-even-or-is-even-add-one-ℤ (inr (inr x)) = {!!}
```

### If an integer `x` is even, then `x + 1` is odd

```agda
is-odd-add-one-is-even-ℤ :
  (a : ℤ) → is-even-ℤ a → is-odd-ℤ (a +ℤ one-ℤ)
is-odd-add-one-is-even-ℤ a H K =
  is-odd-one-ℤ (div-right-summand-ℤ (int-ℕ 2) a one-ℤ H K)
```

### If an integer `x` is even, then `x - 1` is odd

```agda
is-odd-add-neg-one-is-even-ℤ :
  (a : ℤ) → is-even-ℤ a → is-odd-ℤ (a -ℤ one-ℤ)
is-odd-add-neg-one-is-even-ℤ a H K =
  is-odd-neg-one-ℤ (div-right-summand-ℤ (int-ℕ 2) a neg-one-ℤ H K)
```

### If an integer `x + 1` is even, then `x` is odd

```agda
is-odd-is-even-add-one-ℤ :
  (a : ℤ) → is-even-ℤ (a +ℤ one-ℤ) → is-odd-ℤ a
is-odd-is-even-add-one-ℤ a H K =
  is-odd-one-ℤ (div-right-summand-ℤ (int-ℕ 2) a one-ℤ K H)
```

### If an integer `a - 1` is even, then `a` is odd

```agda
is-odd-is-even-add-neg-one-ℤ :
  (a : ℤ) → is-even-ℤ (a -ℤ one-ℤ) → is-odd-ℤ a
is-odd-is-even-add-neg-one-ℤ a H K =
  is-odd-neg-one-ℤ (div-right-summand-ℤ (int-ℕ 2) a neg-one-ℤ K H)
```

### If an integer `x` is odd, then `x + 1` is even

```agda
is-even-add-one-is-odd-ℤ :
  (a : ℤ) → is-odd-ℤ a → is-even-ℤ (a +ℤ one-ℤ)
is-even-add-one-is-odd-ℤ a H =
  is-even-is-not-odd-ℤ
    ( a +ℤ one-ℤ)
    ( λ K →
      {!is-odd-!})
```

### If an integer is even, then its predecessor is odd

```agda
is-odd-pred-is-even-ℤ :
  (a : ℤ) → is-even-ℤ a → is-odd-ℤ (pred-ℤ a)
is-odd-pred-is-even-ℤ a H =
  is-odd-eq-ℤ (is-right-add-neg-one-pred-ℤ a) (is-odd-add-neg-one-is-even-ℤ a H)
```

### If the successor of an integer `a` is even, then `a` is odd

```agda
is-odd-is-even-succ-ℤ :
  (a : ℤ) → is-even-ℤ (succ-ℤ a) → is-odd-ℤ a
is-odd-is-even-succ-ℤ a H =
  is-odd-is-even-add-one-ℤ a (is-even-eq-ℤ' (is-right-add-one-succ-ℤ a) H)
```

### If the predecessor of an integer is even, then it is odd

```agda
is-odd-is-even-pred-ℤ :
  (a : ℤ) → is-even-ℤ (pred-ℤ a) → is-odd-ℤ a
is-odd-is-even-pred-ℤ a H =
  is-odd-is-even-add-neg-one-ℤ a
    ( is-even-eq-ℤ' (is-right-add-neg-one-pred-ℤ a) H)
```

### If an integer `x + 1` is odd, then `x` is even

```text
is-even-is-odd-succ-ℕ :
  (n : ℕ) → is-odd-ℕ (succ-ℕ n) → is-even-ℕ n
is-even-is-odd-succ-ℕ n p =
  is-even-is-even-succ-succ-ℕ
    ( n)
    ( is-even-succ-is-odd-ℕ (succ-ℕ n) p)
```

### An integer is odd if and only if it has an odd expansion

```agda
is-odd-has-odd-expansion-ℤ : (a : ℤ) → has-odd-expansion-ℤ a → is-odd-ℤ a
is-odd-has-odd-expansion-ℤ ._ (x , refl) =
  is-odd-add-one-is-even-ℤ (int-ℕ 2 *ℤ x) (x , commutative-mul-ℤ x (int-ℕ 2))

has-odd-expansion-neg-one-ℤ : has-odd-expansion-ℤ neg-one-ℤ
pr1 has-odd-expansion-neg-one-ℤ = neg-one-ℤ
pr2 has-odd-expansion-neg-one-ℤ = refl

is-even-integer-below-ℤ :
  (a b : ℤ) → UU lzero
is-even-integer-below-ℤ a b = is-even-ℤ b × (b ≤-ℤ a)

is-decidable-is-even-integer-below-ℤ :
  (a b : ℤ) → is-decidable (is-even-integer-below-ℤ a b)
is-decidable-is-even-integer-below-ℤ a b =
  is-decidable-product (is-decidable-is-even-ℤ b) (is-decidable-leq-ℤ b a)

instance-even-integer-below-ℤ :
  (a : ℤ) → Σ ℤ (is-even-integer-below-ℤ a)
instance-even-integer-below-ℤ (inl x) = {!!}
instance-even-integer-below-ℤ (inr (inl x)) =
  ( zero-ℤ , is-even-zero-ℤ , refl-leq-ℤ zero-ℤ)
instance-even-integer-below-ℤ (inr (inr x)) =
  ( zero-ℤ , is-even-zero-ℤ , leq-zero-is-positive-ℤ (inr (inr x)) star)

has-odd-expansion-is-odd-ℤ :
  (a : ℤ) → is-odd-ℤ a → has-odd-expansion-ℤ a
has-odd-expansion-is-odd-ℤ a H = {!!}
```

```text
is-odd-has-odd-expansion-ℕ : (n : ℕ) → has-odd-expansion-ℕ n → is-odd-ℕ n
is-odd-has-odd-expansion-ℕ .(succ-ℕ (m *ℕ 2)) (m , refl) =
  is-odd-succ-is-even-ℕ (m *ℕ 2) (m , refl)

has-odd-expansion-is-odd : (n : ℕ) → is-odd-ℕ n → has-odd-expansion-ℕ n
has-odd-expansion-is-odd zero-ℕ p = ex-falso (p is-even-zero-ℕ)
has-odd-expansion-is-odd (succ-ℕ zero-ℕ) p = 0 , refl
has-odd-expansion-is-odd (succ-ℕ (succ-ℕ n)) p =
  ( succ-ℕ (pr1 s)) , ap (succ-ℕ ∘ succ-ℕ) (pr2 s)
  where
  s : has-odd-expansion-ℕ n
  s = has-odd-expansion-is-odd n (is-odd-is-odd-succ-succ-ℕ n p)
```

### A number is even if and only if it is divisible by an even number

```text
is-even-div-is-even-ℕ :
  (n m : ℕ) → is-even-ℕ m → div-ℕ m n → is-even-ℕ n
is-even-div-is-even-ℕ ._ ._ (m' , refl) (k , refl) =
  k *ℕ m' , associative-mul-ℕ k m' 2

is-even-div-4-ℕ :
  (n : ℕ) → div-ℕ 4 n → is-even-ℕ n
is-even-div-4-ℕ n = is-even-div-is-even-ℕ n 4 (2 , refl)
```

### If any two out of `x`, `y`, and `x + y` are even, then so is the third

```text
is-even-add-ℕ :
  (m n : ℕ) → is-even-ℕ m → is-even-ℕ n → is-even-ℕ (add-ℕ m n)
is-even-add-ℕ = div-add-ℕ 2

is-even-left-summand-ℕ :
  (m n : ℕ) → is-even-ℕ n → is-even-ℕ (add-ℕ m n) → is-even-ℕ m
is-even-left-summand-ℕ = div-left-summand-ℕ 2

is-even-right-summand-ℕ :
  (m n : ℕ) → is-even-ℕ m → is-even-ℕ (add-ℕ m n) → is-even-ℕ n
is-even-right-summand-ℕ = div-right-summand-ℕ 2
```
