# Squares of integers

```agda
module elementary-number-theory.squares-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.parity-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.squares-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

The {{#concept "square" Disambiguation="integer" Agda=square-ℤ}} `a²` of an
[integer](elementary-number-theory.integers.md) `a` is the
[product](elementary-number-theory.multiplication-natural-numbers.md)

```text
  a² := a * a
```

of `a` with itself.

## Definitions

### The square of an integer

```agda
square-ℤ : ℤ → ℤ
square-ℤ a = mul-ℤ a a
```

### The cube of an integer

```agda
cube-ℤ : ℤ → ℤ
cube-ℤ a = mul-ℤ (square-ℤ a) a
```

### The predicate on integers of being square

```agda
is-square-ℤ : ℤ → UU lzero
is-square-ℤ a = Σ ℤ (λ x → a ＝ square-ℤ x)
```

### The square root of a square integer

```agda
square-root-ℤ : (a : ℤ) → is-square-ℤ a → ℤ
square-root-ℤ _ (root , _) = root
```

## Properties

### The integer square of a natural number is the integer of its square

```agda
compute-square-int-ℕ : (n : ℕ) → square-ℤ (int-ℕ n) ＝ int-ℕ (square-ℕ n)
compute-square-int-ℕ n = mul-int-ℕ n n
```

### The square of an integer is the square of its absolute value

```agda
compute-square-abs-ℤ : (a : ℤ) → square-ℤ a ＝ int-ℕ (square-ℕ (abs-ℤ a))
compute-square-abs-ℤ (inl x) = compute-mul-ℤ (inl x) (inl x)
compute-square-abs-ℤ (inr (inl star)) = refl
compute-square-abs-ℤ (inr (inr x)) = mul-int-ℕ (succ-ℕ x) (succ-ℕ x)

compute-square-abs-ℤ' :
  (a : ℤ) → square-ℤ a ＝ square-ℤ (int-abs-ℤ a)
compute-square-abs-ℤ' (inl x) =
  compute-mul-ℤ (inl x) (inl x) ∙ inv (mul-int-ℕ (succ-ℕ x) (succ-ℕ x))
compute-square-abs-ℤ' (inr (inl star)) =
  refl
compute-square-abs-ℤ' (inr (inr x)) =
  refl
```

### Squares in ℤ are nonnegative

```agda
is-nonnegative-square-ℤ : (a : ℤ) → is-nonnegative-ℤ (square-ℤ a)
is-nonnegative-square-ℤ a =
  rec-coproduct
    ( λ H → is-nonnegative-is-positive-ℤ (is-positive-mul-negative-ℤ H H))
    ( λ H → is-nonnegative-mul-ℤ H H)
    ( decide-is-negative-is-nonnegative-ℤ {a})

is-nonnegative-is-square-ℤ : {a : ℤ} → is-square-ℤ a → is-nonnegative-ℤ a
is-nonnegative-is-square-ℤ (r , refl) = is-nonnegative-square-ℤ r
```

### The square of an integer is equal to the square of its negative

```agda
compute-square-neg-ℤ :
  (a : ℤ) → square-ℤ a ＝ square-ℤ (neg-ℤ a)
compute-square-neg-ℤ a = inv (double-negative-law-mul-ℤ a a)
```

### The squares in ℤ are exactly the squares in ℕ

```agda
is-square-int-is-square-nat : {n : ℕ} → is-square-ℕ n → is-square-ℤ (int-ℕ n)
is-square-int-is-square-nat (r , refl) =
  ( int-ℕ r , inv (compute-square-int-ℕ r))

is-square-nat-is-square-int : {a : ℤ} → is-square-ℤ a → is-square-ℕ (abs-ℤ a)
is-square-nat-is-square-int (r , refl) =
  ( abs-ℤ r , distributive-abs-mul-ℤ r r)

iff-is-square-int-is-square-nat :
  (n : ℕ) → is-square-ℕ n ↔ is-square-ℤ (int-ℕ n)
pr1 (iff-is-square-int-is-square-nat n) = is-square-int-is-square-nat
pr2 (iff-is-square-int-is-square-nat n) H =
  tr is-square-ℕ (abs-int-ℕ n) (is-square-nat-is-square-int H)

iff-is-nonneg-square-nat-is-square-int :
  (a : ℤ) → is-square-ℤ a ↔ is-nonnegative-ℤ a × is-square-ℕ (abs-ℤ a)
pr1 (iff-is-nonneg-square-nat-is-square-int a) H =
  ( is-nonnegative-is-square-ℤ H , is-square-nat-is-square-int H)
pr2 (iff-is-nonneg-square-nat-is-square-int a) (H , r , p) =
  ( int-ℕ r ,
    inv (int-abs-is-nonnegative-ℤ a H) ∙
    ap int-ℕ p ∙
    inv (compute-square-int-ℕ r))
```

### Being a square integer is decidable

```agda
is-decidable-is-square-ℤ : (a : ℤ) → is-decidable (is-square-ℤ a)
is-decidable-is-square-ℤ (inl n) =
  inr (map-neg (pr1 (iff-is-nonneg-square-nat-is-square-int (inl n))) pr1)
is-decidable-is-square-ℤ (inr (inl n)) = inl (zero-ℤ , refl)
is-decidable-is-square-ℤ (inr (inr n)) =
  is-decidable-iff
    ( is-square-int-is-square-nat)
    ( is-square-nat-is-square-int)
    ( is-decidable-is-square-ℕ (succ-ℕ n))
```

### Squares of successors

For any integer `a` we have the equation

```text
  (a + 1)² ＝ a² + 2a + 1.
```

```agda
square-succ-ℤ :
  (a : ℤ) → square-ℤ (succ-ℤ a) ＝ square-ℤ a +ℤ int-ℕ 2 *ℤ a +ℤ int-ℕ 1
square-succ-ℤ a =
  double-successor-law-mul-ℤ a a ∙
  ap (_+ℤ int-ℕ 1) (associative-add-ℤ (square-ℤ a) a a)
```

### Squares of double successors

For any `n` we have `(n + 2)² ＝ n² + 4n + 4`

```agda
square-succ-succ-ℤ :
  (a : ℤ) →
  square-ℤ (succ-ℤ (succ-ℤ a)) ＝ square-ℤ a +ℤ int-ℕ 4 *ℤ a +ℤ int-ℕ 4
square-succ-succ-ℤ a =
  ap
    ( square-ℤ)
    ( ap succ-ℤ (inv (right-add-one-ℤ a)) ∙
      inv (right-add-one-ℤ (a +ℤ one-ℤ)) ∙
      associative-add-ℤ a one-ℤ one-ℤ) ∙
  double-distributive-mul-add-ℤ a (int-ℕ 2) a (int-ℕ 2) ∙
  inv
    ( associative-add-ℤ (square-ℤ a +ℤ a *ℤ int-ℕ 2) (int-ℕ 2 *ℤ a) (int-ℕ 4)) ∙
  ap
    ( _+ℤ int-ℕ 4)
    ( associative-add-ℤ (square-ℤ a) (a *ℤ int-ℕ 2) (int-ℕ 2 *ℤ a) ∙
      ap
        ( square-ℤ a +ℤ_)
        ( ap (_+ℤ int-ℕ 2 *ℤ a) (commutative-mul-ℤ a (int-ℕ 2)) ∙
          inv (right-distributive-mul-add-ℤ (int-ℕ 2) (int-ℕ 2) a)))
```

### Squares distribute over multiplication

```agda
distributive-square-mul-ℤ :
  (a b : ℤ) → square-ℤ (a *ℤ b) ＝ square-ℤ a *ℤ square-ℤ b
distributive-square-mul-ℤ a b =
  interchange-law-mul-mul-ℤ a b a b
```

### Equivalent characterizations of a number being even in terms of its square

Consider a integer `n`. The following are equivalent:

- The number `n` is even.
- Its square is even.
- Its square is divisible by 4.

```agda
div-four-square-is-even-ℤ :
  (a : ℤ) → is-even-ℤ a → div-ℤ 4 (square-ℤ a)
div-four-square-is-even-ℤ a H = ?
```

```text
div-four-square-is-even-ℤ :
  (a : ℤ) → is-even-ℤ a → div-ℤ 4 (square-ℤ a)
dif-four-square-is-even-ℤ = ?

is-even-square-is-even-ℤ :
  (n : ℤ) → is-even-ℤ n → is-even-ℤ (square-ℤ n)
is-even-square-is-even-ℤ .(m *ℤ 2) (m , refl) =
  is-even-div-4-ℤ _ (div-four-square-is-even-ℤ (m *ℤ 2) (m , refl))

is-even-is-even-square-ℤ :
  (n : ℤ) → is-even-ℤ (square-ℤ n) → is-even-ℤ n
is-even-is-even-square-ℤ zero-ℤ H = is-even-zero-ℤ
is-even-is-even-square-ℤ (succ-ℤ zero-ℤ) (zero-ℤ , ())
is-even-is-even-square-ℤ (succ-ℤ zero-ℤ) (succ-ℤ k , ())
is-even-is-even-square-ℤ (succ-ℤ (succ-ℤ n)) (m , p) =
  is-even-succ-succ-is-even-ℤ n
    ( is-even-is-even-square-ℤ n
      ( is-even-left-summand-ℤ
        ( square-ℤ n)
        ( 4 *ℤ n)
        ( is-even-div-4-ℤ (4 *ℤ n) (n , commutative-mul-ℤ n 4))
        ( is-even-left-summand-ℤ
          ( square-ℤ n +ℤ 4 *ℤ n)
          ( 4)
          ( 2 , refl)
          ( m , p ∙ square-succ-succ-ℤ n))))

is-even-div-four-square-ℤ :
  (n : ℤ) → div-ℤ 4 (square-ℤ n) → is-even-ℤ n
is-even-div-four-square-ℤ n H =
  is-even-is-even-square-ℤ n (is-even-div-4-ℤ (square-ℤ n) H)
```
