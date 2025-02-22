# Inequality on the integers

```agda
module elementary-number-theory.inequality-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-positive-and-negative-integers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.negative-integers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.nonpositive-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

An [integer](elementary-number-theory.integers.md) `x` is _less than or equal_
to the integer `y` if the
[difference](elementary-number-theory.difference-integers.md) `y - x` is
[nonnegative](elementary-number-theory.nonnegative-integers.md). This relation
defines the
{{#concept "standard ordering" Disambiguation="integers" Agda=leq-ℤ}} on the
integers.

Alternatively, the standard ordering can be defined as a `data` type by
specifying the constructors

```text
  r : (x : ℤ) → x ≤ x
  s : (x y : ℤ) → x ≤ y → x ≤ y + 1.
```

We will introduce both orderings and prove that they are equivalent.

## Definition

### Inequality on the integers

```agda
leq-ℤ-Prop : ℤ → ℤ → Prop lzero
leq-ℤ-Prop a b = subtype-nonnegative-ℤ (b -ℤ a)

leq-ℤ : ℤ → ℤ → UU lzero
leq-ℤ a b = type-Prop (leq-ℤ-Prop a b)

is-prop-leq-ℤ : (a b : ℤ) → is-prop (leq-ℤ a b)
is-prop-leq-ℤ a b = is-prop-type-Prop (leq-ℤ-Prop a b)

infix 30 _≤-ℤ_
_≤-ℤ_ = leq-ℤ
```

### Inductive definition of inequality on the integers

```agda
data
  inductive-leq-ℤ :
    ℤ → ℤ → UU lzero
  where

  refl-inductive-leq-ℤ :
    (a : ℤ) → inductive-leq-ℤ a a

  succ-inductive-leq-ℤ :
    (a b : ℤ) → inductive-leq-ℤ a b → inductive-leq-ℤ a (succ-ℤ b)

refl-inductive-leq-ℤ' :
  (a b : ℤ) → a ＝ b → inductive-leq-ℤ a b
refl-inductive-leq-ℤ' a .a refl = refl-inductive-leq-ℤ a

succ-inductive-leq-ℤ' :
  (a b c : ℤ) (p : succ-ℤ b ＝ c) → inductive-leq-ℤ a b → inductive-leq-ℤ a c
succ-inductive-leq-ℤ' a b .(succ-ℤ b) refl H = succ-inductive-leq-ℤ a b H
```

## Properties

### Inequality on the integers is reflexive, antisymmetric and transitive

```agda
refl-leq-ℤ : (a : ℤ) → a ≤-ℤ a
refl-leq-ℤ a = tr is-nonnegative-ℤ (inv (right-inverse-law-add-ℤ a)) star

antisymmetric-leq-ℤ : {a b : ℤ} → a ≤-ℤ b → b ≤-ℤ a → a ＝ b
antisymmetric-leq-ℤ {a} {b} H K =
  eq-diff-ℤ
    ( is-zero-is-nonnegative-neg-is-nonnegative-ℤ K
      ( is-nonnegative-eq-ℤ (inv (distributive-neg-diff-ℤ a b)) H))

transitive-leq-ℤ : (a b c : ℤ) → b ≤-ℤ c → a ≤-ℤ b → a ≤-ℤ c
transitive-leq-ℤ a b c H K =
  is-nonnegative-eq-ℤ
    ( triangle-diff-ℤ c b a)
    ( is-nonnegative-add-ℤ H K)
```

### Inequality on the integers is decidable

```agda
is-decidable-leq-ℤ : (a b : ℤ) → is-decidable (a ≤-ℤ b)
is-decidable-leq-ℤ a b = is-decidable-is-nonnegative-ℤ (b -ℤ a)

leq-ℤ-Decidable-Prop : (a b : ℤ) → Decidable-Prop lzero
pr1 (leq-ℤ-Decidable-Prop a b) = a ≤-ℤ b
pr1 (pr2 (leq-ℤ-Decidable-Prop a b)) = is-prop-leq-ℤ a b
pr2 (pr2 (leq-ℤ-Decidable-Prop a b)) = is-decidable-leq-ℤ a b
```

### Inequality on the integers is linear

```agda
linear-leq-ℤ : (a b : ℤ) → (a ≤-ℤ b) + (b ≤-ℤ a)
linear-leq-ℤ a b =
  map-coproduct
    ( λ H →
      is-nonnegative-is-positive-ℤ
        ( is-positive-eq-ℤ
          ( distributive-neg-diff-ℤ a b)
          ( is-positive-neg-is-negative-ℤ H)))
    ( id)
    ( decide-is-negative-is-nonnegative-ℤ)
```

### Chaining rules for equality and inequality

```agda
concatenate-eq-leq-eq-ℤ :
  {a b c d : ℤ} → a ＝ b → b ≤-ℤ c → c ＝ d → a ≤-ℤ d
concatenate-eq-leq-eq-ℤ refl H refl = H

concatenate-leq-eq-ℤ :
  (a : ℤ) {b c : ℤ} → a ≤-ℤ b → b ＝ c → a ≤-ℤ c
concatenate-leq-eq-ℤ a H refl = H

concatenate-eq-leq-ℤ :
  {a b : ℤ} (c : ℤ) → a ＝ b → b ≤-ℤ c → a ≤-ℤ c
concatenate-eq-leq-ℤ c refl H = H
```

### An integer is lesser than its successor

```agda
succ-leq-ℤ : (a : ℤ) → a ≤-ℤ succ-ℤ a
succ-leq-ℤ a =
  is-nonnegative-eq-ℤ
    ( inv
      ( ( left-successor-law-add-ℤ a (neg-ℤ a)) ∙
        ( ap succ-ℤ (right-inverse-law-add-ℤ a))))
    ( star)

leq-succ-leq-ℤ : (a b : ℤ) → a ≤-ℤ b → a ≤-ℤ succ-ℤ b
leq-succ-leq-ℤ a b = transitive-leq-ℤ a b (succ-ℤ b) (succ-leq-ℤ b)
```

### Inequality on the integers is equivalent to the inductively defined inequality on the integers

```agda
leq-inductive-leq-ℤ :
  (a b : ℤ) → inductive-leq-ℤ a b → a ≤-ℤ b
leq-inductive-leq-ℤ a .a (refl-inductive-leq-ℤ .a) =
  refl-leq-ℤ a
leq-inductive-leq-ℤ a .(succ-ℤ b) (succ-inductive-leq-ℤ .a b H) =
  leq-succ-leq-ℤ a b (leq-inductive-leq-ℤ a b H)

inductive-leq-leq-ℤ' :
  (a b c : ℤ) (p : diff-ℤ b a ＝ c) → is-nonnegative-ℤ c → inductive-leq-ℤ a b
inductive-leq-leq-ℤ' a b (inr (inl star)) p H =
  refl-inductive-leq-ℤ' a b (inv (eq-diff-ℤ p))
inductive-leq-leq-ℤ' a b (inr (inr zero-ℕ)) p star =
  succ-inductive-leq-ℤ' a a b
    ( is-left-add-one-succ-ℤ a ∙
      ap (_+ℤ a) (inv p) ∙
      is-section-right-add-neg-ℤ a b)
    ( refl-inductive-leq-ℤ a)
inductive-leq-leq-ℤ' a b (inr (inr (succ-ℕ x))) p star =
  succ-inductive-leq-ℤ' a
    ( a +ℤ inr (inr x))
    ( b)
    ( inv (right-successor-law-add-ℤ a (inr (inr x))) ∙
      ap (a +ℤ_) (inv p) ∙
      commutative-add-ℤ a (diff-ℤ b a) ∙
      is-section-right-add-neg-ℤ a b)
    ( inductive-leq-leq-ℤ' a
      ( a +ℤ inr (inr x))
      ( inr (inr x))
      ( commutative-add-ℤ (a +ℤ inr (inr x)) (neg-ℤ a) ∙
        is-retraction-left-add-neg-ℤ a (inr (inr x)))
      ( star))

inductive-leq-leq-ℤ :
  (a b : ℤ) → a ≤-ℤ b → inductive-leq-ℤ a b
inductive-leq-leq-ℤ a b =
  inductive-leq-leq-ℤ' a b (diff-ℤ b a) refl
```

### Addition on the integers preserves inequality

```agda
preserves-order-left-add-ℤ :
  (c a b : ℤ) → a ≤-ℤ b → a +ℤ c ≤-ℤ b +ℤ c
preserves-order-left-add-ℤ c a b =
  is-nonnegative-eq-ℤ (inv (right-translation-diff-ℤ b a c))

preserves-order-right-add-ℤ :
  (c a b : ℤ) → a ≤-ℤ b → c +ℤ a ≤-ℤ c +ℤ b
preserves-order-right-add-ℤ c a b =
  is-nonnegative-eq-ℤ (inv (left-translation-diff-ℤ b a c))

preserves-order-add-ℤ :
  {a b c d : ℤ} → a ≤-ℤ b → c ≤-ℤ d → a +ℤ c ≤-ℤ b +ℤ d
preserves-order-add-ℤ {a} {b} {c} {d} H K =
  transitive-leq-ℤ
    ( a +ℤ c)
    ( b +ℤ c)
    ( b +ℤ d)
    ( preserves-order-right-add-ℤ b c d K)
    ( preserves-order-left-add-ℤ c a b H)
```

### Addition on the integers reflects inequality

```agda
reflects-order-left-add-ℤ :
  (c a b : ℤ) → a +ℤ c ≤-ℤ b +ℤ c → a ≤-ℤ b
reflects-order-left-add-ℤ c a b =
  is-nonnegative-eq-ℤ (right-translation-diff-ℤ b a c)

reflects-order-right-add-ℤ :
  (c a b : ℤ) → c +ℤ a ≤-ℤ c +ℤ b → a ≤-ℤ b
reflects-order-right-add-ℤ c a b =
  is-nonnegative-eq-ℤ (left-translation-diff-ℤ b a c)
```

### The inclusion of ℕ into ℤ preserves inequality

```agda
leq-int-ℕ : (m n : ℕ) → m ≤-ℕ n → int-ℕ m ≤-ℤ int-ℕ n
leq-int-ℕ zero-ℕ n H =
  tr
    ( is-nonnegative-ℤ)
    ( inv (right-unit-law-add-ℤ (int-ℕ n)))
    ( is-nonnegative-int-ℕ n)
leq-int-ℕ (succ-ℕ m) (succ-ℕ n) H = tr (is-nonnegative-ℤ)
  ( inv (diff-succ-ℤ (int-ℕ n) (int-ℕ m)) ∙
    ( ap (_-ℤ (succ-ℤ (int-ℕ m))) (succ-int-ℕ n) ∙
      ap ((int-ℕ (succ-ℕ n)) -ℤ_) (succ-int-ℕ m)))
  ( leq-int-ℕ m n H)
```

### Transposing summands in inequalities

```agda
transpose-left-summand-leq-ℤ :
  (a b c : ℤ) → a ≤-ℤ b +ℤ c → neg-ℤ b +ℤ a ≤-ℤ c
transpose-left-summand-leq-ℤ a b c H =
  reflects-order-right-add-ℤ b
    ( neg-ℤ b +ℤ a)
    ( c)
    ( concatenate-eq-leq-ℤ (b +ℤ c) (is-section-left-add-neg-ℤ b a) H)

inv-transpose-left-summand-leq-ℤ :
  (a b c : ℤ) → neg-ℤ b +ℤ a ≤-ℤ c → a ≤-ℤ b +ℤ c
inv-transpose-left-summand-leq-ℤ a b c H =
  concatenate-eq-leq-ℤ
    ( b +ℤ c)
    ( inv (is-section-left-add-neg-ℤ b a))
    ( preserves-order-right-add-ℤ b (neg-ℤ b +ℤ a) c H)

transpose-left-summand-leq-ℤ' :
  (a b c : ℤ) → b +ℤ a ≤-ℤ c → a ≤-ℤ neg-ℤ b +ℤ c
transpose-left-summand-leq-ℤ' a b c H =
  inv-transpose-left-summand-leq-ℤ a (neg-ℤ b) c
    ( concatenate-eq-leq-ℤ c (ap (add-ℤ' a) (neg-neg-ℤ b)) H)

inv-transpose-left-summand-leq-ℤ' :
  (a b c : ℤ) → a ≤-ℤ neg-ℤ b +ℤ c → b +ℤ a ≤-ℤ c
inv-transpose-left-summand-leq-ℤ' a b c H =
  concatenate-eq-leq-ℤ c
    ( ap (add-ℤ' a) (inv (neg-neg-ℤ b)))
    ( transpose-left-summand-leq-ℤ a (neg-ℤ b) c H)

transpose-right-summand-leq-ℤ :
  (a b c : ℤ) → a ≤-ℤ b +ℤ c → a +ℤ neg-ℤ c ≤-ℤ b
transpose-right-summand-leq-ℤ a b c H =
  reflects-order-left-add-ℤ c
    ( a +ℤ neg-ℤ c)
    ( b)
    ( concatenate-eq-leq-ℤ (b +ℤ c) (is-section-right-add-neg-ℤ c a) H)

inv-transpose-right-summand-leq-ℤ :
  (a b c : ℤ) → a +ℤ neg-ℤ c ≤-ℤ b → a ≤-ℤ b +ℤ c
inv-transpose-right-summand-leq-ℤ a b c H =
  concatenate-eq-leq-ℤ
    ( b +ℤ c)
    ( inv (is-section-right-add-neg-ℤ c a))
    ( preserves-order-left-add-ℤ c (a +ℤ neg-ℤ c) b H)

transpose-right-summand-leq-ℤ' :
  (a b c : ℤ) → a +ℤ c ≤-ℤ b → a ≤-ℤ b +ℤ neg-ℤ c
transpose-right-summand-leq-ℤ' a b c H =
  inv-transpose-right-summand-leq-ℤ a b
    ( neg-ℤ c)
    ( concatenate-eq-leq-ℤ b (ap (add-ℤ a) (neg-neg-ℤ c)) H)

inv-transpose-right-summand-leq-ℤ' :
  (a b c : ℤ) → a ≤-ℤ b +ℤ neg-ℤ c → a +ℤ c ≤-ℤ b
inv-transpose-right-summand-leq-ℤ' a b c H =
  concatenate-eq-leq-ℤ b
    ( ap (add-ℤ a) (inv (neg-neg-ℤ c)))
    ( transpose-right-summand-leq-ℤ a b (neg-ℤ c) H)
```

### The operation taking integers to their negatives reverses their order

**Proof.** If `a ≤ b`, then `b - a` is nonnegative. Note that
`b - a ＝ (-a) - (-b)`, which is therefore also nonnegative, implying that
`-b ≤ -a`.

```agda
reverses-order-neg-ℤ :
  (a b : ℤ) → a ≤-ℤ b → neg-ℤ b ≤-ℤ neg-ℤ a
reverses-order-neg-ℤ a b =
  tr
    ( is-nonnegative-ℤ)
    ( ( commutative-add-ℤ b (neg-ℤ a)) ∙
      ( ap (add-ℤ (neg-ℤ a)) (inv (neg-neg-ℤ b))))
```

### The operation taking integers to their negative reversely reflects their order

```agda
reversely-reflects-order-neg-ℤ :
  (a b : ℤ) → neg-ℤ a ≤-ℤ neg-ℤ b → b ≤-ℤ a
reversely-reflects-order-neg-ℤ a b =
  tr
    ( is-nonnegative-ℤ)
    ( ap (add-ℤ (neg-ℤ b)) (neg-neg-ℤ a) ∙ commutative-add-ℤ (neg-ℤ b) a)
```

### Transposing negatives in inequalities

```agda
transpose-right-neg-leq-ℤ :
  (a b : ℤ) → b ≤-ℤ neg-ℤ a → a ≤-ℤ neg-ℤ b
transpose-right-neg-leq-ℤ a b H =
  reversely-reflects-order-neg-ℤ
    ( neg-ℤ b)
    ( a)
    ( concatenate-eq-leq-ℤ (neg-ℤ a) (neg-neg-ℤ b) H)

transpose-left-neg-leq-ℤ :
  (a b : ℤ) → neg-ℤ b ≤-ℤ a → neg-ℤ a ≤-ℤ b
transpose-left-neg-leq-ℤ a b H =
  reversely-reflects-order-neg-ℤ b
    ( neg-ℤ a)
    ( concatenate-leq-eq-ℤ (neg-ℤ b) H (inv (neg-neg-ℤ a)))
```

### An integer `a` is nonnegative if and only if `0 ≤ a`

```agda
module _
  (a : ℤ)
  where

  abstract
    leq-zero-is-nonnegative-ℤ : is-nonnegative-ℤ a → zero-ℤ ≤-ℤ a
    leq-zero-is-nonnegative-ℤ =
      is-nonnegative-eq-ℤ (inv (right-zero-law-diff-ℤ a))

    is-nonnegative-leq-zero-ℤ : zero-ℤ ≤-ℤ a → is-nonnegative-ℤ a
    is-nonnegative-leq-zero-ℤ =
      is-nonnegative-eq-ℤ (right-zero-law-diff-ℤ a)
```

### An integer greater than or equal to a nonnegative integer is nonnegative

```agda
module _
  (a b : ℤ) (I : a ≤-ℤ b)
  where

  abstract
    is-nonnegative-leq-nonnegative-ℤ : is-nonnegative-ℤ a → is-nonnegative-ℤ b
    is-nonnegative-leq-nonnegative-ℤ H =
      is-nonnegative-leq-zero-ℤ b
        ( transitive-leq-ℤ
          ( zero-ℤ)
          ( a)
          ( b)
          ( I)
          ( leq-zero-is-nonnegative-ℤ a H))
```

### An integer `a` is nonpositive if and only if `a ≤ 0`

```agda
module _
  (a : ℤ)
  where

  abstract
    leq-zero-is-nonpositive-ℤ : is-nonpositive-ℤ a → a ≤-ℤ zero-ℤ
    leq-zero-is-nonpositive-ℤ = is-nonnegative-neg-is-nonpositive-ℤ

    is-nonpositive-leq-zero-ℤ : a ≤-ℤ zero-ℤ → is-nonpositive-ℤ a
    is-nonpositive-leq-zero-ℤ H =
      is-nonpositive-eq-ℤ
        ( neg-neg-ℤ a)
        ( is-nonpositive-neg-is-nonnegative-ℤ H)
```

### An integer less than or equal to a nonpositive integer is nonpositive

```agda
module _
  (a b : ℤ) (I : a ≤-ℤ b)
  where

  abstract
    is-nonpositive-leq-nonpositive-ℤ : is-nonpositive-ℤ b → is-nonpositive-ℤ a
    is-nonpositive-leq-nonpositive-ℤ H =
      is-nonpositive-leq-zero-ℤ a
        ( transitive-leq-ℤ
          ( a)
          ( b)
          ( zero-ℤ)
          ( leq-zero-is-nonpositive-ℤ b H)
          ( I))
```

### A positive integer is greater than or equal to `0`

```agda
leq-zero-is-positive-ℤ :
  (a : ℤ) → is-positive-ℤ a → zero-ℤ ≤-ℤ a
leq-zero-is-positive-ℤ a H =
  leq-zero-is-nonnegative-ℤ a (is-nonnegative-is-positive-ℤ H)
```

## See also

- The decidable total order on the integers is defined in
  [`decidable-total-order-integers`](elementary-number-theory.decidable-total-order-integers.md)
- Strict inequality on the integers is defined in
  [`strict-inequality-integers`](elementary-number-theory.strict-inequality-integers.md)
