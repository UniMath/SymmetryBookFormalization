# Relatively prime natural numbers

```agda
module elementary-number-theory.relatively-prime-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.greatest-common-divisor-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers

open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

Two natural numbers `x` and `y` are said to be relatively prime if their
greatest common divisor is `1`.

## Definition

```agda
is-relatively-prime-ℕ : ℕ → ℕ → UU lzero
is-relatively-prime-ℕ x y = is-one-ℕ (gcd-ℕ x y)
```

## Properties

### Being relatively prime is a proposition

```agda
is-prop-is-relatively-prime-ℕ : (x y : ℕ) → is-prop (is-relatively-prime-ℕ x y)
is-prop-is-relatively-prime-ℕ x y = is-set-ℕ (gcd-ℕ x y) 1

is-relatively-prime-ℕ-Prop : ℕ → ℕ → Prop lzero
pr1 (is-relatively-prime-ℕ-Prop x y) = is-relatively-prime-ℕ x y
pr2 (is-relatively-prime-ℕ-Prop x y) = is-prop-is-relatively-prime-ℕ x y
```

### Being relatively prime is decidable

```agda
is-decidable-is-relatively-prime-ℕ :
  (x y : ℕ) → is-decidable (is-relatively-prime-ℕ x y)
is-decidable-is-relatively-prime-ℕ x y = is-decidable-is-one-ℕ (gcd-ℕ x y)

is-decidable-prop-is-relatively-prime-ℕ :
  (x y : ℕ) → is-decidable-prop (is-relatively-prime-ℕ x y)
pr1 (is-decidable-prop-is-relatively-prime-ℕ x y) =
  is-prop-is-relatively-prime-ℕ x y
pr2 (is-decidable-prop-is-relatively-prime-ℕ x y) =
  is-decidable-is-relatively-prime-ℕ x y

is-relatively-prime-ℕ-Decidable-Prop :
  (x y : ℕ) → Decidable-Prop lzero
pr1 (is-relatively-prime-ℕ-Decidable-Prop x y) =
  is-relatively-prime-ℕ x y
pr2 (is-relatively-prime-ℕ-Decidable-Prop x y) =
  is-decidable-prop-is-relatively-prime-ℕ x y
```

### `a` and `b` are relatively prime if and only if any common divisor is equal to `1`

```agda
is-one-is-common-divisor-is-relatively-prime-ℕ :
  (x y d : ℕ) →
  is-relatively-prime-ℕ x y → is-common-divisor-ℕ x y d → is-one-ℕ d
is-one-is-common-divisor-is-relatively-prime-ℕ x y d H K =
  is-one-div-one-ℕ d
    ( tr
      ( div-ℕ d)
      ( H)
      ( div-gcd-is-common-divisor-ℕ x y d K))

is-relatively-prime-is-one-is-common-divisor-ℕ :
  (x y : ℕ) →
  ((d : ℕ) → is-common-divisor-ℕ x y d → is-one-ℕ d) → is-relatively-prime-ℕ x y
is-relatively-prime-is-one-is-common-divisor-ℕ x y H =
  H (gcd-ℕ x y) (is-common-divisor-gcd-ℕ x y)
```

### If `a` and `b` are relatively prime, then so are any divisors of `a` and `b`

```agda
is-relatively-prime-div-ℕ :
  (a b c d : ℕ) → div-ℕ c a → div-ℕ d b →
  is-relatively-prime-ℕ a b → is-relatively-prime-ℕ c d
is-relatively-prime-div-ℕ a b c d H K L =
  is-one-is-common-divisor-is-relatively-prime-ℕ a b
    ( gcd-ℕ c d)
    ( L)
    ( transitive-div-ℕ (gcd-ℕ c d) c a H (div-left-factor-gcd-ℕ c d) ,
      transitive-div-ℕ (gcd-ℕ c d) d b K (div-right-factor-gcd-ℕ c d))
```

### For any two natural numbers `a` and `b` such that `a + b ≠ 0`, the numbers `a/gcd(a,b)` and `b/gcd(a,b)` are relatively prime

```agda
is-relatively-prime-quotient-div-gcd-ℕ :
  (a b : ℕ) → is-nonzero-ℕ (a +ℕ b) →
  is-relatively-prime-ℕ
    ( quotient-div-ℕ (gcd-ℕ a b) a (div-left-factor-gcd-ℕ a b))
    ( quotient-div-ℕ (gcd-ℕ a b) b (div-right-factor-gcd-ℕ a b))
is-relatively-prime-quotient-div-gcd-ℕ a b nz =
  ( uniqueness-is-gcd-ℕ
    ( quotient-div-ℕ (gcd-ℕ a b) a (div-left-factor-gcd-ℕ a b))
    ( quotient-div-ℕ (gcd-ℕ a b) b (div-right-factor-gcd-ℕ a b))
    ( gcd-ℕ
      ( quotient-div-ℕ (gcd-ℕ a b) a (div-left-factor-gcd-ℕ a b))
      ( quotient-div-ℕ (gcd-ℕ a b) b (div-right-factor-gcd-ℕ a b)))
    ( quotient-div-ℕ
      ( gcd-ℕ a b)
      ( gcd-ℕ a b)
      ( div-gcd-is-common-divisor-ℕ a b
        ( gcd-ℕ a b)
        ( is-common-divisor-gcd-ℕ a b)))
    ( is-gcd-gcd-ℕ
      ( quotient-div-ℕ (gcd-ℕ a b) a (div-left-factor-gcd-ℕ a b))
      ( quotient-div-ℕ (gcd-ℕ a b) b (div-right-factor-gcd-ℕ a b)))
    ( is-gcd-quotient-div-gcd-ℕ (is-common-divisor-gcd-ℕ a b))) ∙
  ( is-idempotent-quotient-div-ℕ
    ( gcd-ℕ a b)
    ( is-nonzero-gcd-ℕ a b nz)
    ( div-gcd-is-common-divisor-ℕ a b
      ( gcd-ℕ a b)
      ( is-common-divisor-gcd-ℕ a b)))
```

### If `a` and `b` are prime and distinct, then they are relatively prime

```agda
module _
  (a b : ℕ)
  (pa : is-prime-ℕ a)
  (pb : is-prime-ℕ b)
  (n : a ≠ b)
  where

  is-one-is-common-divisor-is-prime-ℕ :
    (d : ℕ) → is-common-divisor-ℕ a b d → is-one-ℕ d
  is-one-is-common-divisor-is-prime-ℕ d c =
    pr1
      ( pa d)
      ( ( λ e →
          is-not-one-is-prime-ℕ
            ( a)
            ( pa)
            ( pr1 (pb a) (n , (tr (λ x → div-ℕ x b) e (pr2 c))))) ,
        ( pr1 c))

  is-relatively-prime-is-prime-ℕ :
    is-relatively-prime-ℕ a b
  is-relatively-prime-is-prime-ℕ =
    is-relatively-prime-is-one-is-common-divisor-ℕ
      ( a)
      ( b)
      ( is-one-is-common-divisor-is-prime-ℕ)
```
