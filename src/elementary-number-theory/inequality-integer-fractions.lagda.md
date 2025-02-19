# Inequality on integer fractions

```agda
module elementary-number-theory.inequality-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-positive-and-negative-integers
open import elementary-number-theory.cross-multiplication-difference-integer-fractions
open import elementary-number-theory.difference-integers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.nonpositive-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.strict-inequality-integers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

An [integer fraction](elementary-number-theory.integer-fractions.md) `m/n` is
{{#concept "less or equal" Disambiguation="integer fraction" Agda=leq-fraction-ℤ}}
to a fraction `m'/n'` if the
[integer product](elementary-number-theory.multiplication-integers.md) `m * n'`
is [less or equal](elementary-number-theory.inequality-integers.md) to `m' * n`.

## Definition

### Inequality on integer fractions

```agda
leq-fraction-ℤ-Prop : fraction-ℤ → fraction-ℤ → Prop lzero
leq-fraction-ℤ-Prop (m , n , p) (m' , n' , p') =
  leq-ℤ-Prop (m *ℤ n') (m' *ℤ n)

leq-fraction-ℤ : fraction-ℤ → fraction-ℤ → UU lzero
leq-fraction-ℤ x y = type-Prop (leq-fraction-ℤ-Prop x y)

is-prop-leq-fraction-ℤ : (x y : fraction-ℤ) → is-prop (leq-fraction-ℤ x y)
is-prop-leq-fraction-ℤ x y = is-prop-type-Prop (leq-fraction-ℤ-Prop x y)
```

## Properties

### Inequality on integer fractions is decidable

```agda
is-decidable-leq-fraction-ℤ :
  (x y : fraction-ℤ) → (leq-fraction-ℤ x y) + ¬ (leq-fraction-ℤ x y)
is-decidable-leq-fraction-ℤ x y =
  is-decidable-leq-ℤ
    ( numerator-fraction-ℤ x *ℤ denominator-fraction-ℤ y)
    ( numerator-fraction-ℤ y *ℤ denominator-fraction-ℤ x)

leq-fraction-ℤ-Decidable-Prop : (x y : fraction-ℤ) → Decidable-Prop lzero
leq-fraction-ℤ-Decidable-Prop x y =
  ( leq-fraction-ℤ x y ,
    is-prop-leq-fraction-ℤ x y ,
    is-decidable-leq-fraction-ℤ x y)
```

### Inequality on integer fractions is antisymmetric with respect to the similarity relation

```agda
module _
  (x y : fraction-ℤ)
  where

  is-sim-antisymmetric-leq-fraction-ℤ :
    leq-fraction-ℤ x y →
    leq-fraction-ℤ y x →
    sim-fraction-ℤ x y
  is-sim-antisymmetric-leq-fraction-ℤ H H' =
    sim-is-zero-coss-mul-diff-fraction-ℤ x y
      ( is-zero-is-nonnegative-is-nonpositive-ℤ
        ( H)
        ( is-nonpositive-eq-ℤ
          ( skew-commutative-cross-mul-diff-fraction-ℤ y x)
          ( is-nonpositive-neg-is-nonnegative-ℤ
            ( H'))))
```

### Inequality on integer fractions is transitive

```agda
transitive-leq-fraction-ℤ :
  (p q r : fraction-ℤ) →
  leq-fraction-ℤ q r →
  leq-fraction-ℤ p q →
  leq-fraction-ℤ p r
transitive-leq-fraction-ℤ p q r H H' =
  is-nonnegative-right-factor-mul-ℤ
    ( is-nonnegative-eq-ℤ
      ( lemma-add-cross-mul-diff-fraction-ℤ p q r)
        ( is-nonnegative-add-ℤ
          ( is-nonnegative-mul-ℤ
            ( is-nonnegative-is-positive-ℤ
              ( is-positive-denominator-fraction-ℤ p))
            ( H))
          ( is-nonnegative-mul-ℤ
            ( is-nonnegative-is-positive-ℤ
              ( is-positive-denominator-fraction-ℤ r))
            ( H'))))
    ( is-positive-denominator-fraction-ℤ q)
```

### Chaining rules for similarity and inequality on the integer fractions

```agda
module _
  (p q r : fraction-ℤ)
  where

  concatenate-sim-leq-fraction-ℤ :
    sim-fraction-ℤ p q →
    leq-fraction-ℤ q r →
    leq-fraction-ℤ p r
  concatenate-sim-leq-fraction-ℤ H H' =
    is-nonnegative-right-factor-mul-ℤ
      ( is-nonnegative-eq-ℤ
        ( lemma-left-sim-cross-mul-diff-fraction-ℤ p q r H)
        ( is-nonnegative-mul-ℤ
          ( is-nonnegative-is-positive-ℤ (is-positive-denominator-fraction-ℤ p))
          ( H')))
      ( is-positive-denominator-fraction-ℤ q)

  concatenate-leq-sim-fraction-ℤ :
    leq-fraction-ℤ p q →
    sim-fraction-ℤ q r →
    leq-fraction-ℤ p r
  concatenate-leq-sim-fraction-ℤ H H' =
    is-nonnegative-right-factor-mul-ℤ
      ( is-nonnegative-eq-ℤ
        ( inv (lemma-right-sim-cross-mul-diff-fraction-ℤ p q r H'))
        ( is-nonnegative-mul-ℤ
          ( is-nonnegative-is-positive-ℤ (is-positive-denominator-fraction-ℤ r))
          ( H)))
      ( is-positive-denominator-fraction-ℤ q)
```

### The similarity of integer fractions preserves inequality

```agda
module _
  (p q p' q' : fraction-ℤ) (H : sim-fraction-ℤ p p') (K : sim-fraction-ℤ q q')
  where

  leq-sim-fraction-ℤ : leq-fraction-ℤ p q → leq-fraction-ℤ p' q'
  leq-sim-fraction-ℤ I =
    concatenate-sim-leq-fraction-ℤ p' p q'
      ( symmetric-sim-fraction-ℤ p p' H)
      ( concatenate-leq-sim-fraction-ℤ p q q' I K)
```

### `x ≤ y` if and only if `0 ≤ y - x`

```agda
module _
  (x y : fraction-ℤ)
  where

  eq-translate-diff-leq-zero-fraction-ℤ :
    leq-fraction-ℤ zero-fraction-ℤ (y +fraction-ℤ (neg-fraction-ℤ x)) ＝
    leq-fraction-ℤ x y
  eq-translate-diff-leq-zero-fraction-ℤ =
    ap
      ( is-nonnegative-ℤ)
      ( ( cross-mul-diff-zero-fraction-ℤ (y +fraction-ℤ (neg-fraction-ℤ x))) ∙
        ( ap
          ( add-ℤ ( (numerator-fraction-ℤ y) *ℤ (denominator-fraction-ℤ x)))
          ( left-negative-law-mul-ℤ
            ( numerator-fraction-ℤ x)
            ( denominator-fraction-ℤ y))))
```
