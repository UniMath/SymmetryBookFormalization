# Strict inequality on the rational numbers

```agda
module elementary-number-theory.strict-inequality-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.cross-multiplication-difference-integer-fractions
open import elementary-number-theory.difference-integers
open import elementary-number-theory.inequality-integer-fractions
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.mediant-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.nonpositive-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions
open import elementary-number-theory.strict-inequality-integer-fractions
open import elementary-number-theory.strict-inequality-integers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "standard strict ordering" Disambiguation="rational numbers" Agda=le-ℚ}}
on the [rational numbers](elementary-number-theory.rational-numbers.md) is
inherited from the
[standard strict ordering](elementary-number-theory.strict-inequality-integer-fractions.md)
on [integer fractions](elementary-number-theory.integer-fractions.md): the
rational number `m / n` is _strictly less than_ `m' / n'` if the
[integer product](elementary-number-theory.multiplication-integers.md) `m * n'`
is [strictly less](elementary-number-theory.strict-inequality-integers.md) than
`m' * n`.

## Definition

### The standard strict inequality on the rational numbers

```agda
le-ℚ-Prop : ℚ → ℚ → Prop lzero
le-ℚ-Prop (x , px) (y , py) = le-fraction-ℤ-Prop x y

le-ℚ : ℚ → ℚ → UU lzero
le-ℚ x y = type-Prop (le-ℚ-Prop x y)

is-prop-le-ℚ : (x y : ℚ) → is-prop (le-ℚ x y)
is-prop-le-ℚ x y = is-prop-type-Prop (le-ℚ-Prop x y)
```

## Properties

### Strict inequality on the rational numbers is decidable

```agda
is-decidable-le-ℚ : (x y : ℚ) → (le-ℚ x y) + ¬ (le-ℚ x y)
is-decidable-le-ℚ x y =
  is-decidable-le-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)

le-ℚ-Decidable-Prop : (x y : ℚ) → Decidable-Prop lzero
le-ℚ-Decidable-Prop x y =
  ( le-ℚ x y ,
    is-prop-le-ℚ x y ,
    is-decidable-le-ℚ x y)
```

### Strict inequality on the rational numbers implies inequality

```agda
leq-le-ℚ : {x y : ℚ} → le-ℚ x y → leq-ℚ x y
leq-le-ℚ {x} {y} = leq-le-fraction-ℤ {fraction-ℚ x} {fraction-ℚ y}
```

### Strict inequality on the rationals is asymmetric

```agda
asymmetric-le-ℚ : (x y : ℚ) → le-ℚ x y → ¬ (le-ℚ y x)
asymmetric-le-ℚ x y =
  asymmetric-le-fraction-ℤ
    ( fraction-ℚ x)
    ( fraction-ℚ y)

irreflexive-le-ℚ : (x : ℚ) → ¬ (le-ℚ x x)
irreflexive-le-ℚ =
  is-irreflexive-is-asymmetric le-ℚ asymmetric-le-ℚ
```

### Strict inequality on the rationals is transitive

```agda
module _
  (x y z : ℚ)
  where

  transitive-le-ℚ : le-ℚ y z → le-ℚ x y → le-ℚ x z
  transitive-le-ℚ =
    transitive-le-fraction-ℤ
      ( fraction-ℚ x)
      ( fraction-ℚ y)
      ( fraction-ℚ z)
```

### Concatenation rules for inequality and strict inequality on the rational numbers

```agda
module _
  (x y z : ℚ)
  where

  concatenate-le-leq-ℚ : le-ℚ x y → leq-ℚ y z → le-ℚ x z
  concatenate-le-leq-ℚ =
    concatenate-le-leq-fraction-ℤ
      ( fraction-ℚ x)
      ( fraction-ℚ y)
      ( fraction-ℚ z)

  concatenate-leq-le-ℚ : leq-ℚ x y → le-ℚ y z → le-ℚ x z
  concatenate-leq-le-ℚ =
    concatenate-leq-le-fraction-ℤ
      ( fraction-ℚ x)
      ( fraction-ℚ y)
      ( fraction-ℚ z)
```

### The canonical map from integer fractions to the rational numbers preserves strict inequality

```agda
module _
  (p q : fraction-ℤ)
  where

  preserves-le-rational-fraction-ℤ :
    le-fraction-ℤ p q → le-ℚ (rational-fraction-ℤ p) (rational-fraction-ℤ q)
  preserves-le-rational-fraction-ℤ =
    preserves-le-sim-fraction-ℤ
      ( p)
      ( q)
      ( reduce-fraction-ℤ p)
      ( reduce-fraction-ℤ q)
      ( sim-reduced-fraction-ℤ p)
      ( sim-reduced-fraction-ℤ q)

module _
  (x : ℚ) (p : fraction-ℤ)
  where

  preserves-le-right-rational-fraction-ℤ :
    le-fraction-ℤ (fraction-ℚ x) p → le-ℚ x (rational-fraction-ℤ p)
  preserves-le-right-rational-fraction-ℤ H =
    concatenate-le-sim-fraction-ℤ
      ( fraction-ℚ x)
      ( p)
      ( fraction-ℚ ( rational-fraction-ℤ p))
      ( H)
      ( sim-reduced-fraction-ℤ p)

  preserves-le-left-rational-fraction-ℤ :
    le-fraction-ℤ p (fraction-ℚ x) → le-ℚ (rational-fraction-ℤ p) x
  preserves-le-left-rational-fraction-ℤ =
    concatenate-sim-le-fraction-ℤ
      ( fraction-ℚ ( rational-fraction-ℤ p))
      ( p)
      ( fraction-ℚ x)
      ( symmetric-sim-fraction-ℤ
        ( p)
        ( fraction-ℚ ( rational-fraction-ℤ p))
        ( sim-reduced-fraction-ℤ p))
```

### The rational numbers have no lower or upper bound

```agda
module _
  (x : ℚ)
  where

  exists-lesser-ℚ : exists ℚ (λ q → le-ℚ-Prop q x)
  exists-lesser-ℚ =
    intro-exists
      ( rational-fraction-ℤ frac)
      ( preserves-le-left-rational-fraction-ℤ x frac
        ( le-fraction-le-numerator-fraction-ℤ
          ( frac)
          ( fraction-ℚ x)
          ( refl)
          ( le-pred-ℤ (numerator-ℚ x))))
    where
    frac : fraction-ℤ
    frac = (pred-ℤ (numerator-ℚ x) , positive-denominator-ℚ x)

  exists-greater-ℚ : exists ℚ (λ r → le-ℚ-Prop x r)
  exists-greater-ℚ =
    intro-exists
      ( rational-fraction-ℤ frac)
      ( preserves-le-right-rational-fraction-ℤ x frac
        ( le-fraction-le-numerator-fraction-ℤ
          ( fraction-ℚ x)
          ( frac)
          ( refl)
          ( le-succ-ℤ (numerator-ℚ x))))
    where
    frac : fraction-ℤ
    frac = (succ-ℤ (numerator-ℚ x) , positive-denominator-ℚ x)
```

### For any two rational numbers `x` and `y`, either `x < y` or `y ≤ x`

```agda
decide-le-leq-ℚ : (x y : ℚ) → le-ℚ x y + leq-ℚ y x
decide-le-leq-ℚ x y =
  map-coproduct
    ( id)
    ( λ H →
      is-nonnegative-eq-ℤ
        ( skew-commutative-cross-mul-diff-fraction-ℤ
          ( fraction-ℚ x)
          ( fraction-ℚ y))
        ( is-nonnegative-neg-is-nonpositive-ℤ H))
    ( decide-is-positive-is-nonpositive-ℤ)
```

### Trichotomy on the rationals

```agda
trichotomy-le-ℚ :
  {l : Level} {A : UU l} (x y : ℚ) →
  ( le-ℚ x y → A) →
  ( Id x y → A) →
  ( le-ℚ y x → A) →
  A
trichotomy-le-ℚ x y left eq right with decide-le-leq-ℚ x y | decide-le-leq-ℚ y x
... | inl I | _ = left I
... | inr I | inl I' = right I'
... | inr I | inr I' = eq (antisymmetric-leq-ℚ x y I' I)
```

### The mediant of two distinct rationals is strictly between them

```agda
module _
  (x y : ℚ) (H : le-ℚ x y)
  where

  le-left-mediant-ℚ : le-ℚ x (mediant-ℚ x y)
  le-left-mediant-ℚ =
    preserves-le-right-rational-fraction-ℤ x
      ( mediant-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
      ( le-left-mediant-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y) H)

  le-right-mediant-ℚ : le-ℚ (mediant-ℚ x y) y
  le-right-mediant-ℚ =
    preserves-le-left-rational-fraction-ℤ y
      ( mediant-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
      ( le-right-mediant-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y) H)
```

### Strict inequality on the rational numbers is dense

```agda
module _
  (x y : ℚ) (H : le-ℚ x y)
  where

  dense-le-ℚ : exists ℚ (λ r → le-ℚ-Prop x r ∧ le-ℚ-Prop r y)
  dense-le-ℚ =
    intro-exists
      ( mediant-ℚ x y)
      ( le-left-mediant-ℚ x y H , le-right-mediant-ℚ x y H)
```

### Strict inequality on the rational numbers is located

```agda
located-le-ℚ :
  (x y z : ℚ) → le-ℚ y z → type-disjunction-Prop (le-ℚ-Prop y x) (le-ℚ-Prop x z)
located-le-ℚ x y z H =
  unit-trunc-Prop
    ( map-coproduct
      ( id)
      ( λ p → concatenate-leq-le-ℚ x y z p H)
      ( decide-le-leq-ℚ y x))
```
