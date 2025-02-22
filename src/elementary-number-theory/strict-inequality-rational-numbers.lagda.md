# Strict inequality on the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.strict-inequality-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.cross-multiplication-difference-integer-fractions
open import elementary-number-theory.difference-integers
open import elementary-number-theory.difference-rational-numbers
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

open import foundation.action-on-identifications-functions
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
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.groups
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

  abstract
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

  reflects-le-right-rational-fraction-ℤ :
    le-ℚ x (rational-fraction-ℤ p) → le-fraction-ℤ (fraction-ℚ x) p
  reflects-le-right-rational-fraction-ℤ H =
    concatenate-le-sim-fraction-ℤ
      ( fraction-ℚ x)
      ( reduce-fraction-ℤ p)
      ( p)
      ( H)
      ( symmetric-sim-fraction-ℤ
        ( p)
        ( reduce-fraction-ℤ p)
        ( sim-reduced-fraction-ℤ p))

  iff-le-right-rational-fraction-ℤ :
    le-fraction-ℤ (fraction-ℚ x) p ↔ le-ℚ x (rational-fraction-ℤ p)
  pr1 iff-le-right-rational-fraction-ℤ = preserves-le-right-rational-fraction-ℤ
  pr2 iff-le-right-rational-fraction-ℤ = reflects-le-right-rational-fraction-ℤ

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

  reflects-le-left-rational-fraction-ℤ :
    le-ℚ (rational-fraction-ℤ p) x → le-fraction-ℤ p (fraction-ℚ x)
  reflects-le-left-rational-fraction-ℤ =
    concatenate-sim-le-fraction-ℤ
      ( p)
      ( reduce-fraction-ℤ p)
      ( fraction-ℚ x)
      ( sim-reduced-fraction-ℤ p)

  iff-le-left-rational-fraction-ℤ :
    le-fraction-ℤ p (fraction-ℚ x) ↔ le-ℚ (rational-fraction-ℤ p) x
  pr1 iff-le-left-rational-fraction-ℤ = preserves-le-left-rational-fraction-ℤ
  pr2 iff-le-left-rational-fraction-ℤ = reflects-le-left-rational-fraction-ℤ
```

### `x < y` if and only if `0 < y - x`

```agda
module _
  (x y : ℚ)
  where

  abstract
    iff-translate-diff-le-zero-ℚ : le-ℚ zero-ℚ (y -ℚ x) ↔ le-ℚ x y
    iff-translate-diff-le-zero-ℚ =
      logical-equivalence-reasoning
        le-ℚ zero-ℚ (y -ℚ x)
        ↔ le-fraction-ℤ
          ( zero-fraction-ℤ)
          ( add-fraction-ℤ (fraction-ℚ y) (neg-fraction-ℤ (fraction-ℚ x)))
          by
            inv-iff
              ( iff-le-right-rational-fraction-ℤ
                ( zero-ℚ)
                ( add-fraction-ℤ
                  ( fraction-ℚ y)
                  ( neg-fraction-ℤ (fraction-ℚ x))))
        ↔ le-ℚ x y
          by
            inv-tr
              ( _↔ le-ℚ x y)
              ( eq-translate-diff-le-zero-fraction-ℤ
                ( fraction-ℚ x)
                ( fraction-ℚ y))
              ( id-iff)
```

### Strict inequality on the rational numbers is invariant by translation

```agda
module _
  (z x y : ℚ)
  where

  abstract
    iff-translate-left-le-ℚ : le-ℚ (z +ℚ x) (z +ℚ y) ↔ le-ℚ x y
    iff-translate-left-le-ℚ =
      logical-equivalence-reasoning
        le-ℚ (z +ℚ x) (z +ℚ y)
        ↔ le-ℚ zero-ℚ ((z +ℚ y) -ℚ (z +ℚ x))
          by (inv-iff (iff-translate-diff-le-zero-ℚ (z +ℚ x) (z +ℚ y)))
        ↔ le-ℚ zero-ℚ (y -ℚ x)
          by
            ( inv-tr
              ( _↔ le-ℚ zero-ℚ (y -ℚ x))
              ( ap (le-ℚ zero-ℚ) (left-translation-diff-ℚ y x z))
              ( id-iff))
        ↔ le-ℚ x y
          by (iff-translate-diff-le-zero-ℚ x y)

    iff-translate-right-le-ℚ : le-ℚ (x +ℚ z) (y +ℚ z) ↔ le-ℚ x y
    iff-translate-right-le-ℚ =
      logical-equivalence-reasoning
        le-ℚ (x +ℚ z) (y +ℚ z)
        ↔ le-ℚ zero-ℚ ((y +ℚ z) -ℚ (x +ℚ z))
          by (inv-iff (iff-translate-diff-le-zero-ℚ (x +ℚ z) (y +ℚ z)))
        ↔ le-ℚ zero-ℚ (y -ℚ x)
          by
            ( inv-tr
              ( _↔ le-ℚ zero-ℚ (y -ℚ x))
              ( ap (le-ℚ zero-ℚ) (right-translation-diff-ℚ y x z))
              ( id-iff))
        ↔ le-ℚ x y by (iff-translate-diff-le-zero-ℚ x y)

  preserves-le-left-add-ℚ : le-ℚ x y → le-ℚ (x +ℚ z) (y +ℚ z)
  preserves-le-left-add-ℚ = backward-implication iff-translate-right-le-ℚ

  preserves-le-right-add-ℚ : le-ℚ x y → le-ℚ (z +ℚ x) (z +ℚ y)
  preserves-le-right-add-ℚ = backward-implication iff-translate-left-le-ℚ

  reflects-le-left-add-ℚ : le-ℚ (x +ℚ z) (y +ℚ z) → le-ℚ x y
  reflects-le-left-add-ℚ = forward-implication iff-translate-right-le-ℚ

  reflects-le-right-add-ℚ : le-ℚ (z +ℚ x) (z +ℚ y) → le-ℚ x y
  reflects-le-right-add-ℚ = forward-implication iff-translate-left-le-ℚ
```

### Addition on the rational numbers preserves strict inequality

```agda
preserves-le-add-ℚ :
  {a b c d : ℚ} → le-ℚ a b → le-ℚ c d → le-ℚ (a +ℚ c) (b +ℚ d)
preserves-le-add-ℚ {a} {b} {c} {d} H K =
  transitive-le-ℚ
    ( a +ℚ c)
    ( b +ℚ c)
    ( b +ℚ d)
    ( preserves-le-right-add-ℚ b c d K)
    ( preserves-le-left-add-ℚ c a b H)
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

not-leq-le-ℚ : (x y : ℚ) → le-ℚ x y → ¬ leq-ℚ y x
not-leq-le-ℚ x y H K =
  is-not-positive-is-nonpositive-ℤ
    ( tr
      ( is-nonpositive-ℤ)
      ( skew-commutative-cross-mul-diff-fraction-ℤ
        ( fraction-ℚ y)
        ( fraction-ℚ x))
      ( is-nonpositive-neg-is-nonnegative-ℤ K))
    ( H)
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

### Negation reverses the ordering of strict inequality on the rational numbers

```agda
neg-le-ℚ : (x y : ℚ) → le-ℚ x y → le-ℚ (neg-ℚ y) (neg-ℚ x)
neg-le-ℚ x y = neg-le-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)
```

### Transposing additions on strict inequalities of rational numbers

```agda
le-transpose-right-diff-ℚ : (x y z : ℚ) → le-ℚ x (y -ℚ z) → le-ℚ (x +ℚ z) y
le-transpose-right-diff-ℚ x y z x<y-z =
  tr
    ( le-ℚ (x +ℚ z))
    ( is-section-right-div-Group group-add-ℚ z y)
    ( preserves-le-left-add-ℚ z x (y -ℚ z) x<y-z)

le-transpose-right-add-ℚ : (x y z : ℚ) → le-ℚ x (y +ℚ z) → le-ℚ (x -ℚ z) y
le-transpose-right-add-ℚ x y z x<y+z =
  tr
    ( le-ℚ (x -ℚ z))
    ( is-retraction-right-div-Group group-add-ℚ z y)
    ( preserves-le-left-add-ℚ (neg-ℚ z) x (y +ℚ z) x<y+z)

le-transpose-left-diff-ℚ : (x y z : ℚ) → le-ℚ (x -ℚ y) z → le-ℚ x (z +ℚ y)
le-transpose-left-diff-ℚ x y z x-y<z =
  tr
    ( λ w → le-ℚ w (z +ℚ y))
    ( is-section-right-div-Group group-add-ℚ y x)
    ( preserves-le-left-add-ℚ y (x -ℚ y) z x-y<z)

le-transpose-left-add-ℚ : (x y z : ℚ) → le-ℚ (x +ℚ y) z → le-ℚ x (z -ℚ y)
le-transpose-left-add-ℚ x y z x+y<z =
  tr
    ( λ w → le-ℚ w (z -ℚ y))
    ( is-retraction-right-div-Group group-add-ℚ y x)
    ( preserves-le-left-add-ℚ (neg-ℚ y) (x +ℚ y) z x+y<z)

le-iff-transpose-left-add-ℚ : (x y z : ℚ) → le-ℚ (x +ℚ y) z ↔ le-ℚ x (z -ℚ y)
pr1 (le-iff-transpose-left-add-ℚ x y z) = le-transpose-left-add-ℚ x y z
pr2 (le-iff-transpose-left-add-ℚ x y z) = le-transpose-right-diff-ℚ x z y

le-iff-transpose-left-diff-ℚ : (x y z : ℚ) → le-ℚ (x -ℚ y) z ↔ le-ℚ x (z +ℚ y)
pr1 (le-iff-transpose-left-diff-ℚ x y z) = le-transpose-left-diff-ℚ x y z
pr2 (le-iff-transpose-left-diff-ℚ x y z) = le-transpose-right-add-ℚ x z y
```
