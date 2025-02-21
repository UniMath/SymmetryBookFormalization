# Inequality on the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.inequality-rational-numbers where
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
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.nonpositive-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.order-preserving-maps-posets
open import order-theory.posets
open import order-theory.preorders
open import order-theory.transposition-inequalities-along-order-preserving-retractions-posets
open import order-theory.transposition-inequalities-along-sections-of-order-preserving-maps-posets
```

</details>

## Idea

The
{{#concept "standard ordering" Disambiguation="rational numbers" Agda=leq-ℚ}} on
the [rational numbers](elementary-number-theory.rational-numbers.md) is
inherited from the
[standard ordering](elementary-number-theory.inequality-integer-fractions.md) on
[integer fractions](elementary-number-theory.integer-fractions.md): the rational
number `m / n` is _less than or equal to_ `m' / n'` if the
[integer product](elementary-number-theory.multiplication-integers.md) `m * n'`
is [less than or equal](elementary-number-theory.inequality-integers.md) to
`m' * n`.

## Definition

### Inequality on the rational numbers

```agda
leq-ℚ-Prop : ℚ → ℚ → Prop lzero
leq-ℚ-Prop (x , px) (y , py) = leq-fraction-ℤ-Prop x y

leq-ℚ : ℚ → ℚ → UU lzero
leq-ℚ x y = type-Prop (leq-ℚ-Prop x y)

is-prop-leq-ℚ : (x y : ℚ) → is-prop (leq-ℚ x y)
is-prop-leq-ℚ x y = is-prop-type-Prop (leq-ℚ-Prop x y)

infix 30 _≤-ℚ_
_≤-ℚ_ = leq-ℚ
```

## Properties

### Inequality on the rational numbers is decidable

```agda
is-decidable-leq-ℚ : (x y : ℚ) → (leq-ℚ x y) + ¬ (leq-ℚ x y)
is-decidable-leq-ℚ x y =
  is-decidable-leq-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)

leq-ℚ-Decidable-Prop : (x y : ℚ) → Decidable-Prop lzero
leq-ℚ-Decidable-Prop x y =
  ( leq-ℚ x y ,
    is-prop-leq-ℚ x y ,
    is-decidable-leq-ℚ x y)
```

### Inequality on the rational numbers is reflexive

```agda
refl-leq-ℚ : (x : ℚ) → leq-ℚ x x
refl-leq-ℚ x =
  refl-leq-ℤ (numerator-ℚ x *ℤ denominator-ℚ x)
```

### Inequality on the rational numbers is antisymmetric

```agda
abstract
  antisymmetric-leq-ℚ : (x y : ℚ) → leq-ℚ x y → leq-ℚ y x → x ＝ y
  antisymmetric-leq-ℚ x y H H' =
    ( inv (is-retraction-rational-fraction-ℚ x)) ∙
    ( eq-ℚ-sim-fraction-ℤ
      ( fraction-ℚ x)
      ( fraction-ℚ y)
      ( is-sim-antisymmetric-leq-fraction-ℤ
        ( fraction-ℚ x)
        ( fraction-ℚ y)
        ( H)
        ( H'))) ∙
    ( is-retraction-rational-fraction-ℚ y)
```

### Inequality on the rational numbers is linear

```agda
abstract
  linear-leq-ℚ : (x y : ℚ) → (leq-ℚ x y) + (leq-ℚ y x)
  linear-leq-ℚ x y =
    map-coproduct
      ( id)
      ( is-nonnegative-eq-ℤ
        (distributive-neg-diff-ℤ
          ( numerator-ℚ y *ℤ denominator-ℚ x)
          ( numerator-ℚ x *ℤ denominator-ℚ y)))
      ( decide-is-nonnegative-is-nonnegative-neg-ℤ
        { cross-mul-diff-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)})
```

### Inequality on the rational numbers is transitive

```agda
module _
  (x y z : ℚ)
  where

  abstract
    transitive-leq-ℚ : leq-ℚ y z → leq-ℚ x y → leq-ℚ x z
    transitive-leq-ℚ =
      transitive-leq-fraction-ℤ
        ( fraction-ℚ x)
        ( fraction-ℚ y)
        ( fraction-ℚ z)
```

### The partially ordered set of rational numbers ordered by inequality

```agda
ℚ-Preorder : Preorder lzero lzero
ℚ-Preorder =
  (ℚ , leq-ℚ-Prop , refl-leq-ℚ , transitive-leq-ℚ)

ℚ-Poset : Poset lzero lzero
ℚ-Poset = (ℚ-Preorder , antisymmetric-leq-ℚ)
```

### The canonical map from integer fractions to the rational numbers preserves inequality

```agda
module _
  (p q : fraction-ℤ)
  where

  abstract
    preserves-leq-rational-fraction-ℤ :
      leq-fraction-ℤ p q → leq-ℚ (rational-fraction-ℤ p) (rational-fraction-ℤ q)
    preserves-leq-rational-fraction-ℤ =
      preserves-leq-sim-fraction-ℤ
        ( p)
        ( q)
        ( reduce-fraction-ℤ p)
        ( reduce-fraction-ℤ q)
        ( sim-reduced-fraction-ℤ p)
        ( sim-reduced-fraction-ℤ q)

module _
  (x : ℚ) (p : fraction-ℤ)
  where

  abstract
    preserves-leq-right-rational-fraction-ℤ :
      leq-fraction-ℤ (fraction-ℚ x) p → leq-ℚ x (rational-fraction-ℤ p)
    preserves-leq-right-rational-fraction-ℤ H =
      concatenate-leq-sim-fraction-ℤ
        ( fraction-ℚ x)
        ( p)
        ( fraction-ℚ ( rational-fraction-ℤ p))
        ( H)
        ( sim-reduced-fraction-ℤ p)

    reflects-leq-right-rational-fraction-ℤ :
      leq-ℚ x (rational-fraction-ℤ p) → leq-fraction-ℤ (fraction-ℚ x) p
    reflects-leq-right-rational-fraction-ℤ H =
      concatenate-leq-sim-fraction-ℤ
        ( fraction-ℚ x)
        ( reduce-fraction-ℤ p)
        ( p)
        ( H)
        ( symmetric-sim-fraction-ℤ
          ( p)
          ( reduce-fraction-ℤ p)
          ( sim-reduced-fraction-ℤ p))

  iff-leq-right-rational-fraction-ℤ :
    leq-fraction-ℤ (fraction-ℚ x) p ↔ leq-ℚ x (rational-fraction-ℤ p)
  pr1 iff-leq-right-rational-fraction-ℤ =
    preserves-leq-right-rational-fraction-ℤ
  pr2 iff-leq-right-rational-fraction-ℤ = reflects-leq-right-rational-fraction-ℤ

  abstract
    preserves-leq-left-rational-fraction-ℤ :
      leq-fraction-ℤ p (fraction-ℚ x) → leq-ℚ (rational-fraction-ℤ p) x
    preserves-leq-left-rational-fraction-ℤ =
      concatenate-sim-leq-fraction-ℤ
        ( fraction-ℚ ( rational-fraction-ℤ p))
        ( p)
        ( fraction-ℚ x)
        ( symmetric-sim-fraction-ℤ
          ( p)
          ( fraction-ℚ ( rational-fraction-ℤ p))
          ( sim-reduced-fraction-ℤ p))

    reflects-leq-left-rational-fraction-ℤ :
      leq-ℚ (rational-fraction-ℤ p) x → leq-fraction-ℤ p (fraction-ℚ x)
    reflects-leq-left-rational-fraction-ℤ =
      concatenate-sim-leq-fraction-ℤ
        ( p)
        ( reduce-fraction-ℤ p)
        ( fraction-ℚ x)
        ( sim-reduced-fraction-ℤ p)

  iff-leq-left-rational-fraction-ℤ :
    leq-fraction-ℤ p (fraction-ℚ x) ↔ leq-ℚ (rational-fraction-ℤ p) x
  pr1 iff-leq-left-rational-fraction-ℤ = preserves-leq-left-rational-fraction-ℤ
  pr2 iff-leq-left-rational-fraction-ℤ = reflects-leq-left-rational-fraction-ℤ
```

### `x ≤ y` if and only if `0 ≤ y - x`

```agda
module _
  (x y : ℚ)
  where

  abstract
    iff-translate-diff-leq-zero-ℚ : leq-ℚ zero-ℚ (y -ℚ x) ↔ leq-ℚ x y
    iff-translate-diff-leq-zero-ℚ =
      logical-equivalence-reasoning
        leq-ℚ zero-ℚ (y -ℚ x)
        ↔ leq-fraction-ℤ
          ( zero-fraction-ℤ)
          ( add-fraction-ℤ (fraction-ℚ y) (neg-fraction-ℤ (fraction-ℚ x)))
          by
            inv-iff
              ( iff-leq-right-rational-fraction-ℤ
                ( zero-ℚ)
                ( add-fraction-ℤ
                  ( fraction-ℚ y)
                  ( neg-fraction-ℤ (fraction-ℚ x))))
        ↔ leq-ℚ x y
          by
            inv-tr
              ( _↔ leq-ℚ x y)
              ( eq-translate-diff-leq-zero-fraction-ℤ
                ( fraction-ℚ x)
                ( fraction-ℚ y))
              ( id-iff)
```

### Inequality on the rational numbers is invariant by translation

```agda
module _
  (z x y : ℚ)
  where

  abstract
    iff-translate-left-leq-ℚ : leq-ℚ (z +ℚ x) (z +ℚ y) ↔ leq-ℚ x y
    iff-translate-left-leq-ℚ =
      logical-equivalence-reasoning
        leq-ℚ (z +ℚ x) (z +ℚ y)
        ↔ leq-ℚ zero-ℚ ((z +ℚ y) -ℚ (z +ℚ x))
          by (inv-iff (iff-translate-diff-leq-zero-ℚ (z +ℚ x) (z +ℚ y)))
        ↔ leq-ℚ zero-ℚ (y -ℚ x)
          by
            ( inv-tr
              ( _↔ leq-ℚ zero-ℚ (y -ℚ x))
              ( ap (leq-ℚ zero-ℚ) (left-translation-diff-ℚ y x z))
              ( id-iff))
        ↔ leq-ℚ x y
          by (iff-translate-diff-leq-zero-ℚ x y)

    iff-translate-right-leq-ℚ : leq-ℚ (x +ℚ z) (y +ℚ z) ↔ leq-ℚ x y
    iff-translate-right-leq-ℚ =
      logical-equivalence-reasoning
        leq-ℚ (x +ℚ z) (y +ℚ z)
        ↔ leq-ℚ zero-ℚ ((y +ℚ z) -ℚ (x +ℚ z))
          by (inv-iff (iff-translate-diff-leq-zero-ℚ (x +ℚ z) (y +ℚ z)))
        ↔ leq-ℚ zero-ℚ (y -ℚ x)
          by
            ( inv-tr
              ( _↔ leq-ℚ zero-ℚ (y -ℚ x))
              ( ap (leq-ℚ zero-ℚ) (right-translation-diff-ℚ y x z))
              ( id-iff))
        ↔ leq-ℚ x y by (iff-translate-diff-leq-zero-ℚ x y)

  preserves-leq-left-add-ℚ : leq-ℚ x y → leq-ℚ (x +ℚ z) (y +ℚ z)
  preserves-leq-left-add-ℚ = backward-implication iff-translate-right-leq-ℚ

  preserves-leq-right-add-ℚ : leq-ℚ x y → leq-ℚ (z +ℚ x) (z +ℚ y)
  preserves-leq-right-add-ℚ = backward-implication iff-translate-left-leq-ℚ

  reflects-leq-left-add-ℚ : leq-ℚ (x +ℚ z) (y +ℚ z) → leq-ℚ x y
  reflects-leq-left-add-ℚ = forward-implication iff-translate-right-leq-ℚ

  reflects-leq-right-add-ℚ : leq-ℚ (z +ℚ x) (z +ℚ y) → leq-ℚ x y
  reflects-leq-right-add-ℚ = forward-implication iff-translate-left-leq-ℚ

right-add-hom-leq-ℚ : (z : ℚ) → hom-Poset ℚ-Poset ℚ-Poset
pr1 (right-add-hom-leq-ℚ z) x = x +ℚ z
pr2 (right-add-hom-leq-ℚ z) = preserves-leq-left-add-ℚ z

left-add-hom-leq-ℚ : (z : ℚ) → hom-Poset ℚ-Poset ℚ-Poset
pr1 (left-add-hom-leq-ℚ z) x = z +ℚ x
pr2 (left-add-hom-leq-ℚ z) = preserves-leq-right-add-ℚ z
```

### Addition on the rational numbers preserves inequality

```agda
preserves-leq-add-ℚ :
  {a b c d : ℚ} → leq-ℚ a b → leq-ℚ c d → leq-ℚ (a +ℚ c) (b +ℚ d)
preserves-leq-add-ℚ {a} {b} {c} {d} H K =
  transitive-leq-ℚ
    ( a +ℚ c)
    ( b +ℚ c)
    ( b +ℚ d)
    ( preserves-leq-right-add-ℚ b c d K)
    ( preserves-leq-left-add-ℚ c a b H)
```

### Transposing additions on inequalities of rational numbers

```agda
leq-transpose-right-diff-ℚ : (x y z : ℚ) → x ≤-ℚ (y -ℚ z) → x +ℚ z ≤-ℚ y
leq-transpose-right-diff-ℚ x y z x≤y-z =
  leq-transpose-is-section-hom-Poset
    ( ℚ-Poset)
    ( ℚ-Poset)
    ( right-add-hom-leq-ℚ z)
    ( _-ℚ z)
    ( is-section-diff-ℚ z)
    ( x)
    ( y)
    ( x≤y-z)

leq-transpose-right-add-ℚ : (x y z : ℚ) → x ≤-ℚ y +ℚ z → x -ℚ z ≤-ℚ y
leq-transpose-right-add-ℚ x y z x≤y+z =
  leq-transpose-is-section-hom-Poset
    ( ℚ-Poset)
    ( ℚ-Poset)
    ( right-add-hom-leq-ℚ (neg-ℚ z))
    ( _+ℚ z)
    ( is-retraction-diff-ℚ z)
    ( x)
    ( y)
    ( x≤y+z)

leq-transpose-left-add-ℚ : (x y z : ℚ) → x +ℚ y ≤-ℚ z → x ≤-ℚ z -ℚ y
leq-transpose-left-add-ℚ x y z x+y≤z =
  leq-transpose-is-retraction-hom-Poset
    ( ℚ-Poset)
    ( ℚ-Poset)
    ( _+ℚ y)
    ( right-add-hom-leq-ℚ (neg-ℚ y))
    ( is-retraction-diff-ℚ y)
    ( x)
    ( z)
    ( x+y≤z)

leq-transpose-left-diff-ℚ : (x y z : ℚ) → x -ℚ y ≤-ℚ z → x ≤-ℚ z +ℚ y
leq-transpose-left-diff-ℚ x y z x-y≤z =
  leq-transpose-is-retraction-hom-Poset
    ( ℚ-Poset)
    ( ℚ-Poset)
    ( _-ℚ y)
    ( right-add-hom-leq-ℚ y)
    ( is-section-diff-ℚ y)
    ( x)
    ( z)
    ( x-y≤z)

leq-iff-transpose-left-add-ℚ : (x y z : ℚ) → x +ℚ y ≤-ℚ z ↔ x ≤-ℚ z -ℚ y
pr1 (leq-iff-transpose-left-add-ℚ x y z) = leq-transpose-left-add-ℚ x y z
pr2 (leq-iff-transpose-left-add-ℚ x y z) = leq-transpose-right-diff-ℚ x z y

leq-iff-transpose-left-diff-ℚ : (x y z : ℚ) → x -ℚ y ≤-ℚ z ↔ x ≤-ℚ z +ℚ y
pr1 (leq-iff-transpose-left-diff-ℚ x y z) = leq-transpose-left-diff-ℚ x y z
pr2 (leq-iff-transpose-left-diff-ℚ x y z) = leq-transpose-right-add-ℚ x z y
```

## See also

- The decidable total order on the rational numbers is defined in
  [`decidable-total-order-rational-numbers`](elementary-number-theory.decidable-total-order-rational-numbers.md)
- The strict ordering on the rational numbers is defined in
  [`strict-inequality-rational-numbers`](elementary-number-theory.strict-inequality-rational-numbers.md)
