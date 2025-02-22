# Positive rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.cross-multiplication-difference-integer-fractions
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-inverses-positive-integer-fractions
open import elementary-number-theory.multiplicative-monoid-of-rational-numbers
open import elementary-number-theory.negative-integers
open import elementary-number-theory.nonzero-rational-numbers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integer-fractions
open import elementary-number-theory.positive-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.invertible-elements-monoids
open import group-theory.monoids
open import group-theory.semigroups
open import group-theory.submonoids
open import group-theory.submonoids-commutative-monoids
open import group-theory.subsemigroups
```

</details>

## Idea

A [rational number](elementary-number-theory.rational-numbers.md) `x` is said to
be {{#concept "positive" Disambiguation="rational number" Agda=is-positive-ℚ}}
if its underlying fraction is
[positive](elementary-number-theory.positive-integer-fractions.md).

Positive rational numbers are a [subsemigroup](group-theory.subsemigroups.md) of
the
[additive monoid of rational numbers](elementary-number-theory.additive-group-of-rational-numbers.md)
and a [submonoid](group-theory.submonoids.md) of the
[multiplicative monoid of rational numbers](elementary-number-theory.multiplicative-monoid-of-rational-numbers.md).

## Definitions

### The property of being a positive rational number

```agda
module _
  (x : ℚ)
  where

  is-positive-ℚ : UU lzero
  is-positive-ℚ = is-positive-fraction-ℤ (fraction-ℚ x)

  is-prop-is-positive-ℚ : is-prop is-positive-ℚ
  is-prop-is-positive-ℚ = is-prop-is-positive-fraction-ℤ (fraction-ℚ x)

  is-positive-prop-ℚ : Prop lzero
  pr1 is-positive-prop-ℚ = is-positive-ℚ
  pr2 is-positive-prop-ℚ = is-prop-is-positive-ℚ
```

### The type of positive rational numbers

```agda
positive-ℚ : UU lzero
positive-ℚ = type-subtype is-positive-prop-ℚ

ℚ⁺ : UU lzero
ℚ⁺ = positive-ℚ

module _
  (x : positive-ℚ)
  where

  rational-ℚ⁺ : ℚ
  rational-ℚ⁺ = pr1 x

  fraction-ℚ⁺ : fraction-ℤ
  fraction-ℚ⁺ = fraction-ℚ rational-ℚ⁺

  numerator-ℚ⁺ : ℤ
  numerator-ℚ⁺ = numerator-ℚ rational-ℚ⁺

  denominator-ℚ⁺ : ℤ
  denominator-ℚ⁺ = denominator-ℚ rational-ℚ⁺

  is-positive-rational-ℚ⁺ : is-positive-ℚ rational-ℚ⁺
  is-positive-rational-ℚ⁺ = pr2 x

  is-positive-fraction-ℚ⁺ : is-positive-fraction-ℤ fraction-ℚ⁺
  is-positive-fraction-ℚ⁺ = is-positive-rational-ℚ⁺

  is-positive-numerator-ℚ⁺ : is-positive-ℤ numerator-ℚ⁺
  is-positive-numerator-ℚ⁺ = is-positive-rational-ℚ⁺

  is-positive-denominator-ℚ⁺ : is-positive-ℤ denominator-ℚ⁺
  is-positive-denominator-ℚ⁺ = is-positive-denominator-ℚ rational-ℚ⁺

abstract
  eq-ℚ⁺ : {x y : ℚ⁺} → rational-ℚ⁺ x ＝ rational-ℚ⁺ y → x ＝ y
  eq-ℚ⁺ {x} {y} = eq-type-subtype is-positive-prop-ℚ
```

## Properties

### The positive rational numbers form a set

```agda
is-set-ℚ⁺ : is-set ℚ⁺
is-set-ℚ⁺ = is-set-type-subtype is-positive-prop-ℚ is-set-ℚ
```

### The rational image of a positive integer is positive

```agda
abstract
  is-positive-rational-ℤ :
    (x : ℤ) → is-positive-ℤ x → is-positive-ℚ (rational-ℤ x)
  is-positive-rational-ℤ x P = P

one-ℚ⁺ : ℚ⁺
one-ℚ⁺ = (one-ℚ , is-positive-int-positive-ℤ one-positive-ℤ)
```

### The rational image of a positive integer fraction is positive

```agda
abstract
  is-positive-rational-fraction-ℤ :
    {x : fraction-ℤ} (P : is-positive-fraction-ℤ x) →
    is-positive-ℚ (rational-fraction-ℤ x)
  is-positive-rational-fraction-ℤ = is-positive-reduce-fraction-ℤ
```

### A rational number `x` is positive if and only if `0 < x`

```agda
module _
  (x : ℚ)
  where

  abstract
    le-zero-is-positive-ℚ : is-positive-ℚ x → le-ℚ zero-ℚ x
    le-zero-is-positive-ℚ =
      is-positive-eq-ℤ (inv (cross-mul-diff-zero-fraction-ℤ (fraction-ℚ x)))

    is-positive-le-zero-ℚ : le-ℚ zero-ℚ x → is-positive-ℚ x
    is-positive-le-zero-ℚ =
      is-positive-eq-ℤ (cross-mul-diff-zero-fraction-ℤ (fraction-ℚ x))
```

### The difference of a rational number with a lesser rational number is positive

```agda
module _
  (x y : ℚ) (H : le-ℚ x y)
  where

  abstract
    is-positive-diff-le-ℚ : is-positive-ℚ (y -ℚ x)
    is-positive-diff-le-ℚ =
      is-positive-le-zero-ℚ
        ( y -ℚ x)
        ( backward-implication
          ( iff-translate-diff-le-zero-ℚ x y)
          ( H))

  positive-diff-le-ℚ : ℚ⁺
  positive-diff-le-ℚ = y -ℚ x , is-positive-diff-le-ℚ

  left-law-positive-diff-le-ℚ : (rational-ℚ⁺ positive-diff-le-ℚ) +ℚ x ＝ y
  left-law-positive-diff-le-ℚ =
    ( associative-add-ℚ y (neg-ℚ x) x) ∙
    ( inv-tr
      ( λ u → y +ℚ u ＝ y)
      ( left-inverse-law-add-ℚ x)
      ( right-unit-law-add-ℚ y))

  right-law-positive-diff-le-ℚ : x +ℚ (rational-ℚ⁺ positive-diff-le-ℚ) ＝ y
  right-law-positive-diff-le-ℚ =
    commutative-add-ℚ x (y -ℚ x) ∙ left-law-positive-diff-le-ℚ
```

### A nonzero rational number or its negative is positive

```agda
decide-is-negative-is-positive-is-nonzero-ℚ :
  {x : ℚ} → is-nonzero-ℚ x → is-positive-ℚ (neg-ℚ x) + is-positive-ℚ x
decide-is-negative-is-positive-is-nonzero-ℚ {x} H =
  rec-coproduct
    ( inl ∘ is-positive-neg-is-negative-ℤ)
    ( inr)
    ( decide-sign-nonzero-ℤ
      { numerator-ℚ x}
      (is-nonzero-numerator-is-nonzero-ℚ x H))
```

### A rational and its negative are not both positive

```agda
abstract
  not-is-negative-is-positive-ℚ :
    (x : ℚ) → ¬ (is-positive-ℚ (neg-ℚ x) × is-positive-ℚ x)
  not-is-negative-is-positive-ℚ x (N , P) =
    is-not-negative-and-positive-ℤ
      ( numerator-ℚ x)
      ( ( is-negative-eq-ℤ
          (neg-neg-ℤ (numerator-ℚ x))
          (is-negative-neg-is-positive-ℤ {numerator-ℚ (neg-ℚ x)} N)) ,
        ( P))
```

### Positive rational numbers are nonzero

```agda
abstract
  is-nonzero-is-positive-ℚ : {x : ℚ} → is-positive-ℚ x → is-nonzero-ℚ x
  is-nonzero-is-positive-ℚ {x} H =
    is-nonzero-is-nonzero-numerator-ℚ x
      ( is-nonzero-is-positive-ℤ
        { numerator-ℚ x}
        ( H))

nonzero-ℚ⁺ : positive-ℚ → nonzero-ℚ
nonzero-ℚ⁺ (x , P) = (x , is-nonzero-is-positive-ℚ P)
```

### The sum of two positive rational numbers is positive

```agda
abstract
  is-positive-add-ℚ :
    {x y : ℚ} → is-positive-ℚ x → is-positive-ℚ y → is-positive-ℚ (x +ℚ y)
  is-positive-add-ℚ {x} {y} P Q =
    is-positive-rational-fraction-ℤ
      ( is-positive-add-fraction-ℤ
        { fraction-ℚ x}
        { fraction-ℚ y}
        ( P)
        ( Q))
```

### The positive rational numbers are an additive subsemigroup of the rational numbers

```agda
subsemigroup-add-ℚ⁺ : Subsemigroup lzero semigroup-add-ℚ
pr1 subsemigroup-add-ℚ⁺ = is-positive-prop-ℚ
pr2 subsemigroup-add-ℚ⁺ {x} {y} = is-positive-add-ℚ {x} {y}

semigroup-add-ℚ⁺ : Semigroup lzero
semigroup-add-ℚ⁺ =
  semigroup-Subsemigroup semigroup-add-ℚ subsemigroup-add-ℚ⁺
```

### The positive sum of two positive rational numbers

```agda
add-ℚ⁺ : ℚ⁺ → ℚ⁺ → ℚ⁺
add-ℚ⁺ = mul-Subsemigroup semigroup-add-ℚ subsemigroup-add-ℚ⁺

infixl 35 _+ℚ⁺_
_+ℚ⁺_ = add-ℚ⁺
```

### The positive sum of positive rational numbers is associative

```agda
associative-add-ℚ⁺ : (x y z : ℚ⁺) → ((x +ℚ⁺ y) +ℚ⁺ z) ＝ (x +ℚ⁺ (y +ℚ⁺ z))
associative-add-ℚ⁺ =
  associative-mul-Subsemigroup semigroup-add-ℚ subsemigroup-add-ℚ⁺
```

### The positive sum of positive rational numbers is commutative

```agda
commutative-add-ℚ⁺ : (x y : ℚ⁺) → (x +ℚ⁺ y) ＝ (y +ℚ⁺ x)
commutative-add-ℚ⁺ x y =
  eq-ℚ⁺ (commutative-add-ℚ (rational-ℚ⁺ x) (rational-ℚ⁺ y))
```

### The additive interchange law on positive rational numbers

```agda
interchange-law-add-add-ℚ⁺ :
  (x y u v : ℚ⁺) → (x +ℚ⁺ y) +ℚ⁺ (u +ℚ⁺ v) ＝ (x +ℚ⁺ u) +ℚ⁺ (y +ℚ⁺ v)
interchange-law-add-add-ℚ⁺ x y u v =
  eq-ℚ⁺
    ( interchange-law-add-add-ℚ
      ( rational-ℚ⁺ x)
      ( rational-ℚ⁺ y)
      ( rational-ℚ⁺ u)
      ( rational-ℚ⁺ v))
```

### The product of two positive rational numbers is positive

```agda
abstract
  is-positive-mul-ℚ :
    {x y : ℚ} → is-positive-ℚ x → is-positive-ℚ y → is-positive-ℚ (x *ℚ y)
  is-positive-mul-ℚ {x} {y} P Q =
    is-positive-rational-fraction-ℤ
      ( is-positive-mul-fraction-ℤ
        { fraction-ℚ x}
        { fraction-ℚ y}
        ( P)
        ( Q))
```

### The positive rational numbers are a multiplicative submonoid of the rational numbers

```agda
is-submonoid-mul-ℚ⁺ :
  is-submonoid-subset-Monoid monoid-mul-ℚ is-positive-prop-ℚ
pr1 is-submonoid-mul-ℚ⁺ = is-positive-rational-ℚ⁺ one-ℚ⁺
pr2 is-submonoid-mul-ℚ⁺ x y = is-positive-mul-ℚ {x} {y}

submonoid-mul-ℚ⁺ : Submonoid lzero monoid-mul-ℚ
pr1 submonoid-mul-ℚ⁺ = is-positive-prop-ℚ
pr2 submonoid-mul-ℚ⁺ = is-submonoid-mul-ℚ⁺

monoid-mul-ℚ⁺ : Monoid lzero
monoid-mul-ℚ⁺ = monoid-Submonoid monoid-mul-ℚ submonoid-mul-ℚ⁺

commutative-monoid-mul-ℚ⁺ : Commutative-Monoid lzero
commutative-monoid-mul-ℚ⁺ =
  commutative-monoid-Commutative-Submonoid
    commutative-monoid-mul-ℚ
    submonoid-mul-ℚ⁺
```

### The positive product of two positive rational numbers

```agda
mul-ℚ⁺ : ℚ⁺ → ℚ⁺ → ℚ⁺
mul-ℚ⁺ = mul-Submonoid monoid-mul-ℚ submonoid-mul-ℚ⁺

infixl 40 _*ℚ⁺_
_*ℚ⁺_ = mul-ℚ⁺
```

### The positive product of positive rational numbers is associative

```agda
associative-mul-ℚ⁺ : (x y z : ℚ⁺) → ((x *ℚ⁺ y) *ℚ⁺ z) ＝ (x *ℚ⁺ (y *ℚ⁺ z))
associative-mul-ℚ⁺ =
  associative-mul-Submonoid monoid-mul-ℚ submonoid-mul-ℚ⁺
```

### The positive product of positive rational numbers is commutative

```agda
commutative-mul-ℚ⁺ : (x y : ℚ⁺) → (x *ℚ⁺ y) ＝ (y *ℚ⁺ x)
commutative-mul-ℚ⁺ =
  commutative-mul-Commutative-Submonoid
    commutative-monoid-mul-ℚ
    submonoid-mul-ℚ⁺
```

### Multiplicative unit laws for positive multiplication of positive rational numbers

```agda
left-unit-law-mul-ℚ⁺ : (x : ℚ⁺) → one-ℚ⁺ *ℚ⁺ x ＝ x
left-unit-law-mul-ℚ⁺ =
  left-unit-law-mul-Submonoid monoid-mul-ℚ submonoid-mul-ℚ⁺

right-unit-law-mul-ℚ⁺ : (x : ℚ⁺) → x *ℚ⁺ one-ℚ⁺ ＝ x
right-unit-law-mul-ℚ⁺ =
  right-unit-law-mul-Submonoid monoid-mul-ℚ submonoid-mul-ℚ⁺
```

### The positive rational numbers are invertible elements of the multiplicative monoid of rational numbers

```agda
module _
  (x : ℚ) (P : is-positive-ℚ x)
  where

  inv-is-positive-ℚ : ℚ
  pr1 inv-is-positive-ℚ = inv-is-positive-fraction-ℤ (fraction-ℚ x) P
  pr2 inv-is-positive-ℚ =
    is-reduced-inv-is-positive-fraction-ℤ
      ( fraction-ℚ x)
      ( P)
      ( is-reduced-fraction-ℚ x)

  abstract
    left-inverse-law-mul-is-positive-ℚ : inv-is-positive-ℚ *ℚ x ＝ one-ℚ
    left-inverse-law-mul-is-positive-ℚ =
      ( eq-ℚ-sim-fraction-ℤ
        ( mul-fraction-ℤ
          ( inv-is-positive-fraction-ℤ (fraction-ℚ x) P)
          ( fraction-ℚ x))
        ( one-fraction-ℤ)
        ( left-inverse-law-mul-is-positive-fraction-ℤ (fraction-ℚ x) P)) ∙
      ( is-retraction-rational-fraction-ℚ one-ℚ)

    right-inverse-law-mul-is-positive-ℚ : x *ℚ inv-is-positive-ℚ ＝ one-ℚ
    right-inverse-law-mul-is-positive-ℚ =
      (commutative-mul-ℚ x _) ∙ (left-inverse-law-mul-is-positive-ℚ)

  is-mul-invertible-is-positive-ℚ : is-invertible-element-Monoid monoid-mul-ℚ x
  pr1 is-mul-invertible-is-positive-ℚ = inv-is-positive-ℚ
  pr1 (pr2 is-mul-invertible-is-positive-ℚ) =
    right-inverse-law-mul-is-positive-ℚ
  pr2 (pr2 is-mul-invertible-is-positive-ℚ) =
    left-inverse-law-mul-is-positive-ℚ
```

### The strict inequality on positive rational numbers

```agda
le-prop-ℚ⁺ : ℚ⁺ → ℚ⁺ → Prop lzero
le-prop-ℚ⁺ x y = le-ℚ-Prop (rational-ℚ⁺ x) (rational-ℚ⁺ y)

le-ℚ⁺ : ℚ⁺ → ℚ⁺ → UU lzero
le-ℚ⁺ x y = type-Prop (le-prop-ℚ⁺ x y)

is-prop-le-ℚ⁺ : (x y : ℚ⁺) → is-prop (le-ℚ⁺ x y)
is-prop-le-ℚ⁺ x y = is-prop-type-Prop (le-prop-ℚ⁺ x y)
```

### The sum of two positive rational numbers is greater than each of them

```agda
module _
  (x y : ℚ⁺)
  where

  le-left-add-ℚ⁺ : le-ℚ⁺ x (x +ℚ⁺ y)
  le-left-add-ℚ⁺ =
    tr
      ( λ z → le-ℚ z ((rational-ℚ⁺ x) +ℚ (rational-ℚ⁺ y)))
      ( right-unit-law-add-ℚ (rational-ℚ⁺ x))
      ( preserves-le-right-add-ℚ
        ( rational-ℚ⁺ x)
        ( zero-ℚ)
        ( rational-ℚ⁺ y)
        ( le-zero-is-positive-ℚ
          ( rational-ℚ⁺ y)
          ( is-positive-rational-ℚ⁺ y)))

  le-right-add-ℚ⁺ : le-ℚ⁺ y (x +ℚ⁺ y)
  le-right-add-ℚ⁺ =
    tr
      ( λ z → le-ℚ z ((rational-ℚ⁺ x) +ℚ (rational-ℚ⁺ y)))
      ( left-unit-law-add-ℚ (rational-ℚ⁺ y))
      ( preserves-le-left-add-ℚ
        ( rational-ℚ⁺ y)
        ( zero-ℚ)
        ( rational-ℚ⁺ x)
        ( le-zero-is-positive-ℚ
          ( rational-ℚ⁺ x)
          ( is-positive-rational-ℚ⁺ x)))
```

### The positive difference of strictly inequal positive rational numbers

```agda
module _
  (x y : ℚ⁺) (H : le-ℚ⁺ x y)
  where

  le-diff-ℚ⁺ : ℚ⁺
  pr1 le-diff-ℚ⁺ = (rational-ℚ⁺ y) -ℚ (rational-ℚ⁺ x)
  pr2 le-diff-ℚ⁺ =
    is-positive-le-zero-ℚ
      ( (rational-ℚ⁺ y) -ℚ (rational-ℚ⁺ x))
      ( backward-implication
        ( iff-translate-diff-le-zero-ℚ
          ( rational-ℚ⁺ x)
          ( rational-ℚ⁺ y))
        ( ( H)))

  left-diff-law-add-ℚ⁺ : le-diff-ℚ⁺ +ℚ⁺ x ＝ y
  left-diff-law-add-ℚ⁺ =
    eq-ℚ⁺
      ( ( associative-add-ℚ
          ( rational-ℚ⁺ y)
          ( neg-ℚ (rational-ℚ⁺ x))
          ( rational-ℚ⁺ x)) ∙
        ( ( ap
            ( (rational-ℚ⁺ y) +ℚ_)
            ( left-inverse-law-add-ℚ (rational-ℚ⁺ x))) ∙
        ( right-unit-law-add-ℚ (rational-ℚ⁺ y))))

  right-diff-law-add-ℚ⁺ : x +ℚ⁺ le-diff-ℚ⁺ ＝ y
  right-diff-law-add-ℚ⁺ =
    ( eq-ℚ⁺
      ( commutative-add-ℚ
        ( rational-ℚ⁺ x)
        ( rational-ℚ⁺ le-diff-ℚ⁺))) ∙
    ( left-diff-law-add-ℚ⁺)
```

### The positive mediant between zero and a positive rational number

```agda
mediant-zero-ℚ⁺ : ℚ⁺ → ℚ⁺
mediant-zero-ℚ⁺ x =
  ( mediant-ℚ zero-ℚ (rational-ℚ⁺ x) ,
    is-positive-le-zero-ℚ
      ( mediant-ℚ zero-ℚ (rational-ℚ⁺ x))
      ( le-left-mediant-ℚ
        ( zero-ℚ)
        ( rational-ℚ⁺ x)
        ( le-zero-is-positive-ℚ (rational-ℚ⁺ x) (is-positive-rational-ℚ⁺ x))))

abstract
  le-mediant-zero-ℚ⁺ : (x : ℚ⁺) → le-ℚ⁺ (mediant-zero-ℚ⁺ x) x
  le-mediant-zero-ℚ⁺ x =
    le-right-mediant-ℚ
      ( zero-ℚ)
      ( rational-ℚ⁺ x)
      ( le-zero-is-positive-ℚ (rational-ℚ⁺ x) (is-positive-rational-ℚ⁺ x))
```

### Any positive rational number is the sum of two positive rational numbers

```agda
module _
  (x : ℚ⁺)
  where

  left-summand-split-ℚ⁺ : ℚ⁺
  left-summand-split-ℚ⁺ = mediant-zero-ℚ⁺ x

  right-summand-split-ℚ⁺ : ℚ⁺
  right-summand-split-ℚ⁺ =
    le-diff-ℚ⁺ (mediant-zero-ℚ⁺ x) x (le-mediant-zero-ℚ⁺ x)

  eq-add-split-ℚ⁺ :
    left-summand-split-ℚ⁺ +ℚ⁺ right-summand-split-ℚ⁺ ＝ x
  eq-add-split-ℚ⁺ =
    right-diff-law-add-ℚ⁺ (mediant-zero-ℚ⁺ x) x (le-mediant-zero-ℚ⁺ x)

  split-ℚ⁺ : Σ ℚ⁺ (λ u → Σ ℚ⁺ (λ v → u +ℚ⁺ v ＝ x))
  split-ℚ⁺ =
    left-summand-split-ℚ⁺ ,
    right-summand-split-ℚ⁺ ,
    eq-add-split-ℚ⁺
```

### Any two positive rational numbers have a positive rational number strictly less than both

```agda
module _
  (x y : ℚ⁺)
  where

  strict-min-law-ℚ⁺ : Σ ℚ⁺ (λ z → (le-ℚ⁺ z x) × (le-ℚ⁺ z y))
  strict-min-law-ℚ⁺ =
    rec-coproduct
      ( λ I →
        ( mediant-zero-ℚ⁺ x) ,
        ( le-mediant-zero-ℚ⁺ x) ,
        ( transitive-le-ℚ
          ( mediant-ℚ zero-ℚ (rational-ℚ⁺ x))
          ( rational-ℚ⁺ x)
          ( rational-ℚ⁺ y)
          ( I)
          ( le-mediant-zero-ℚ⁺ x)))
      ( λ I →
        ( mediant-zero-ℚ⁺ y) ,
        ( concatenate-le-leq-ℚ
          ( mediant-ℚ zero-ℚ (rational-ℚ⁺ y))
          ( rational-ℚ⁺ y)
          ( rational-ℚ⁺ x)
          ( le-mediant-zero-ℚ⁺ y)
          ( I)) ,
        ( le-mediant-zero-ℚ⁺ y))
      ( decide-le-leq-ℚ (rational-ℚ⁺ x) (rational-ℚ⁺ y))

  strict-min-ℚ⁺ : ℚ⁺
  strict-min-ℚ⁺ = pr1 strict-min-law-ℚ⁺

  le-left-min-ℚ⁺ : le-ℚ⁺ strict-min-ℚ⁺ x
  le-left-min-ℚ⁺ = pr1 (pr2 strict-min-law-ℚ⁺)

  le-right-min-ℚ⁺ : le-ℚ⁺ strict-min-ℚ⁺ y
  le-right-min-ℚ⁺ = pr2 (pr2 strict-min-law-ℚ⁺)
```

### Any positive rational number `p` has a `q` with `q + q < p`

```agda
abstract
  double-le-ℚ⁺ :
    (p : ℚ⁺) →
    exists ℚ⁺ (λ q → le-prop-ℚ⁺ (q +ℚ⁺ q) p)
  double-le-ℚ⁺ p = unit-trunc-Prop dependent-pair-result
    where
    q : ℚ⁺
    q = left-summand-split-ℚ⁺ p
    r : ℚ⁺
    r = right-summand-split-ℚ⁺ p
    s : ℚ⁺
    s = strict-min-ℚ⁺ q r
    -- Inlining this blows up compile times for some unclear reason.
    dependent-pair-result : Σ ℚ⁺ (λ x → le-ℚ⁺ (x +ℚ⁺ x) p)
    dependent-pair-result =
      s ,
      tr
        ( le-ℚ⁺ (s +ℚ⁺ s))
        ( eq-add-split-ℚ⁺ p)
        ( preserves-le-add-ℚ
          { rational-ℚ⁺ s}
          { rational-ℚ⁺ q}
          { rational-ℚ⁺ s}
          { rational-ℚ⁺ r}
          ( le-left-min-ℚ⁺ q r)
          ( le-right-min-ℚ⁺ q r))
```

### Addition with a positive rational number is an increasing map

```agda
le-left-add-rational-ℚ⁺ : (x : ℚ) (d : ℚ⁺) → le-ℚ x ((rational-ℚ⁺ d) +ℚ x)
le-left-add-rational-ℚ⁺ x d =
  concatenate-leq-le-ℚ
    ( x)
    ( zero-ℚ +ℚ x)
    ( (rational-ℚ⁺ d) +ℚ x)
    ( inv-tr (leq-ℚ x) (left-unit-law-add-ℚ x) (refl-leq-ℚ x))
    ( preserves-le-left-add-ℚ
      ( x)
      ( zero-ℚ)
      ( rational-ℚ⁺ d)
      ( le-zero-is-positive-ℚ
        ( rational-ℚ⁺ d)
        ( is-positive-rational-ℚ⁺ d)))

le-right-add-rational-ℚ⁺ : (x : ℚ) (d : ℚ⁺) → le-ℚ x (x +ℚ (rational-ℚ⁺ d))
le-right-add-rational-ℚ⁺ x d =
  inv-tr
    ( le-ℚ x)
    ( commutative-add-ℚ x (rational-ℚ⁺ d))
    ( le-left-add-rational-ℚ⁺ x d)
```

### Subtraction by a positive rational number is a strictly deflationary map

```agda
le-diff-rational-ℚ⁺ : (x : ℚ) (d : ℚ⁺) → le-ℚ (x -ℚ rational-ℚ⁺ d) x
le-diff-rational-ℚ⁺ x d =
  tr
    ( le-ℚ (x -ℚ rational-ℚ⁺ d))
    ( equational-reasoning
      (x -ℚ rational-ℚ⁺ d) +ℚ rational-ℚ⁺ d
      ＝ x +ℚ (neg-ℚ (rational-ℚ⁺ d) +ℚ rational-ℚ⁺ d)
        by associative-add-ℚ x (neg-ℚ (rational-ℚ⁺ d)) (rational-ℚ⁺ d)
      ＝ x +ℚ zero-ℚ
        by ap (x +ℚ_) (left-inverse-law-add-ℚ (rational-ℚ⁺ d))
      ＝ x by right-unit-law-add-ℚ x)
    ( le-right-add-rational-ℚ⁺ (x -ℚ rational-ℚ⁺ d) d)
```

### Characterization of inequality on the rational numbers by the additive action of `ℚ⁺`

For any `x y : ℚ`, the following conditions are equivalent:

- `x ≤ y`
- `∀ (δ : ℚ⁺) → x < y + δ`
- `∀ (δ : ℚ⁺) → x ≤ y + δ`

```agda
module _
  (x y : ℚ)
  where

  le-add-positive-leq-ℚ :
    (I : leq-ℚ x y) (d : ℚ⁺) → le-ℚ x (y +ℚ (rational-ℚ⁺ d))
  le-add-positive-leq-ℚ I d =
    concatenate-leq-le-ℚ
      ( x)
      ( y)
      ( y +ℚ (rational-ℚ⁺ d))
      ( I)
      ( le-right-add-rational-ℚ⁺ y d)

  leq-add-positive-le-add-positive-ℚ :
    ((d : ℚ⁺) → le-ℚ x (y +ℚ (rational-ℚ⁺ d))) →
    ((d : ℚ⁺) → leq-ℚ x (y +ℚ (rational-ℚ⁺ d)))
  leq-add-positive-le-add-positive-ℚ H d =
    leq-le-ℚ
      { x}
      { y +ℚ (rational-ℚ⁺ d)}
      (H d)

  leq-leq-add-positive-ℚ :
    ((d : ℚ⁺) → leq-ℚ x (y +ℚ (rational-ℚ⁺ d))) → leq-ℚ x y
  leq-leq-add-positive-ℚ H =
    rec-coproduct
      ( λ I →
        ex-falso
          ( not-leq-le-ℚ
            ( mediant-ℚ y x)
            ( x)
            ( le-right-mediant-ℚ y x I)
            ( tr
              ( leq-ℚ x)
              ( right-law-positive-diff-le-ℚ
                ( y)
                ( mediant-ℚ y x)
                ( le-left-mediant-ℚ y x I))
              ( H
                ( positive-diff-le-ℚ
                  ( y)
                  ( mediant-ℚ y x)
                  ( le-left-mediant-ℚ y x I))))))
      ( id)
      ( decide-le-leq-ℚ y x)

  equiv-leq-le-add-positive-ℚ :
    leq-ℚ x y ≃ ((d : ℚ⁺) → le-ℚ x (y +ℚ (rational-ℚ⁺ d)))
  equiv-leq-le-add-positive-ℚ =
    equiv-iff
      ( leq-ℚ-Prop x y)
      ( Π-Prop ℚ⁺ (λ d → le-ℚ-Prop x (y +ℚ (rational-ℚ⁺ d))))
      ( le-add-positive-leq-ℚ)
      ( leq-leq-add-positive-ℚ ∘ leq-add-positive-le-add-positive-ℚ)

  equiv-leq-leq-add-positive-ℚ :
    leq-ℚ x y ≃ ((d : ℚ⁺) → leq-ℚ x (y +ℚ (rational-ℚ⁺ d)))
  equiv-leq-leq-add-positive-ℚ =
    equiv-iff
      ( leq-ℚ-Prop x y)
      ( Π-Prop ℚ⁺ (λ d → leq-ℚ-Prop x (y +ℚ (rational-ℚ⁺ d))))
      ( leq-add-positive-le-add-positive-ℚ ∘ le-add-positive-leq-ℚ)
      ( leq-leq-add-positive-ℚ)
```

```agda
module _
  (x y : ℚ) (d : ℚ⁺)
  where

  le-le-add-positive-leq-add-positive-ℚ :
    (L : leq-ℚ y (x +ℚ (rational-ℚ⁺ d)))
    (r : ℚ)
    (I : le-ℚ (r +ℚ rational-ℚ⁺ d) y) →
    le-ℚ r x
  le-le-add-positive-leq-add-positive-ℚ L r I =
    reflects-le-left-add-ℚ
      ( rational-ℚ⁺ d)
      ( r)
      ( x)
      ( concatenate-le-leq-ℚ
        ( r +ℚ rational-ℚ⁺ d)
        ( y)
        ( x +ℚ rational-ℚ⁺ d)
        ( I)
        ( L))

  leq-add-positive-le-le-add-positive-ℚ :
    ((r : ℚ) → le-ℚ (r +ℚ rational-ℚ⁺ d) y → le-ℚ r x) →
    leq-ℚ y (x +ℚ rational-ℚ⁺ d)
  leq-add-positive-le-le-add-positive-ℚ L =
    rec-coproduct
      ( ex-falso ∘ (irreflexive-le-ℚ x) ∘ L x)
      ( id)
      ( decide-le-leq-ℚ (x +ℚ rational-ℚ⁺ d) y)
```
