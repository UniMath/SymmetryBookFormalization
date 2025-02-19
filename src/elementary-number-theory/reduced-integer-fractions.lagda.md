# Reduced integer fractions

```agda
module elementary-number-theory.reduced-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.bezouts-lemma-integers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.equality-integers
open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.relatively-prime-integers
open import elementary-number-theory.unit-similarity-integers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "reduced fraction" Agda=is-reduced-fraction-ℤ}} is a
[fraction](elementary-number-theory.integer-fractions.md) in which its numerator
and denominator are
[coprime](elementary-number-theory.relatively-prime-integers.md). In the module
[`elementary-number-theory.rational-numbers`](elementary-number-theory.rational-numbers.md)
we will define the type `ℚ` of rational numbers to be the type of reduced
integer fractions.

## Definitions

### The predicate of being a reduced fraction

```agda
is-reduced-fraction-ℤ : fraction-ℤ → UU lzero
is-reduced-fraction-ℤ x =
  is-relative-prime-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x)
```

## Properties and constructions

### Being a reduced fraction is a proposition

```agda
is-prop-is-reduced-fraction-ℤ :
  (x : fraction-ℤ) → is-prop (is-reduced-fraction-ℤ x)
is-prop-is-reduced-fraction-ℤ x =
  is-prop-is-relative-prime-ℤ
    ( numerator-fraction-ℤ x)
    ( denominator-fraction-ℤ x)
```

### The negative of a reduced integer fraction is reduced

```agda
is-reduced-neg-fraction-ℤ :
  (x : fraction-ℤ) →
  is-reduced-fraction-ℤ x →
  is-reduced-fraction-ℤ (neg-fraction-ℤ x)
is-reduced-neg-fraction-ℤ x =
  tr
    ( is-one-ℤ)
    ( inv
      ( preserves-gcd-left-neg-ℤ
        ( numerator-fraction-ℤ x)
        ( denominator-fraction-ℤ x)))
```

### Any fraction can be reduced

```agda
reduce-numerator-fraction-ℤ :
  (x : fraction-ℤ) →
  div-ℤ
    ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
    ( numerator-fraction-ℤ x)
reduce-numerator-fraction-ℤ x =
  div-left-gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x)

int-reduce-numerator-fraction-ℤ : fraction-ℤ → ℤ
int-reduce-numerator-fraction-ℤ x = pr1 (reduce-numerator-fraction-ℤ x)

eq-reduce-numerator-fraction-ℤ :
  (x : fraction-ℤ) →
  ( mul-ℤ
    ( int-reduce-numerator-fraction-ℤ x)
    ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))) ＝
  ( numerator-fraction-ℤ x)
eq-reduce-numerator-fraction-ℤ x = pr2 (reduce-numerator-fraction-ℤ x)

reduce-denominator-fraction-ℤ :
  (x : fraction-ℤ) →
  div-ℤ
    ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
    ( denominator-fraction-ℤ x)
reduce-denominator-fraction-ℤ x =
  div-right-gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x)

int-reduce-denominator-fraction-ℤ : fraction-ℤ → ℤ
int-reduce-denominator-fraction-ℤ x =
  pr1 (reduce-denominator-fraction-ℤ x)

eq-reduce-denominator-fraction-ℤ :
  (x : fraction-ℤ) →
  ( mul-ℤ
    ( int-reduce-denominator-fraction-ℤ x)
    ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))) ＝
  ( denominator-fraction-ℤ x)
eq-reduce-denominator-fraction-ℤ x =
  pr2 (reduce-denominator-fraction-ℤ x)

is-positive-int-reduce-denominator-fraction-ℤ :
  (x : fraction-ℤ) → is-positive-ℤ (int-reduce-denominator-fraction-ℤ x)
is-positive-int-reduce-denominator-fraction-ℤ x =
  is-positive-left-factor-mul-ℤ
    ( is-positive-eq-ℤ
      ( inv (eq-reduce-denominator-fraction-ℤ x))
      ( is-positive-denominator-fraction-ℤ x))
    ( is-positive-gcd-is-positive-right-ℤ
      ( numerator-fraction-ℤ x)
      ( denominator-fraction-ℤ x)
      ( is-positive-denominator-fraction-ℤ x))

reduce-fraction-ℤ : fraction-ℤ → fraction-ℤ
reduce-fraction-ℤ x =
  pair
    ( int-reduce-numerator-fraction-ℤ x)
    ( pair
      ( int-reduce-denominator-fraction-ℤ x)
      ( is-positive-int-reduce-denominator-fraction-ℤ x))

is-reduced-reduce-fraction-ℤ :
  (x : fraction-ℤ) → is-reduced-fraction-ℤ (reduce-fraction-ℤ x)
is-reduced-reduce-fraction-ℤ x =
  is-zero-gcd-case-split
    ( is-decidable-is-zero-ℤ
      ( gcd-ℤ
        ( numerator-fraction-ℤ (reduce-fraction-ℤ x))
        ( denominator-fraction-ℤ (reduce-fraction-ℤ x))))
  where
  is-zero-gcd-case-split :
    ( is-zero-ℤ
      ( gcd-ℤ
        ( numerator-fraction-ℤ (reduce-fraction-ℤ x))
        ( denominator-fraction-ℤ (reduce-fraction-ℤ x))) +
      ¬ (is-zero-ℤ
        ( gcd-ℤ
          ( numerator-fraction-ℤ (reduce-fraction-ℤ x))
          ( denominator-fraction-ℤ (reduce-fraction-ℤ x))))) →
    is-reduced-fraction-ℤ (reduce-fraction-ℤ x)
  is-zero-gcd-case-split (inl z) =
    ex-falso (tr is-positive-ℤ
      ( is-zero-right-is-zero-gcd-ℤ
        ( numerator-fraction-ℤ (reduce-fraction-ℤ x))
          ( denominator-fraction-ℤ (reduce-fraction-ℤ x)) z)
          ( is-positive-denominator-fraction-ℤ (reduce-fraction-ℤ x)))
  is-zero-gcd-case-split (inr nz) =
    is-plus-or-minus-case-split
      ( is-plus-or-minus-sim-unit-ℤ
      ( antisymmetric-div-ℤ (alpha *ℤ d) d
        ( div-gcd-is-common-divisor-ℤ
          ( numerator-fraction-ℤ x)
          ( denominator-fraction-ℤ x)
          ( alpha *ℤ d)
          ( pair
            -- alpha * d divides the numerator of x
            ( tr
              ( λ u → div-ℤ u (numerator-fraction-ℤ x))
              ( commutative-mul-ℤ d alpha)
              ( div-div-quotient-div-ℤ alpha (numerator-fraction-ℤ x) d
                ( pr1 ( is-common-divisor-gcd-ℤ
                  ( numerator-fraction-ℤ x)
                  ( denominator-fraction-ℤ x)))
                ( pr1 ( is-common-divisor-gcd-ℤ
                  ( numerator-fraction-ℤ (reduce-fraction-ℤ x))
                  ( denominator-fraction-ℤ (reduce-fraction-ℤ x))))))
            -- alpha * d divides the denominator of x
            ( tr
              ( λ u → div-ℤ u (denominator-fraction-ℤ x))
              ( commutative-mul-ℤ d alpha)
              ( div-div-quotient-div-ℤ alpha (denominator-fraction-ℤ x) d
                ( pr2 ( is-common-divisor-gcd-ℤ
                  ( numerator-fraction-ℤ x)
                  ( denominator-fraction-ℤ x)))
                ( pr2 ( is-common-divisor-gcd-ℤ
                  ( numerator-fraction-ℤ (reduce-fraction-ℤ x))
                  ( denominator-fraction-ℤ (reduce-fraction-ℤ x))))))))
        (pair ( gcd-ℤ ( numerator-fraction-ℤ (reduce-fraction-ℤ x))
          ( denominator-fraction-ℤ (reduce-fraction-ℤ x))) refl)))
    where
    alpha : ℤ
    alpha =
      gcd-ℤ
        ( numerator-fraction-ℤ (reduce-fraction-ℤ x))
        ( denominator-fraction-ℤ (reduce-fraction-ℤ x))
    d : ℤ
    d = gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x)
    is-plus-or-minus-case-split :
      (is-plus-or-minus-ℤ (alpha *ℤ d) d) →
      is-reduced-fraction-ℤ (reduce-fraction-ℤ x)
    is-plus-or-minus-case-split (inl pos) =
      ( is-injective-right-mul-ℤ d
        ( λ r → tr is-positive-ℤ r
          ( is-positive-gcd-is-positive-right-ℤ
            ( numerator-fraction-ℤ x) ( denominator-fraction-ℤ x)
            ( is-positive-denominator-fraction-ℤ x)))) pos
    is-plus-or-minus-case-split (inr neg) =
      (ex-falso
        ( tr is-positive-ℤ {y = neg-ℤ one-ℤ}
          ( inv
            ( neg-neg-ℤ
              ( gcd-ℤ
                ( numerator-fraction-ℤ (reduce-fraction-ℤ x))
                ( denominator-fraction-ℤ (reduce-fraction-ℤ x)))) ∙
            ( ap neg-ℤ
              ( is-injective-right-mul-ℤ d
                ( λ r →
                  tr is-positive-ℤ r
                    ( is-positive-gcd-is-positive-right-ℤ
                      ( numerator-fraction-ℤ x)
                      ( denominator-fraction-ℤ x)
                      ( is-positive-denominator-fraction-ℤ x)))
                ( associative-mul-ℤ
                  ( neg-one-ℤ)
                  ( gcd-ℤ ( numerator-fraction-ℤ (reduce-fraction-ℤ x))
              ( denominator-fraction-ℤ (reduce-fraction-ℤ x)))
              d ∙ neg))))
          ( is-positive-gcd-ℤ
            ( numerator-fraction-ℤ (reduce-fraction-ℤ x))
            ( denominator-fraction-ℤ (reduce-fraction-ℤ x))
            ( inr (is-positive-denominator-fraction-ℤ (reduce-fraction-ℤ x))))))

sim-reduced-fraction-ℤ :
  (x : fraction-ℤ) → (sim-fraction-ℤ x (reduce-fraction-ℤ x))
sim-reduced-fraction-ℤ x =
  equational-reasoning
    (numerator-fraction-ℤ x) *ℤ (denominator-fraction-ℤ (reduce-fraction-ℤ x))
    ＝ ((numerator-fraction-ℤ (reduce-fraction-ℤ x)) *ℤ
        (gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))) *ℤ
        (denominator-fraction-ℤ (reduce-fraction-ℤ x))
      by ap (_*ℤ (denominator-fraction-ℤ (reduce-fraction-ℤ x)))
          (inv (eq-reduce-numerator-fraction-ℤ x))
    ＝ (numerator-fraction-ℤ (reduce-fraction-ℤ x)) *ℤ
      ((gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x)) *ℤ
        (denominator-fraction-ℤ (reduce-fraction-ℤ x)))
      by associative-mul-ℤ (numerator-fraction-ℤ (reduce-fraction-ℤ x))
        (gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
        (denominator-fraction-ℤ (reduce-fraction-ℤ x))
    ＝ (numerator-fraction-ℤ (reduce-fraction-ℤ x)) *ℤ (denominator-fraction-ℤ x)
      by
        ap
        ( (numerator-fraction-ℤ (reduce-fraction-ℤ x)) *ℤ_)
        ( ( commutative-mul-ℤ
            ( gcd-ℤ (numerator-fraction-ℤ x) (denominator-fraction-ℤ x))
            ( denominator-fraction-ℤ (reduce-fraction-ℤ x))) ∙
          ( eq-reduce-denominator-fraction-ℤ x))

reduce-preserves-sim-ℤ :
  (x y : fraction-ℤ) (H : sim-fraction-ℤ x y) →
  sim-fraction-ℤ (reduce-fraction-ℤ x) (reduce-fraction-ℤ y)
reduce-preserves-sim-ℤ x y H =
  transitive-sim-fraction-ℤ
    ( reduce-fraction-ℤ x)
    ( y)
    ( reduce-fraction-ℤ y)
    ( sim-reduced-fraction-ℤ y)
    ( transitive-sim-fraction-ℤ
      ( reduce-fraction-ℤ x)
      ( x)
      ( y)
      ( H)
      ( symmetric-sim-fraction-ℤ
        ( x)
        ( reduce-fraction-ℤ x)
        ( sim-reduced-fraction-ℤ x)))
```

### Two similar fractions have equal reduced form

```agda
sim-unique-numerator-reduce-fraction-ℤ :
  ( x y : fraction-ℤ) →
  ( H : sim-fraction-ℤ x y) →
  sim-unit-ℤ
    ( int-reduce-numerator-fraction-ℤ x)
    ( int-reduce-numerator-fraction-ℤ y)
sim-unique-numerator-reduce-fraction-ℤ x y H =
  antisymmetric-div-ℤ
    ( int-reduce-numerator-fraction-ℤ x)
    ( int-reduce-numerator-fraction-ℤ y)
    ( div-red-x-red-y)
    ( div-red-y-red-x)
  where
  reduced-eqn :
    mul-ℤ
      ( int-reduce-numerator-fraction-ℤ x)
      ( int-reduce-denominator-fraction-ℤ y) ＝
    mul-ℤ
      ( int-reduce-numerator-fraction-ℤ y)
      ( int-reduce-denominator-fraction-ℤ x)
  reduced-eqn = reduce-preserves-sim-ℤ x y H
  div-red-x-num :
    div-ℤ
      ( int-reduce-numerator-fraction-ℤ x)
      ( mul-ℤ
        ( int-reduce-denominator-fraction-ℤ x)
        ( int-reduce-numerator-fraction-ℤ y))
  div-red-x-num =
    pair
      ( int-reduce-denominator-fraction-ℤ y)
      ( commutative-mul-ℤ
        ( int-reduce-denominator-fraction-ℤ y)
        ( int-reduce-numerator-fraction-ℤ x) ∙
        ( reduced-eqn ∙
          commutative-mul-ℤ
            ( int-reduce-numerator-fraction-ℤ y)
            ( int-reduce-denominator-fraction-ℤ x)))
  red-x-coprime :
    gcd-ℤ
      ( int-reduce-numerator-fraction-ℤ x)
      ( int-reduce-denominator-fraction-ℤ x) ＝
    one-ℤ
  red-x-coprime = is-reduced-reduce-fraction-ℤ x
  div-red-x-red-y :
    div-ℤ
      ( int-reduce-numerator-fraction-ℤ x)
      ( int-reduce-numerator-fraction-ℤ y)
  div-red-x-red-y = div-right-factor-coprime-ℤ
    (int-reduce-numerator-fraction-ℤ x)
    (int-reduce-denominator-fraction-ℤ x)
    (int-reduce-numerator-fraction-ℤ y)
    div-red-x-num red-x-coprime
  div-red-y-num :
    div-ℤ
      ( int-reduce-numerator-fraction-ℤ y)
      ( mul-ℤ
        ( int-reduce-denominator-fraction-ℤ y)
        ( int-reduce-numerator-fraction-ℤ x))
  div-red-y-num = pair (int-reduce-denominator-fraction-ℤ x)
    ( commutative-mul-ℤ
      ( int-reduce-denominator-fraction-ℤ x)
      ( int-reduce-numerator-fraction-ℤ y) ∙
      ( inv (reduced-eqn) ∙
        commutative-mul-ℤ
          ( int-reduce-numerator-fraction-ℤ x)
          ( int-reduce-denominator-fraction-ℤ y)))
  red-y-coprime :
    gcd-ℤ
      ( int-reduce-numerator-fraction-ℤ y)
      ( int-reduce-denominator-fraction-ℤ y) ＝
    one-ℤ
  red-y-coprime = is-reduced-reduce-fraction-ℤ y
  div-red-y-red-x :
    div-ℤ
      ( int-reduce-numerator-fraction-ℤ y)
      ( int-reduce-numerator-fraction-ℤ x)
  div-red-y-red-x = div-right-factor-coprime-ℤ
    (int-reduce-numerator-fraction-ℤ y)
    (int-reduce-denominator-fraction-ℤ y)
    (int-reduce-numerator-fraction-ℤ x)
    div-red-y-num red-y-coprime

unique-numerator-reduce-fraction-ℤ :
  ( x y : fraction-ℤ) →
  ( H : sim-fraction-ℤ x y) →
  int-reduce-numerator-fraction-ℤ x ＝
  int-reduce-numerator-fraction-ℤ y
unique-numerator-reduce-fraction-ℤ x y H =
  is-zero-num-case-split
    (is-decidable-is-zero-ℤ (int-reduce-numerator-fraction-ℤ x))
  where
  is-zero-num-case-split :
    ( is-zero-ℤ (int-reduce-numerator-fraction-ℤ x) +
      ¬ (is-zero-ℤ (int-reduce-numerator-fraction-ℤ x))) →
    int-reduce-numerator-fraction-ℤ x ＝ int-reduce-numerator-fraction-ℤ y
  is-zero-num-case-split (inl z) =
    z ∙
    inv (is-zero-sim-unit-ℤ (sim-unique-numerator-reduce-fraction-ℤ x y H) z)
  is-zero-num-case-split (inr nz) =
    is-plus-or-minus-case-split
      ( is-plus-or-minus-sim-unit-ℤ
        ( sim-unique-numerator-reduce-fraction-ℤ x y H))
    where
    is-plus-or-minus-case-split :
      is-plus-or-minus-ℤ
        ( int-reduce-numerator-fraction-ℤ x)
        ( int-reduce-numerator-fraction-ℤ y) →
      int-reduce-numerator-fraction-ℤ x ＝ int-reduce-numerator-fraction-ℤ y
    is-plus-or-minus-case-split (inl pos) = pos
    is-plus-or-minus-case-split (inr neg) =
      ex-falso (Eq-eq-ℤ contra)
      where
      lem : (w : ℤ) → is-positive-ℤ w → Σ ℕ (λ n → w ＝ inr (inr n))
      lem (inr (inr n)) H = pair n refl

      reduced-eqn :
        mul-ℤ
          ( int-reduce-numerator-fraction-ℤ x)
          ( int-reduce-denominator-fraction-ℤ y) ＝
        mul-ℤ
          ( int-reduce-numerator-fraction-ℤ x)
          ( neg-one-ℤ *ℤ (int-reduce-denominator-fraction-ℤ x))
      reduced-eqn =
        equational-reasoning
          mul-ℤ
            ( int-reduce-numerator-fraction-ℤ x)
            ( int-reduce-denominator-fraction-ℤ y)
          ＝ mul-ℤ
              ( int-reduce-numerator-fraction-ℤ y)
              ( int-reduce-denominator-fraction-ℤ x)
            by reduce-preserves-sim-ℤ x y H
          ＝ mul-ℤ
              ( (int-reduce-numerator-fraction-ℤ x) *ℤ neg-one-ℤ)
              ( int-reduce-denominator-fraction-ℤ x)
            by
              ap
                ( _*ℤ (int-reduce-denominator-fraction-ℤ x))
                ( inv neg ∙
                  commutative-mul-ℤ
                    ( neg-one-ℤ)
                    ( int-reduce-numerator-fraction-ℤ x))
          ＝ mul-ℤ
              ( int-reduce-numerator-fraction-ℤ x)
              ( neg-one-ℤ *ℤ (int-reduce-denominator-fraction-ℤ x))
            by
              associative-mul-ℤ
                ( int-reduce-numerator-fraction-ℤ x)
                ( neg-one-ℤ)
                ( int-reduce-denominator-fraction-ℤ x)

      x-nat : ℕ
      x-nat =
        pr1
          ( lem
            ( int-reduce-denominator-fraction-ℤ x)
            ( is-positive-int-reduce-denominator-fraction-ℤ x))

      y-nat : ℕ
      y-nat =
        pr1
          ( lem
            ( int-reduce-denominator-fraction-ℤ y)
            ( is-positive-int-reduce-denominator-fraction-ℤ y))

      contra : inr (inr y-nat) ＝ neg-ℤ (inr (inr x-nat))
      contra =
        equational-reasoning
          inr (inr y-nat)
          ＝ (int-reduce-denominator-fraction-ℤ y)
            by
              inv
                ( pr2
                  ( lem
                    ( int-reduce-denominator-fraction-ℤ y)
                    ( is-positive-int-reduce-denominator-fraction-ℤ y)))
          ＝ neg-ℤ (int-reduce-denominator-fraction-ℤ x)
            by
              is-injective-left-mul-ℤ
                ( int-reduce-numerator-fraction-ℤ x)
                ( nz)
                ( reduced-eqn)
          ＝ neg-ℤ (inr (inr x-nat))
            by
              ap
                ( neg-ℤ)
                ( pr2
                  ( lem
                    ( int-reduce-denominator-fraction-ℤ x)
                    ( is-positive-int-reduce-denominator-fraction-ℤ x)))

sim-unique-denominator-reduce-fraction-ℤ :
  ( x y : fraction-ℤ) →
  ( H : sim-fraction-ℤ x y) →
  sim-unit-ℤ
    ( int-reduce-denominator-fraction-ℤ x)
    ( int-reduce-denominator-fraction-ℤ y)
sim-unique-denominator-reduce-fraction-ℤ x y H = antisymmetric-div-ℤ
  (int-reduce-denominator-fraction-ℤ x)
  (int-reduce-denominator-fraction-ℤ y)
  div-red-x-red-y div-red-y-red-x
  where
  reduced-eqn :
    mul-ℤ
      ( int-reduce-numerator-fraction-ℤ x)
      ( int-reduce-denominator-fraction-ℤ y) ＝
    mul-ℤ
      ( int-reduce-numerator-fraction-ℤ y)
      ( int-reduce-denominator-fraction-ℤ x)
  reduced-eqn = reduce-preserves-sim-ℤ x y H
  div-red-x-num :
    div-ℤ
      ( int-reduce-denominator-fraction-ℤ x)
      ( mul-ℤ
        ( int-reduce-numerator-fraction-ℤ x)
        ( int-reduce-denominator-fraction-ℤ y))
  div-red-x-num = pair (int-reduce-numerator-fraction-ℤ y)
    (inv (reduced-eqn))
  red-x-coprime :
    gcd-ℤ
      ( int-reduce-denominator-fraction-ℤ x)
      ( int-reduce-numerator-fraction-ℤ x) ＝
    one-ℤ
  red-x-coprime =
    is-commutative-gcd-ℤ
      ( int-reduce-denominator-fraction-ℤ x)
      ( int-reduce-numerator-fraction-ℤ x) ∙
    is-reduced-reduce-fraction-ℤ x
  div-red-x-red-y :
    div-ℤ
      ( int-reduce-denominator-fraction-ℤ x)
      ( int-reduce-denominator-fraction-ℤ y)
  div-red-x-red-y = div-right-factor-coprime-ℤ
    (int-reduce-denominator-fraction-ℤ x)
    (int-reduce-numerator-fraction-ℤ x)
    (int-reduce-denominator-fraction-ℤ y)
    div-red-x-num red-x-coprime
  div-red-y-num :
    div-ℤ
      ( int-reduce-denominator-fraction-ℤ y)
      ( mul-ℤ
        ( int-reduce-numerator-fraction-ℤ y)
        ( int-reduce-denominator-fraction-ℤ x))
  div-red-y-num = pair (int-reduce-numerator-fraction-ℤ x)
    (reduced-eqn)
  red-y-coprime :
    gcd-ℤ
      ( int-reduce-denominator-fraction-ℤ y)
      ( int-reduce-numerator-fraction-ℤ y) ＝
    one-ℤ
  red-y-coprime =
    is-commutative-gcd-ℤ
      ( int-reduce-denominator-fraction-ℤ y)
      ( int-reduce-numerator-fraction-ℤ y) ∙
    is-reduced-reduce-fraction-ℤ y
  div-red-y-red-x :
    div-ℤ
      ( int-reduce-denominator-fraction-ℤ y)
      ( int-reduce-denominator-fraction-ℤ x)
  div-red-y-red-x = div-right-factor-coprime-ℤ
    (int-reduce-denominator-fraction-ℤ y)
    (int-reduce-numerator-fraction-ℤ y)
    (int-reduce-denominator-fraction-ℤ x)
    div-red-y-num red-y-coprime

unique-denominator-reduce-fraction-ℤ :
  (x y : fraction-ℤ) → (H : sim-fraction-ℤ x y) →
  int-reduce-denominator-fraction-ℤ x ＝ int-reduce-denominator-fraction-ℤ y
unique-denominator-reduce-fraction-ℤ x y H =
  eq-sim-unit-is-nonnegative-ℤ
    ( is-nonnegative-is-positive-ℤ
      ( is-positive-int-reduce-denominator-fraction-ℤ x))
    ( is-nonnegative-is-positive-ℤ
      ( is-positive-int-reduce-denominator-fraction-ℤ y))
    (sim-unique-denominator-reduce-fraction-ℤ x y H)

unique-reduce-fraction-ℤ :
  (x y : fraction-ℤ) → (H : sim-fraction-ℤ x y) →
  reduce-fraction-ℤ x ＝ reduce-fraction-ℤ y
unique-reduce-fraction-ℤ x y H =
  eq-pair'
    ( pair
      ( unique-numerator-reduce-fraction-ℤ x y H)
      ( eq-pair-Σ'
        ( pair
          ( unique-denominator-reduce-fraction-ℤ x y H)
          ( eq-is-prop
            ( is-prop-is-positive-ℤ (int-reduce-denominator-fraction-ℤ y))))))
```

## See also

- [The type of rational numbers](elementary-number-theory.rational-numbers.md)
