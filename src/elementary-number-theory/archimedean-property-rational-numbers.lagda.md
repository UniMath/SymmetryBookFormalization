# The Archimedean property of `ℚ`

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.archimedean-property-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.archimedean-property-integer-fractions
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
```

</details>

## Definition

The
{{#concept "Archimedean property" Disambiguation="rational numbers" Agda=archimedean-property-ℚ}}
of `ℚ` is that for any two
[rational numbers](elementary-number-theory.rational-numbers.md) `x y : ℚ`, with
[positive](elementary-number-theory.positive-rational-numbers.md) `x`, there is
an `n : ℕ` such that `y` is less than `n` as a rational number times `x`.

```agda
abstract
  bound-archimedean-property-ℚ :
    (x y : ℚ) →
    is-positive-ℚ x →
    Σ ℕ (λ n → le-ℚ y (rational-ℤ (int-ℕ n) *ℚ x))
  bound-archimedean-property-ℚ x y pos-x =
    let
      (n , nx<y) =
        bound-archimedean-property-fraction-ℤ
          ( fraction-ℚ x)
          ( fraction-ℚ y)
          ( pos-x)
    in
      n ,
      binary-tr
        ( le-ℚ)
        ( is-retraction-rational-fraction-ℚ y)
        ( inv
          ( mul-rational-fraction-ℤ
            ( in-fraction-ℤ (int-ℕ n))
            ( fraction-ℚ x)) ∙
          ap-binary
            ( mul-ℚ)
            ( is-retraction-rational-fraction-ℚ (rational-ℤ (int-ℕ n)))
            ( is-retraction-rational-fraction-ℚ x))
        ( preserves-le-rational-fraction-ℤ
          ( fraction-ℚ y)
          ( in-fraction-ℤ (int-ℕ n) *fraction-ℤ fraction-ℚ x) nx<y)

  archimedean-property-ℚ :
    (x y : ℚ) →
      is-positive-ℚ x →
      exists ℕ (λ n → le-ℚ-Prop y (rational-ℤ (int-ℕ n) *ℚ x))
  archimedean-property-ℚ x y pos-x =
    unit-trunc-Prop (bound-archimedean-property-ℚ x y pos-x)
```
