# The Archimedean property of `ℚ⁺`

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.archimedean-property-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.archimedean-property-rational-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
```

</details>

## Definition

The
{{#concept "Archimedean property" Disambiguation="positive rational numbers" Agda=archimedean-property-ℚ⁺}}
of `ℚ⁺` is that for any two
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
`x y : ℚ⁺`, there is an `n : ℕ⁺` such that `y` is less than `n` as a rational
number times `x`.

```agda
abstract
  bound-archimedean-property-ℚ⁺ :
    (x y : ℚ⁺) →
    Σ ℕ⁺ (λ n → le-ℚ⁺ y (positive-rational-ℕ⁺ n *ℚ⁺ x))
  bound-archimedean-property-ℚ⁺ (x , pos-x) (y , pos-y) =
    let
      (n , y<nx) = bound-archimedean-property-ℚ x y pos-x
      n≠0 : is-nonzero-ℕ n
      n≠0 n=0 =
        asymmetric-le-ℚ
          ( zero-ℚ)
          ( y)
          ( le-zero-is-positive-ℚ y pos-y)
          ( tr
            ( le-ℚ y)
            ( equational-reasoning
              rational-ℤ (int-ℕ n) *ℚ x
              ＝ rational-ℤ (int-ℕ 0) *ℚ x
                by ap (λ m → rational-ℤ (int-ℕ m) *ℚ x) n=0
              ＝ zero-ℚ by left-zero-law-mul-ℚ x)
            y<nx)
    in (n , n≠0) , y<nx

  archimedean-property-ℚ⁺ :
    (x y : ℚ⁺) →
    exists ℕ⁺ (λ n → le-prop-ℚ⁺ y (positive-rational-ℕ⁺ n *ℚ⁺ x))
  archimedean-property-ℚ⁺ x y =
    unit-trunc-Prop (bound-archimedean-property-ℚ⁺ x y)
```

## Corollaries

### For every positive rational number, there is a smaller `1 / n` for a natural number n

```agda
smaller-reciprocal-ℚ⁺ :
  (q : ℚ⁺) → Σ ℕ⁺ (λ n → le-ℚ⁺ (positive-reciprocal-rational-ℕ⁺ n) q)
smaller-reciprocal-ℚ⁺ q⁺@(q , _) =
  let (n⁺ , 1<nq) = bound-archimedean-property-ℚ⁺ q⁺ one-ℚ⁺ in
  n⁺ ,
  binary-tr
    ( le-ℚ)
    ( right-unit-law-mul-ℚ _)
    ( ap
      ( rational-ℚ⁺)
      ( equational-reasoning
        positive-reciprocal-rational-ℕ⁺ n⁺ *ℚ⁺
          (positive-rational-ℕ⁺ n⁺ *ℚ⁺ q⁺)
        ＝ (positive-reciprocal-rational-ℕ⁺ n⁺ *ℚ⁺ positive-rational-ℕ⁺ n⁺)
          *ℚ⁺ q⁺
          by inv (associative-mul-ℚ⁺ _ _ _)
        ＝ one-ℚ⁺ *ℚ⁺ q⁺ by ap (_*ℚ⁺ q⁺) (left-inverse-law-mul-ℚ⁺ _)
        ＝ q⁺ by left-unit-law-mul-ℚ⁺ q⁺))
    ( preserves-le-left-mul-ℚ⁺
      ( positive-reciprocal-rational-ℕ⁺ n⁺)
      ( one-ℚ)
      ( rational-ℚ⁺ (positive-rational-ℕ⁺ n⁺ *ℚ⁺ q⁺))
      ( 1<nq))
```
