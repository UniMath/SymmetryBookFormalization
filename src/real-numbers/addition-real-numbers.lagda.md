# Addition on the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.addition-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.equality-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.subtypes
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
```

</details>

## Idea

We introduce addition on the
[Dedekind real numbers](real-numbers.dedekind-real-numbers.md) and derive its
basic properties.

## Definition

```agda
module _
  {l : Level}
  where
  add-L-ℝ : (x y : ℝ l) → subtype l ℚ
  add-L-ℝ x y q =
    ∃ ℚ ( λ r → ∃ ℚ ( λ s →
        conjunction-Prop (lower-cut-ℝ x r)
          ( conjunction-Prop (lower-cut-ℝ y s)
            ( q ＝ r +ℚ s , is-prop-eq-ℚ))))

  add-U-ℝ : (x y : ℝ l) → subtype l ℚ
  add-U-ℝ x y q =
    ∃ ℚ ( λ r → ∃ ℚ ( λ s →
      conjunction-Prop (upper-cut-ℝ x r)
        ( conjunction-Prop (upper-cut-ℝ y s)
          ( q ＝ r +ℚ s , is-prop-eq-ℚ))))

  neg-L-ℝ : (x : ℝ l) → subtype l ℚ
  neg-L-ℝ x q =
    ∃ ℚ ( λ r → conjunction-Prop (upper-cut-ℝ x r)
            ( q ＝ neg-ℚ r , is-prop-eq-ℚ))

  neg-U-ℝ : (x : ℝ l) → subtype l ℚ
  neg-U-ℝ x q =
    ∃ ℚ ( λ r → conjunction-Prop (lower-cut-ℝ x r)
            ( q ＝ neg-ℚ r , is-prop-eq-ℚ))

  -- need to also add dedekind cut checks all around
```
