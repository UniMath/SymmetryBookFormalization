# Unbounded Farey fractions

```agda
module elementary-number-theory.unbounded-farey-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers

open import foundation.universe-levels
```

</details>

## Idea

[Farey fractions](elementary-number-theory.farey-fractions.md) are a way of
encoding all [rational numbers](elementary-number-theory.rational-numbers.md)
between $0$ and $1$ inclusive. This idea can be generalized to encode all
rational numbers.

The type of
{{#concept "unbounded Farey fractions" Agda=unbounded-farey-fraction}} is an
inductive type that is mutually defined with an adjacency relation, given with
the following constructors:

```text
  𝒾 : ℤ → ℱ
  𝓂 : (x y : ℱ) → ℛ x y → ℱ

  𝓈 : (a : ℤ) → ℛ (𝒾 a) (𝒾 (a + 1))
  𝓇 : (x y : ℱ) (r : ℛ x y) → ℛ x (𝓂 x y r)
  𝓁 : (x y : ℱ) (r : ℛ x y) → ℛ (𝓂 x y r) y.
```

## Definitions

### Unbounded Farey fractions

```agda
mutual

  data
    unbounded-farey-fraction : UU lzero
    where

    farey-integer :
      ℤ → unbounded-farey-fraction

    mediant-unbounded-farey-fraction :
      (x y : unbounded-farey-fraction) →
      adjacent-unbounded-farey-fraction x y → unbounded-farey-fraction

  data
    adjacent-unbounded-farey-fraction :
      unbounded-farey-fraction → unbounded-farey-fraction → UU lzero
    where

    adjacent-farey-integer-succ :
      (a : ℤ) →
      adjacent-unbounded-farey-fraction
        ( farey-integer a)
        ( farey-integer (succ-ℤ a))

    right-adjacent-mediant-unbounded-farey-fraction :
      (x y : unbounded-farey-fraction)
      (H : adjacent-unbounded-farey-fraction x y) →
      adjacent-unbounded-farey-fraction
        ( x)
        ( mediant-unbounded-farey-fraction x y H)

    left-adjacent-mediant-unbounded-farey-fraction :
      (x y : unbounded-farey-fraction)
      (H : adjacent-unbounded-farey-fraction x y) →
      adjacent-unbounded-farey-fraction
        ( mediant-unbounded-farey-fraction x y H)
        ( y)
```
