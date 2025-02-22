# Pell numbers

```agda
module elementary-number-theory.pell-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
```

</details>

## Idea

The $n$th {{#concept "Pell number" Agda=pell-number-ℕ OEIS=A0000129 WDID=Q1386491 WD="Pell number"}} is the number $P(n)$, which are defined recursively by

```text
  P 0 := 0
  P 1 := 1
  P (n + 2) := 2 · P (n + 1) + P n.
```

The first few Pell numbers are

```text
  index        |    0 |    1 |    2 |    3 |    4 |    5 |    6 |    7 |    8 |
  -------------+------+------+------+------+------+------+------+------+------+
  Pell number  |    0 |    1 |    2 |    5 |   12 |   29 |   70 |  169 |  408 |
```

The sequence of Pell numbers is listed as A0000129 in the [OEIS](literature.oeis.md) {{#cite oeis}}. Any two consecutive Pell numbers are [relatively prime](elementary-number-theory.relatively-prime-natural-numbers.md).

## Definitions

### The Pell numbers

```agda
pell-number-ℕ : ℕ → ℕ
pell-number-ℕ zero-ℕ = 0
pell-number-ℕ (succ-ℕ zero-ℕ) = 1
pell-number-ℕ (succ-ℕ (succ-ℕ n)) =
  2 *ℕ pell-number-ℕ (succ-ℕ n) +ℕ pell-number-ℕ n
```

## References

{{#bibliography}}
