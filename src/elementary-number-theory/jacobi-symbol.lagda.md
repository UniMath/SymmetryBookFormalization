# The Jacobi symbol

```agda
module elementary-number-theory.jacobi-symbol where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.fundamental-theorem-of-arithmetic
open import elementary-number-theory.integers
open import elementary-number-theory.legendre-symbol
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers

open import foundation.type-arithmetic-dependent-function-types
open import foundation.unit-type

open import lists.functoriality-lists
open import lists.lists
```

</details>

## Idea

The
{{#concept "Jacobi symbol" WD="Jacobi symbol" WDID=Q241015 Agda=jacobi-symbol}}
is a function which encodes information about the
[squareness](elementary-number-theory.squares-modular-arithmetic.md) of an
[integer](elementary-number-theory.integers.md) within certain
[rings of integers modulo `p`](elementary-number-theory.modular-arithmetic.md),
for [prime](elementary-number-theory.prime-numbers.md) `p`. Specifically,
`jacobi-symbol(a,n)` for an integer `a : ℤ` and natural number `n : ℕ` is the
product of the [legendre symbols](elementary-number-theory.legendre-symbol.md)

```text
  legendre-symbol(p₁,a) · legendre-symbol(p₂,a) · … · legendre-symbol(pₖ,a),
```

where `p₁, …, pₖ` are the prime factors of `n`, not necessarily distinct (i.e.
it is possible that `pᵢ = pⱼ`).

## Definition

```agda
jacobi-symbol : ℤ → ℕ → ℤ
jacobi-symbol a 0 = zero-ℤ
jacobi-symbol a 1 = one-ℤ
jacobi-symbol a (succ-ℕ (succ-ℕ n)) =
  fold-list
    ( one-ℤ)
    ( mul-ℤ)
    ( map-list
      ( swap-Π legendre-symbol a)
      ( list-of-primes-fundamental-theorem-arithmetic-ℕ
        ( succ-ℕ (succ-ℕ n))
        ( star)))
```
