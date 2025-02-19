# The cofibonacci sequence

```agda
module elementary-number-theory.cofibonacci where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.fibonacci-sequence
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.minimal-structured-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.pisano-periods
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

The {{#concept "cofibonacci sequence" Agda=cofibonacci}} is the unique function
`G : ℕ → ℕ` satisfying the property that

```text
  div-ℕ (G m) n ↔ div-ℕ m (fibonacci-ℕ n).
```

The sequence starts

```text
  n   0   1   2   3   4   5   6   7   8   9  10  11  12  13
  Gₙ  1   3   4   6   5  12   8   6  12  15  10  12   7  24  ⋯
```

## Definitions

### The predicate of being a multiple of the `m`-th cofibonacci number

```agda
is-multiple-of-cofibonacci : (m x : ℕ) → UU lzero
is-multiple-of-cofibonacci m x =
  is-nonzero-ℕ m → is-nonzero-ℕ x × div-ℕ m (fibonacci-ℕ x)

is-decidable-is-multiple-of-cofibonacci :
  (m x : ℕ) → is-decidable (is-multiple-of-cofibonacci m x)
is-decidable-is-multiple-of-cofibonacci m x =
  is-decidable-function-type
    ( is-decidable-zero-is-nonzero-ℕ m)
    ( is-decidable-product
      ( is-decidable-zero-is-nonzero-ℕ x)
      ( is-decidable-div-ℕ m (fibonacci-ℕ x)))

cofibonacci-multiple : (m : ℕ) → Σ ℕ (is-multiple-of-cofibonacci m)
cofibonacci-multiple zero-ℕ = pair zero-ℕ (λ f → (ex-falso (f refl)))
cofibonacci-multiple (succ-ℕ m) =
  pair
    ( pisano-period m)
    ( λ f → pair (is-nonzero-pisano-period m) (div-fibonacci-pisano-period m))
```

### The cofibonacci sequence

```agda
least-multiple-of-cofibonacci :
  (m : ℕ) → minimal-element-ℕ (is-multiple-of-cofibonacci m)
least-multiple-of-cofibonacci m =
  well-ordering-principle-ℕ
    ( is-multiple-of-cofibonacci m)
    ( is-decidable-is-multiple-of-cofibonacci m)
    ( pr2 (cofibonacci-multiple m))

cofibonacci : ℕ → ℕ
cofibonacci m = pr1 (least-multiple-of-cofibonacci m)

is-multiple-of-cofibonacci-cofibonacci :
  (m : ℕ) → is-multiple-of-cofibonacci m (cofibonacci m)
is-multiple-of-cofibonacci-cofibonacci m =
  pr1 (pr2 (least-multiple-of-cofibonacci m))

is-lower-bound-cofibonacci :
  (m x : ℕ) → is-multiple-of-cofibonacci m x →
  cofibonacci m ≤-ℕ x
is-lower-bound-cofibonacci m =
  pr2 (pr2 (least-multiple-of-cofibonacci m))
```

## Properties

### The `0`-th cofibonacci number is `0`

```agda
is-zero-cofibonacci-zero-ℕ : is-zero-ℕ (cofibonacci zero-ℕ)
is-zero-cofibonacci-zero-ℕ =
  is-zero-leq-zero-ℕ
    ( cofibonacci zero-ℕ)
    ( is-lower-bound-cofibonacci zero-ℕ zero-ℕ ( λ f → ex-falso (f refl)))
```

### The cofibonacci sequence is left adjoint to the Fibonacci sequence

```agda
forward-is-left-adjoint-cofibonacci :
  (m n : ℕ) → div-ℕ (cofibonacci m) n → div-ℕ m (fibonacci-ℕ n)
forward-is-left-adjoint-cofibonacci zero-ℕ n H =
  tr
    ( div-ℕ zero-ℕ)
    ( ap
      ( fibonacci-ℕ)
      ( inv
        ( is-zero-div-zero-ℕ n
          ( tr (λ t → div-ℕ t n) is-zero-cofibonacci-zero-ℕ H))))
    ( refl-div-ℕ zero-ℕ)
forward-is-left-adjoint-cofibonacci (succ-ℕ m) zero-ℕ H =
  div-zero-ℕ (succ-ℕ m)
forward-is-left-adjoint-cofibonacci (succ-ℕ m) (succ-ℕ n) H =
  div-fibonacci-div-ℕ
    ( succ-ℕ m)
    ( cofibonacci (succ-ℕ m))
    ( succ-ℕ n)
    ( H)
    ( pr2
      ( is-multiple-of-cofibonacci-cofibonacci
        ( succ-ℕ m)
        ( is-nonzero-succ-ℕ m)))

{-
converse-is-left-adjoint-cofibonacci :
  (m n : ℕ) → div-ℕ m (fibonacci-ℕ n) → div-ℕ (cofibonacci m) n
converse-is-left-adjoint-cofibonacci m n H = {!!}

is-left-adjoint-cofibonacci :
  (m n : ℕ) → div-ℕ (cofibonacci m) n ↔ div-ℕ m (fibonacci-ℕ n)
is-left-adjoint-cofibonacci m n = {!!}
-}
```

## External links

- [A001177](https://oeis.org/A001177) in the OEIS
