# Euclidean division on the natural numbers

```agda
module elementary-number-theory.euclidean-division-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

{{#concept "Euclidean division" Agda=euclidean-division-ℕ}} is a binary
operation on the [natural numbers](elementary-number-theory.natural-numbers.md)
that returns the division with remainder. In other words, the Euclidean division
of `n` by `d` gives the unique pair of natural numbers `q` and `r < d` such that
the identification `qd + r ＝ n` holds.

There are several ways of specifying Euclidean division. Since we have already
defined the
[congruence relations](elementary-number-theory.congruence-natural-numbers.md)
independently, we can define the Euclidean division of a natural number `n` by
`d` as the data consisting of:

- A natural number `r`, called the
  {{#concept "remainder" Disambiguation="Euclidean division of natural numbers" Agda=remainder-euclidean-division-ℕ}}
- A proof that `r` is congruent to `n` modulo `d`
- A proof that if `d ≠ 0`, then `r < d`.

Given that `r` is congruent to `n` modulo `d` we obtain a number `q` such that
`d * q = dist-ℕ r x`, where `dist-ℕ` is the
[distance function](elementary-number-theory.distance-natural-numbers.md). This
number `q` is the
{{#concept "quotient" Disambiguation="Euclidean divistion of naturalnumbers" Agda=quotient-euclidean-division-ℕ}}
after Euclidean division.

Note that if `d ＝ 0`, then the unique natural number that is congruent to `n`
modulo `d` is the number `n` itself. The type of this data is therefore always
[contractible](foundation-core.contractible-types.md), even in the case
`d ＝ 0`.

## Definitions

### Euclidean division via modular arithmetic

```agda
euclidean-division-ℕ :
  (k x : ℕ) → Σ ℕ (λ r → (x ≡ r mod-ℕ k) × (is-nonzero-ℕ k → le-ℕ r k))
pr1 (euclidean-division-ℕ zero-ℕ x) = x
pr1 (pr2 (euclidean-division-ℕ zero-ℕ x)) = refl-cong-ℕ zero-ℕ x
pr2 (pr2 (euclidean-division-ℕ zero-ℕ x)) f = ex-falso (f refl)
pr1 (euclidean-division-ℕ (succ-ℕ k) x) = nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)
pr1 (pr2 (euclidean-division-ℕ (succ-ℕ k) x)) =
  symmetric-cong-ℕ
    ( succ-ℕ k)
    ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k x))
    ( x)
    ( cong-nat-mod-succ-ℕ k x)
pr2 (pr2 (euclidean-division-ℕ (succ-ℕ k) x)) f =
  strict-upper-bound-nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)

remainder-euclidean-division-ℕ : ℕ → ℕ → ℕ
remainder-euclidean-division-ℕ k x =
  pr1 (euclidean-division-ℕ k x)

cong-euclidean-division-ℕ :
  (k x : ℕ) → x ≡ remainder-euclidean-division-ℕ k x mod-ℕ k
cong-euclidean-division-ℕ k x =
  pr1 (pr2 (euclidean-division-ℕ k x))

strict-upper-bound-remainder-euclidean-division-ℕ :
  (k x : ℕ) → is-nonzero-ℕ k → le-ℕ (remainder-euclidean-division-ℕ k x) k
strict-upper-bound-remainder-euclidean-division-ℕ k x =
  pr2 (pr2 (euclidean-division-ℕ k x))

quotient-euclidean-division-ℕ : ℕ → ℕ → ℕ
quotient-euclidean-division-ℕ k x =
  pr1 (cong-euclidean-division-ℕ k x)

eq-quotient-euclidean-division-ℕ :
  (k x : ℕ) →
  ( quotient-euclidean-division-ℕ k x *ℕ k) ＝
  ( dist-ℕ x (remainder-euclidean-division-ℕ k x))
eq-quotient-euclidean-division-ℕ k x =
  pr2 (cong-euclidean-division-ℕ k x)

eq-euclidean-division-ℕ :
  (k x : ℕ) →
  quotient-euclidean-division-ℕ k x *ℕ k +ℕ
  remainder-euclidean-division-ℕ k x ＝
  x
eq-euclidean-division-ℕ zero-ℕ x =
  ( inv
    ( ap
      ( _+ℕ x)
      ( right-zero-law-mul-ℕ (quotient-euclidean-division-ℕ zero-ℕ x)))) ∙
  ( left-unit-law-add-ℕ x)
eq-euclidean-division-ℕ (succ-ℕ k) x =
  ( ap
    ( _+ℕ remainder-euclidean-division-ℕ (succ-ℕ k) x)
    ( ( pr2 (cong-euclidean-division-ℕ (succ-ℕ k) x)) ∙
      ( symmetric-dist-ℕ x
        ( remainder-euclidean-division-ℕ (succ-ℕ k) x)))) ∙
  ( is-difference-dist-ℕ' (remainder-euclidean-division-ℕ (succ-ℕ k) x) x
    ( leq-nat-mod-succ-ℕ k x))
```

### Euclidean division via an array of natural numbers

The following definition produces for each `k : ℕ` a sequence of sequences as
follows:

```text
    This is column k
      ↓
  0,…,0,0,0,0,0,0,0,…  -- The sequence at row 0 is the constant sequence
  1,0,…,0,0,0,0,0,0,…  -- We append 1's at the start
      ⋮
  1,…,1,0,…,0,0,0,0,…  -- This is row k+1
  2,1,…,1,0,0,0,0,0,…  -- After k+1 steps we append 2's at the start
      ⋮
  2,…,2,1,…,1,0,…,0,…  -- This is row 2(k+1)
  3,2,…,2,1,…,1,0,0,…  -- After another k+1 steps we append 3's at the start
      ⋮
```

This produces an array of natural numbers. We find the quotient of the euclidean
division of `n` by `k+1` in the `k`-th column of the `n`-th row of this array.
We will arbitrarily set the quotient of the euclidean division of `n` by `0` to
`0` in this definition.

```agda
array-quotient-euclidean-division-ℕ : ℕ → ℕ → ℕ → ℕ
array-quotient-euclidean-division-ℕ k zero-ℕ m = zero-ℕ
array-quotient-euclidean-division-ℕ k (succ-ℕ n) zero-ℕ =
  succ-ℕ (array-quotient-euclidean-division-ℕ k n k)
array-quotient-euclidean-division-ℕ k (succ-ℕ n) (succ-ℕ m) =
  array-quotient-euclidean-division-ℕ k n m

quotient-euclidean-division-ℕ' : ℕ → ℕ → ℕ
quotient-euclidean-division-ℕ' zero-ℕ n = zero-ℕ
quotient-euclidean-division-ℕ' (succ-ℕ k) n =
  array-quotient-euclidean-division-ℕ k n k
```

## Properties

### If `d` divides a number `n`, then its quotient by euclidean division is its quotient by division

Suppose `q * d ＝ n`. Then the congruence class `r` of `n` modulo `d` is `0`, so
the distance between `r` and `n` is `n`.

```text
compute-euclidean-division-div-ℕ :
  (d n : ℕ) (H : div-ℕ d n) →
  quotient-euclidean-division-ℕ d n ＝ quotient-div-ℕ d n H
compute-euclidean-division-div-ℕ d n H =
  {!eq-quotient-div-eq-is-nonzero-divisor-ℕ!}
```
