# The congruence relations on the natural numbers

```agda
module elementary-number-theory.congruence-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Two [natural numbers](elementary-number-theory.natural-numbers.md) `x` and `y`
are said to be
{{#concept "congruent" Disambiguation="natural numbers" Agda=cong-ℕ WDID=Q3773677 WD="congruence of integers"}}
modulo `k` if their
[distance](elementary-number-theory.distance-natural-numbers.md) `dist-ℕ x y` is
[divisible](elementary-number-theory.divisibility-natural-numbers.md) by `k`,
i.e., if

```text
  k | dist-ℕ x y.
```

For each natural number `k`, the congruence relation modulo `k` defines an
[equivalence relation](foundation.equivalence-relations.md). Furthermore, the
congruence relations respect
[addition](elementary-number-theory.addition-natural-numbers.md) and
[multiplication](elementary-number-theory.multiplication-natural-numbers.md).

[Quotienting](foundation.set-quotients.md) by the congruence relation leads to
[modular arithmetic](elementary-number-theory.modular-arithmetic.md). Properties
of the congruence relation with respect to the
[standard finite types](univalent-combinatorics.standard-finite-types.md) are
formalized in the file
[`modular-arithmetic-standard-finite-types`](elementary-number-theory.modular-arithmetic-standard-finite-types.md).

## Properties

### The congruence relations on the natural numbers

```agda
cong-ℕ :
  ℕ → ℕ → ℕ → UU lzero
cong-ℕ k x y = div-ℕ k (dist-ℕ x y)

_≡_mod-ℕ_ : ℕ → ℕ → ℕ → UU lzero
x ≡ y mod-ℕ k = cong-ℕ k x y
```

## Properties

### Any two natural numbers are congruent to each other modulo `1`

```agda
is-indiscrete-cong-one-ℕ :
  (x y : ℕ) → x ≡ y mod-ℕ 1
is-indiscrete-cong-one-ℕ x y = div-one-ℕ (dist-ℕ x y)
```

### Congruence of natural numbers is a reflexive relation

```agda
refl-cong-ℕ : (k : ℕ) → is-reflexive (cong-ℕ k)
pr1 (refl-cong-ℕ k x) = zero-ℕ
pr2 (refl-cong-ℕ k x) =
  (left-zero-law-mul-ℕ (succ-ℕ k)) ∙ (inv (dist-eq-ℕ x x refl))

cong-identification-ℕ :
  (k : ℕ) {x y : ℕ} → x ＝ y → x ≡ y mod-ℕ k
cong-identification-ℕ k {x} refl = refl-cong-ℕ k x
```

### Congruence of natural numbers is a symmetric relation

```agda
symmetric-cong-ℕ : (k : ℕ) → is-symmetric (cong-ℕ k)
pr1 (symmetric-cong-ℕ k x y (d , p)) = d
pr2 (symmetric-cong-ℕ k x y (d , p)) = p ∙ (symmetric-dist-ℕ x y)
```

### Congruence of natural numbers is a transitive relation

```agda
transitive-cong-ℕ : (k : ℕ) → is-transitive (cong-ℕ k)
transitive-cong-ℕ k x y z e d with is-total-dist-ℕ x y z
transitive-cong-ℕ k x y z e d | inl α =
  concatenate-div-eq-ℕ (div-add-ℕ k (dist-ℕ x y) (dist-ℕ y z) d e) α
transitive-cong-ℕ k x y z e d | inr (inl α) =
  div-right-summand-ℕ k (dist-ℕ y z) (dist-ℕ x z) e
    ( concatenate-div-eq-ℕ d (inv α))
transitive-cong-ℕ k x y z e d | inr (inr α) =
  div-left-summand-ℕ k (dist-ℕ x z) (dist-ℕ x y) d
    ( concatenate-div-eq-ℕ e (inv α))
```

### Concatenating congruence and equality

```agda
concatenate-eq-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 x4 : ℕ} →
  x1 ＝ x2 → x2 ≡ x3 mod-ℕ k → x3 ＝ x4 → x1 ≡ x4 mod-ℕ k
concatenate-eq-cong-eq-ℕ k refl H refl = H

concatenate-eq-cong-ℕ :
  (k : ℕ) {x1 x2 x3 : ℕ} →
  x1 ＝ x2 → x2 ≡ x3 mod-ℕ k → x1 ≡ x3 mod-ℕ k
concatenate-eq-cong-ℕ k refl H = H

concatenate-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 : ℕ} →
  x1 ≡ x2 mod-ℕ k → x2 ＝ x3 → x1 ≡ x3 mod-ℕ k
concatenate-cong-eq-ℕ k H refl = H

concatenate-cong-eq-cong-ℕ :
  {k x1 x2 x3 x4 : ℕ} →
  x1 ≡ x2 mod-ℕ k → x2 ＝ x3 → x3 ≡ x4 mod-ℕ k → x1 ≡ x4 mod-ℕ k
concatenate-cong-eq-cong-ℕ {k} {x} {y} {.y} {z} H refl K =
  transitive-cong-ℕ k x y z K H

concatenate-eq-cong-eq-cong-eq-ℕ :
  (k : ℕ) {x1 x2 x3 x4 x5 x6 : ℕ} →
  x1 ＝ x2 → x2 ≡ x3 mod-ℕ k → x3 ＝ x4 →
  x4 ≡ x5 mod-ℕ k → x5 ＝ x6 → x1 ≡ x6 mod-ℕ k
concatenate-eq-cong-eq-cong-eq-ℕ k
  {x} {.x} {y} {.y} {z} {.z} refl H refl K refl =
  transitive-cong-ℕ k x y z K H
```

### If the distance between two natural numbers is strictly less than `k`, then they are congruent modulo `k` if and only if they are equal

```agda
eq-cong-le-dist-ℕ :
  (k x y : ℕ) → le-ℕ (dist-ℕ x y) k → x ≡ y mod-ℕ k → x ＝ y
eq-cong-le-dist-ℕ k x y H K =
  eq-dist-ℕ x y (is-zero-div-ℕ k (dist-ℕ x y) H K)
```

### Any two numbers strictly less than `k` are congruent modulo `k` if and only if they are equal

```agda
eq-cong-le-ℕ :
  (k x y : ℕ) → le-ℕ x k → le-ℕ y k → x ≡ y mod-ℕ k → x ＝ y
eq-cong-le-ℕ k x y H K =
  eq-cong-le-dist-ℕ k x y (strict-upper-bound-dist-ℕ k x y H K)

eq-cong-nat-Fin :
  (k : ℕ) (x y : Fin k) → nat-Fin k x ≡ nat-Fin k y mod-ℕ k → x ＝ y
eq-cong-nat-Fin (succ-ℕ k) x y H =
  is-injective-nat-Fin (succ-ℕ k)
    ( eq-cong-le-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) x) (nat-Fin (succ-ℕ k) y)
      ( strict-upper-bound-nat-Fin (succ-ℕ k) x)
      ( strict-upper-bound-nat-Fin (succ-ℕ k) y)
      ( H))
```

### Any natural number is congruent to `0` modulo itself

```agda
cong-zero-ℕ :
  (k : ℕ) → k ≡ 0 mod-ℕ k
pr1 (cong-zero-ℕ k) = 1
pr2 (cong-zero-ℕ k) =
  (left-unit-law-mul-ℕ k) ∙ (inv (right-unit-law-dist-ℕ k))

cong-zero-ℕ' : (k : ℕ) → 0 ≡ k mod-ℕ k
cong-zero-ℕ' k =
  symmetric-cong-ℕ k k zero-ℕ (cong-zero-ℕ k)
```

### The inclusion of `0` from `Fin (k + 1)` into `ℕ` is congruent to `0` modulo `k + 1`

```agda
cong-is-zero-nat-zero-Fin :
  {k : ℕ} → nat-Fin (succ-ℕ k) (zero-Fin k) ≡ 0 mod-ℕ succ-ℕ k
cong-is-zero-nat-zero-Fin {k} =
  cong-identification-ℕ (succ-ℕ k) (is-zero-nat-zero-Fin {k})
```

### Any two natural numbers that are congruent modulo `0` are equal

In other words, the congruence relation modulo `0` is discrete.

```agda
is-discrete-cong-zero-ℕ :
  (x y : ℕ) → x ≡ y mod-ℕ 0 → x ＝ y
is-discrete-cong-zero-ℕ x y (k , p) =
  eq-dist-ℕ x y (inv p ∙ right-zero-law-mul-ℕ k)
```

### If `x` and `x + 1` are congruent modulo `k`, then `k ＝ 1`

```agda
is-one-cong-succ-ℕ : {k : ℕ} (x : ℕ) → x ≡ succ-ℕ x mod-ℕ k → is-one-ℕ k
is-one-cong-succ-ℕ {k} x H =
  is-one-div-one-ℕ k (tr (div-ℕ k) (is-one-dist-succ-ℕ x) H)
```

### A number is divisible by `k` if and only if it is congruent to `0` modulo `k`

```agda
div-cong-zero-ℕ :
  (k x : ℕ) → x ≡ 0 mod-ℕ k → div-ℕ k x
div-cong-zero-ℕ k x =
  tr (div-ℕ k) (right-unit-law-dist-ℕ x)

cong-zero-div-ℕ :
  (k x : ℕ) → div-ℕ k x → x ≡ 0 mod-ℕ k
cong-zero-div-ℕ k x =
  tr (div-ℕ k) (inv (right-unit-law-dist-ℕ x))
```

### Congruence is invariant under scalar multiplication

```agda
scalar-invariant-cong-ℕ :
  (k x y z : ℕ) → x ≡ y mod-ℕ k → z *ℕ x ≡ z *ℕ y mod-ℕ k
pr1 (scalar-invariant-cong-ℕ k x y z (d , p)) = z *ℕ d
pr2 (scalar-invariant-cong-ℕ k x y z (d , p)) =
  ( associative-mul-ℕ z d k) ∙
    ( ( ap (z *ℕ_) p) ∙
      ( left-distributive-mul-dist-ℕ x y z))

scalar-invariant-cong-ℕ' :
  (k x y z : ℕ) → x ≡ y mod-ℕ k → x *ℕ z ≡ y *ℕ z mod-ℕ k
scalar-invariant-cong-ℕ' k x y z H =
  concatenate-eq-cong-eq-ℕ k
    ( commutative-mul-ℕ x z)
    ( scalar-invariant-cong-ℕ k x y z H)
    ( commutative-mul-ℕ z y)
```

### Multiplication respects the congruence relation

```agda
congruence-mul-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  x ≡ x' mod-ℕ k → y ≡ y' mod-ℕ k → x *ℕ y ≡ x' *ℕ y' mod-ℕ k
congruence-mul-ℕ k {x} {y} {x'} {y'} H K =
  transitive-cong-ℕ k (x *ℕ y) (x *ℕ y') (x' *ℕ y')
    ( scalar-invariant-cong-ℕ' k x x' y' H)
    ( scalar-invariant-cong-ℕ k y y' x K)
```

### The congruence is translation invariant

```agda
translation-invariant-cong-ℕ :
  (k x y z : ℕ) → x ≡ y mod-ℕ k → z +ℕ x ≡ z +ℕ y mod-ℕ k
pr1 (translation-invariant-cong-ℕ k x y z (d , p)) = d
pr2 (translation-invariant-cong-ℕ k x y z (d , p)) =
  p ∙ inv (translation-invariant-dist-ℕ z x y)

translation-invariant-cong-ℕ' :
  (k x y z : ℕ) → x ≡ y mod-ℕ k → x +ℕ z ≡ y +ℕ z mod-ℕ k
translation-invariant-cong-ℕ' k x y z H =
  concatenate-eq-cong-eq-ℕ k
    ( commutative-add-ℕ x z)
    ( translation-invariant-cong-ℕ k x y z H)
    ( commutative-add-ℕ z y)

step-invariant-cong-ℕ :
  (k x y : ℕ) → x ≡ y mod-ℕ k → succ-ℕ x ≡ succ-ℕ y mod-ℕ k
step-invariant-cong-ℕ k x y = translation-invariant-cong-ℕ' k x y 1

reflects-cong-add-ℕ :
  {k : ℕ} (x : ℕ) {y z : ℕ} → x +ℕ y ≡ x +ℕ z mod-ℕ k → y ≡ z mod-ℕ k
pr1 (reflects-cong-add-ℕ {k} x {y} {z} (d , p)) = d
pr2 (reflects-cong-add-ℕ {k} x {y} {z} (d , p)) =
  p ∙ translation-invariant-dist-ℕ x y z

reflects-cong-left-add-ℕ :
  {k : ℕ} (x : ℕ) {y z : ℕ} → cong-ℕ k (x +ℕ z) (y +ℕ z) → cong-ℕ k x y
pr1 (reflects-cong-left-add-ℕ x (d , p)) = d
pr2 (reflects-cong-left-add-ℕ {k} x {y} {z} (d , p)) =
  p ∙ translation-invariant-dist-ℕ' z x y

reflects-cong-add-ℕ' :
  {k : ℕ} (x : ℕ) {y z : ℕ} → y +ℕ x ≡ z +ℕ x mod-ℕ k → y ≡ z mod-ℕ k
reflects-cong-add-ℕ' {k} x {y} {z} H =
  reflects-cong-add-ℕ x {y} {z}
    ( concatenate-eq-cong-eq-ℕ k
      ( commutative-add-ℕ x y)
      ( H)
      ( commutative-add-ℕ z x))
```

### The congruence relations respect addition

```agda
congruence-add-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  x ≡ x' mod-ℕ k → y ≡ y' mod-ℕ k → x +ℕ y ≡ x' +ℕ y' mod-ℕ k
congruence-add-ℕ k {x} {y} {x'} {y'} H K =
  transitive-cong-ℕ k (x +ℕ y) (x +ℕ y') (x' +ℕ y')
    ( translation-invariant-cong-ℕ' k x x' y' H)
    ( translation-invariant-cong-ℕ k y y' x K)

congruence-right-summand-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  cong-ℕ k x x' → cong-ℕ k (x +ℕ y) (x' +ℕ y') → cong-ℕ k y y'
congruence-right-summand-ℕ k {x} {y} {x'} {y'} H K =
  reflects-cong-add-ℕ x {y}
    ( transitive-cong-ℕ k
      ( x +ℕ y)
      ( x' +ℕ y')
      ( x +ℕ y')
      ( translation-invariant-cong-ℕ' k x' x y'
        ( symmetric-cong-ℕ k x x' H))
      ( K))

congruence-left-summand-ℕ :
  (k : ℕ) {x y x' y' : ℕ} →
  cong-ℕ k y y' → cong-ℕ k (x +ℕ y) (x' +ℕ y') → cong-ℕ k x x'
congruence-left-summand-ℕ k {x} {y} {x'} {y'} H K =
  congruence-right-summand-ℕ k {y} {x} {y'} {x'} H
    ( concatenate-eq-cong-ℕ k
      ( commutative-add-ℕ y x)
      ( concatenate-cong-eq-ℕ k {x1 = x +ℕ y}
        ( K)
        ( commutative-add-ℕ x' y')))
```

## See also

- [Congruence relations on the integers](elementary-number-theory.congruence-integers.md)
