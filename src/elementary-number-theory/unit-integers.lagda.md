# Unit integers

```agda
module elementary-number-theory.unit-integers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.groups-of-units-commutative-rings
open import commutative-algebra.invertible-elements-commutative-rings

open import elementary-number-theory.equality-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.ring-of-integers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.negation
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

An [integer](elementary-number-theory.integers.md) $a$ is said to be a
{{#concept "unit" Disambiguation="integer" Agda=unit-ℤ  WD="unit" WDID=Q118084}}
if it [divides](elementary-number-theory.divisibility-integers.md) the integer
$1$, i.e., if there exists an integer $b$ such that

$$
ab=1.
$$

Note that the predicate of being a unit is expressed without explicitly
referring to divisibility of the integers in order to avoid cyclic dependencies
in the library. Some properties of divisibility involving unit integers are
studied in
[`elementary-number-theory.divisibility-integers`](elementary-number-theory.divisibility-integers.md`).

## Definitions

### Unit integers

```agda
is-unit-ℤ : ℤ → UU lzero
is-unit-ℤ = is-invertible-element-Commutative-Ring ℤ-Commutative-Ring

is-nonunit-ℤ : ℤ → UU lzero
is-nonunit-ℤ a = ¬ is-unit-ℤ a

unit-ℤ : UU lzero
unit-ℤ = type-group-of-units-Commutative-Ring ℤ-Commutative-Ring

int-unit-ℤ : unit-ℤ → ℤ
int-unit-ℤ = inclusion-group-of-units-Commutative-Ring ℤ-Commutative-Ring

is-unit-unit-ℤ : (x : unit-ℤ) → is-unit-ℤ (int-unit-ℤ x)
is-unit-unit-ℤ =
  is-invertible-element-inclusion-group-of-units-Commutative-Ring
    ℤ-Commutative-Ring
```

### The predicate of being $1$ or $-1$

```agda
is-one-or-neg-one-ℤ : ℤ → UU lzero
is-one-or-neg-one-ℤ x = (is-one-ℤ x) + (is-neg-one-ℤ x)
```

### The unit integer $1$

```agda
is-unit-one-ℤ : is-unit-ℤ one-ℤ
is-unit-one-ℤ = is-invertible-element-one-Commutative-Ring ℤ-Commutative-Ring

one-unit-ℤ : unit-ℤ
one-unit-ℤ = unit-group-of-units-Commutative-Ring ℤ-Commutative-Ring

is-unit-is-one-ℤ : (x : ℤ) → is-one-ℤ x → is-unit-ℤ x
is-unit-is-one-ℤ x p =
  is-invertible-element-is-one-Commutative-Ring ℤ-Commutative-Ring x (inv p)
```

### The unit integer $-1$

```agda
is-unit-neg-one-ℤ : is-unit-ℤ neg-one-ℤ
is-unit-neg-one-ℤ = (neg-one-ℤ , refl , refl)

neg-one-unit-ℤ : unit-ℤ
pr1 neg-one-unit-ℤ = neg-one-ℤ
pr2 neg-one-unit-ℤ = is-unit-neg-one-ℤ

is-unit-is-neg-one-ℤ :
  (x : ℤ) → is-neg-one-ℤ x → is-unit-ℤ x
is-unit-is-neg-one-ℤ .neg-one-ℤ refl = is-unit-neg-one-ℤ
```

## Properties

### The product $xy$ is a unit if and only if both $x$ and $y$ are units

```agda
is-unit-mul-ℤ :
  (x y : ℤ) → is-unit-ℤ x → is-unit-ℤ y → is-unit-ℤ (x *ℤ y)
is-unit-mul-ℤ = is-invertible-element-mul-Commutative-Ring ℤ-Commutative-Ring

mul-unit-ℤ : unit-ℤ → unit-ℤ → unit-ℤ
mul-unit-ℤ = mul-group-of-units-Commutative-Ring ℤ-Commutative-Ring

is-unit-left-factor-mul-ℤ :
  (x y : ℤ) → is-unit-ℤ (x *ℤ y) → is-unit-ℤ x
is-unit-left-factor-mul-ℤ =
  is-invertible-element-left-factor-Commutative-Ring ℤ-Commutative-Ring

is-unit-right-factor-ℤ :
  (x y : ℤ) → is-unit-ℤ (x *ℤ y) → is-unit-ℤ y
is-unit-right-factor-ℤ =
  is-invertible-element-right-factor-Commutative-Ring ℤ-Commutative-Ring
```

### An integer is a unit if and only if it is $1$ or $-1$

```agda
is-unit-is-one-or-neg-one-ℤ :
  (x : ℤ) → is-one-or-neg-one-ℤ x → is-unit-ℤ x
is-unit-is-one-or-neg-one-ℤ x (inl p) = is-unit-is-one-ℤ x p
is-unit-is-one-or-neg-one-ℤ x (inr p) = is-unit-is-neg-one-ℤ x p

is-one-or-neg-one-is-unit-ℤ :
  (x : ℤ) → is-unit-ℤ x → is-one-or-neg-one-ℤ x
is-one-or-neg-one-is-unit-ℤ (inl zero-ℕ) (d , p) = inr refl
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (inl zero-ℕ , p , q) =
  ex-falso (Eq-eq-ℤ (inv q ∙ compute-mul-ℤ neg-one-ℤ (inl (succ-ℕ x))))
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (inl (succ-ℕ d) , p , q) =
  ex-falso (Eq-eq-ℤ (inv q ∙ compute-mul-ℤ (inl (succ-ℕ d)) (inl (succ-ℕ x))))
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (inr (inl star) , p , q) =
  ex-falso (Eq-eq-ℤ (inv q ∙ compute-mul-ℤ zero-ℤ (inl (succ-ℕ x))))
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (inr (inr zero-ℕ) , p , q) =
  ex-falso (Eq-eq-ℤ (inv q ∙ compute-mul-ℤ one-ℤ (inl (succ-ℕ x))))
is-one-or-neg-one-is-unit-ℤ (inl (succ-ℕ x)) (inr (inr (succ-ℕ d)) , p , q) =
  ex-falso
    ( Eq-eq-ℤ (inv q ∙ compute-mul-ℤ (inr (inr (succ-ℕ d))) (inl (succ-ℕ x))))
is-one-or-neg-one-is-unit-ℤ (inr (inl star)) (d , p , q) =
  ex-falso (Eq-eq-ℤ (inv (right-zero-law-mul-ℤ d) ∙ q))
is-one-or-neg-one-is-unit-ℤ (inr (inr zero-ℕ)) (d , p , q) = inl refl
is-one-or-neg-one-is-unit-ℤ (inr (inr (succ-ℕ x))) (inl zero-ℕ , p , q) =
  ex-falso (Eq-eq-ℤ (inv q ∙ compute-mul-ℤ neg-one-ℤ (inr (inr (succ-ℕ x)))))
is-one-or-neg-one-is-unit-ℤ (inr (inr (succ-ℕ x))) (inl (succ-ℕ d) , p , q) =
  ex-falso
    ( Eq-eq-ℤ (inv q ∙ compute-mul-ℤ (inl (succ-ℕ d)) (inr (inr (succ-ℕ x)))))
is-one-or-neg-one-is-unit-ℤ (inr (inr (succ-ℕ x))) (inr (inl star) , p , q) =
  ex-falso (Eq-eq-ℤ (inv q ∙ compute-mul-ℤ zero-ℤ (inr (inr (succ-ℕ x)))))
is-one-or-neg-one-is-unit-ℤ (inr (inr (succ-ℕ x))) (inr (inr zero-ℕ) , p , q) =
  ex-falso (Eq-eq-ℤ (inv q ∙ compute-mul-ℤ one-ℤ (inr (inr (succ-ℕ x)))))
is-one-or-neg-one-is-unit-ℤ
  (inr (inr (succ-ℕ x))) (inr (inr (succ-ℕ d)) , p , q) =
  ex-falso
    ( Eq-eq-ℤ
      ( inv q ∙ compute-mul-ℤ (inr (inr (succ-ℕ d))) (inr (inr (succ-ℕ x)))))
```

### Some examples of integers that aren't units

```agda
abstract
  is-nonunit-zero-ℤ : is-nonunit-ℤ zero-ℤ
  is-nonunit-zero-ℤ H
    with
    is-one-or-neg-one-is-unit-ℤ zero-ℤ H
  ... | inl ()
  ... | inr ()

abstract
  is-nonunit-two-ℤ : is-nonunit-ℤ (int-ℕ 2)
  is-nonunit-two-ℤ H
    with
    is-one-or-neg-one-is-unit-ℤ (int-ℕ 2) H
  ... | inl ()
  ... | inr ()

abstract
  is-nonunit-three-ℤ : is-nonunit-ℤ (int-ℕ 3)
  is-nonunit-three-ℤ H
    with
    is-one-or-neg-one-is-unit-ℤ (int-ℕ 3) H
  ... | inl ()
  ... | inr ()
```

### Unit integers are idempotent

```agda
idempotent-is-unit-ℤ : {x : ℤ} → is-unit-ℤ x → x *ℤ x ＝ one-ℤ
idempotent-is-unit-ℤ {x} H =
  f (is-one-or-neg-one-is-unit-ℤ x H)
  where
  f : is-one-or-neg-one-ℤ x → x *ℤ x ＝ one-ℤ
  f (inl refl) = refl
  f (inr refl) = refl

abstract
  is-one-is-unit-int-ℕ : (x : ℕ) → is-unit-ℤ (int-ℕ x) → is-one-ℕ x
  is-one-is-unit-int-ℕ x H with is-one-or-neg-one-is-unit-ℤ (int-ℕ x) H
  ... | inl p = is-injective-int-ℕ p
  ... | inr p = ex-falso (tr is-nonnegative-ℤ p (is-nonnegative-int-ℕ x))
```
