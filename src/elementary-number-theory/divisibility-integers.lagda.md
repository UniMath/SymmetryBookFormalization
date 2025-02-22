# Divisibility of integers

```agda
module elementary-number-theory.divisibility-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-integers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.nonpositive-integers
open import elementary-number-theory.nonzero-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.unit-integers
open import elementary-number-theory.unit-similarity-integers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

On this page we define the
{{#concept "divisibility" Disambiguation="integers" Agda=div-ℤ WD="divisibility" WDID=Q5284415}}
relation on the [integers](elementary-number-theory.integers.md).

An integer `m` is said to **divide** an integer `n` if there exists an integer
`k` equipped with an [identification](foundation-core.identity-types.md)
`km ＝ n`. Using the
[Curry–Howard interpretation](https://en.wikipedia.org/wiki/Curry–Howard_correspondence)
of logic into type theory, we express divisibility as follows:

```text
  div-ℤ m n := Σ (k : ℤ), k *ℤ m ＝ n.
```

If `n` is a [nonzero integer](elementary-number-theory.nonzero-integers.md),
then `div-ℤ m n` is always a [proposition](foundation-core.propositions.md) in
the sense that the type `div-ℤ m n` contains at most one element.

## Definitions

### Divisibility of the integers

```agda
div-ℤ : ℤ → ℤ → UU lzero
div-ℤ d x = Σ ℤ (λ k → k *ℤ d ＝ x)

quotient-div-ℤ : (x y : ℤ) → div-ℤ x y → ℤ
quotient-div-ℤ x y H = pr1 H

eq-quotient-div-ℤ :
  (x y : ℤ) (H : div-ℤ x y) → (quotient-div-ℤ x y H) *ℤ x ＝ y
eq-quotient-div-ℤ x y H = pr2 H

eq-quotient-div-ℤ' :
  (x y : ℤ) (H : div-ℤ x y) → x *ℤ (quotient-div-ℤ x y H) ＝ y
eq-quotient-div-ℤ' x y H =
  commutative-mul-ℤ x (quotient-div-ℤ x y H) ∙ eq-quotient-div-ℤ x y H

div-quotient-div-ℤ :
  (d x : ℤ) (H : div-ℤ d x) → div-ℤ (quotient-div-ℤ d x H) x
pr1 (div-quotient-div-ℤ d x (u , p)) = d
pr2 (div-quotient-div-ℤ d x (u , p)) = commutative-mul-ℤ d u ∙ p

concatenate-eq-div-ℤ :
  {x y z : ℤ} → x ＝ y → div-ℤ y z → div-ℤ x z
concatenate-eq-div-ℤ refl p = p

concatenate-div-eq-ℤ :
  {x y z : ℤ} → div-ℤ x y → y ＝ z → div-ℤ x z
concatenate-div-eq-ℤ p refl = p

concatenate-eq-div-eq-ℤ :
  {x y z w : ℤ} → x ＝ y → div-ℤ y z → z ＝ w → div-ℤ x w
concatenate-eq-div-eq-ℤ refl p refl = p
```

## Properties

### A natural number `m` divides a natural number `n` if and only if `m` divides `n` as integers

```agda
div-int-div-ℕ :
  {m n : ℕ} → div-ℕ m n → div-ℤ (int-ℕ m) (int-ℕ n)
pr1 (div-int-div-ℕ {m} {n} (pair d p)) = int-ℕ d
pr2 (div-int-div-ℕ {m} {n} (pair d p)) = mul-int-ℕ d m ∙ ap int-ℕ p

div-div-int-ℕ :
  {m n : ℕ} → div-ℤ (int-ℕ m) (int-ℕ n) → div-ℕ m n
div-div-int-ℕ {zero-ℕ} {n} (pair d p) =
  div-eq-ℕ zero-ℕ n
    ( inv (is-injective-int-ℕ (inv p ∙ right-zero-law-mul-ℤ d)))
pr1 (div-div-int-ℕ {succ-ℕ m} {n} (pair d p)) = abs-ℤ d
pr2 (div-div-int-ℕ {succ-ℕ m} {n} (pair d p)) =
  is-injective-int-ℕ
    ( ( inv (mul-int-ℕ (abs-ℤ d) (succ-ℕ m))) ∙
      ( ( ap
          ( _*ℤ (inr (inr m)))
          { int-abs-ℤ d}
          { d}
          ( int-abs-is-nonnegative-ℤ d
            ( is-nonnegative-left-factor-mul-ℤ
              { d}
              { inr (inr m)}
              ( is-nonnegative-eq-ℤ (inv p) (is-nonnegative-int-ℕ n))
              ( star)))) ∙
        ( p)))
```

### Divisibility by a nonzero integer is a property

```agda
is-prop-div-ℤ : (d x : ℤ) → is-nonzero-ℤ d → is-prop (div-ℤ d x)
is-prop-div-ℤ d x f = is-prop-map-is-emb (is-emb-right-mul-ℤ d f) x
```

### The divisibility relation is a preorder

Note that the divisibility relation on the integers is not antisymmetric.

```agda
refl-div-ℤ : is-reflexive div-ℤ
pr1 (refl-div-ℤ x) = one-ℤ
pr2 (refl-div-ℤ x) = left-unit-law-mul-ℤ x

transitive-div-ℤ : is-transitive div-ℤ
pr1 (transitive-div-ℤ x y z (pair e q) (pair d p)) = e *ℤ d
pr2 (transitive-div-ℤ x y z (pair e q) (pair d p)) =
  ( associative-mul-ℤ e d x) ∙
    ( ( ap (e *ℤ_) p) ∙
      ( q))
```

### Every integer is divisible by `1`

```agda
div-one-ℤ : (x : ℤ) → div-ℤ one-ℤ x
pr1 (div-one-ℤ x) = x
pr2 (div-one-ℤ x) = right-unit-law-mul-ℤ x
```

### Every integer divides `0`

```agda
div-zero-ℤ : (x : ℤ) → div-ℤ x zero-ℤ
pr1 (div-zero-ℤ x) = zero-ℤ
pr2 (div-zero-ℤ x) = left-zero-law-mul-ℤ x
```

### Every integer that is divisible by `0` is `0`

```agda
is-zero-div-zero-ℤ :
  (x : ℤ) → div-ℤ zero-ℤ x → is-zero-ℤ x
is-zero-div-zero-ℤ x (pair d p) = inv p ∙ right-zero-law-mul-ℤ d
```

### A unit integer divides every integer

```agda
div-is-unit-ℤ :
  (x y : ℤ) → is-unit-ℤ x → div-ℤ x y
pr1 (div-is-unit-ℤ x y (d , p , q)) = y *ℤ d
pr2 (div-is-unit-ℤ x y (d , p , q)) =
  associative-mul-ℤ y d x ∙ (ap (y *ℤ_) q ∙ right-unit-law-mul-ℤ y)
```

### An integer is a unit if and only if it divides $1$

```agda
div-one-is-unit-ℤ : (x : ℤ) → is-unit-ℤ x → div-ℤ x one-ℤ
div-one-is-unit-ℤ x (d , p , q) = (d , q)

is-unit-div-one-ℤ : (x : ℤ) → div-ℤ x one-ℤ → is-unit-ℤ x
is-unit-div-one-ℤ x (d , p) = (d , commutative-mul-ℤ x d ∙ p , p)
```

### The quotient of `x` by one is `x`

```agda
eq-quotient-div-is-one-ℤ :
  (k x : ℤ) → is-one-ℤ k → (H : div-ℤ k x) → quotient-div-ℤ k x H ＝ x
eq-quotient-div-is-one-ℤ .one-ℤ x refl H =
  ap
    ( quotient-div-ℤ one-ℤ x)
    ( inv
      ( eq-is-prop'
        ( is-prop-div-ℤ one-ℤ x (λ ()))
        ( div-one-ℤ x)
        ( H)))
```

### If `k` divides `x` and `k` is `0` then `x` is `0`

```agda
is-zero-is-zero-div-ℤ : (x k : ℤ) → div-ℤ k x → is-zero-ℤ k → is-zero-ℤ x
is-zero-is-zero-div-ℤ x .zero-ℤ k-div-x refl = is-zero-div-zero-ℤ x k-div-x
```

### If `x` divides `y` then `x` divides any multiple of `y`

```agda
div-mul-ℤ :
  (k x y : ℤ) → div-ℤ x y → div-ℤ x (k *ℤ y)
div-mul-ℤ k x y = transitive-div-ℤ x y (k *ℤ y) (k , refl)
```

### If `x` divides `y` then it divides `-y`

```agda
div-neg-ℤ : (x y : ℤ) → div-ℤ x y → div-ℤ x (neg-ℤ y)
pr1 (div-neg-ℤ x y (pair d p)) = neg-ℤ d
pr2 (div-neg-ℤ x y (pair d p)) = left-negative-law-mul-ℤ d x ∙ ap neg-ℤ p
```

### If `x` divides `y` then `-x` divides `y`

```agda
neg-div-ℤ : (x y : ℤ) → div-ℤ x y → div-ℤ (neg-ℤ x) y
pr1 (neg-div-ℤ x y (pair d p)) = neg-ℤ d
pr2 (neg-div-ℤ x y (pair d p)) =
  equational-reasoning
    (neg-ℤ d) *ℤ (neg-ℤ x)
    ＝ neg-ℤ (d *ℤ (neg-ℤ x))
      by left-negative-law-mul-ℤ d (neg-ℤ x)
    ＝ neg-ℤ (neg-ℤ (d *ℤ x))
      by ap neg-ℤ (right-negative-law-mul-ℤ d x)
    ＝ (d *ℤ x)
      by neg-neg-ℤ (d *ℤ x)
    ＝ y
      by p
```

### If `x` divides two out of the three integers `y`, `z`, and `y + z`, then it divides the third

```agda
div-add-ℤ : (x y z : ℤ) → div-ℤ x y → div-ℤ x z → div-ℤ x (y +ℤ z)
pr1 (div-add-ℤ x y z (pair d p) (pair e q)) = d +ℤ e
pr2 (div-add-ℤ x y z (pair d p) (pair e q)) =
  ( right-distributive-mul-add-ℤ d e x) ∙
  ( ap-add-ℤ p q)

div-right-summand-ℤ :
  (x y z : ℤ) → div-ℤ x y → div-ℤ x (y +ℤ z) → div-ℤ x z
div-right-summand-ℤ x y z H K =
  tr
    ( div-ℤ x)
    ( is-retraction-left-add-neg-ℤ y z)
    ( div-add-ℤ x
      ( neg-ℤ y)
      ( y +ℤ z)
      ( div-neg-ℤ x y H)
      ( K))

div-left-summand-ℤ :
  (x y z : ℤ) → div-ℤ x z → div-ℤ x (y +ℤ z) → div-ℤ x y
div-left-summand-ℤ x y z H K =
  tr
    ( div-ℤ x)
    ( is-retraction-right-add-neg-ℤ z y)
    ( div-add-ℤ x
      ( y +ℤ z)
      ( neg-ℤ z)
      ( K)
      ( div-neg-ℤ x z H))
```

### Multiplication preserves divisibility

```agda
preserves-div-mul-ℤ :
  (k l x y : ℤ) → div-ℤ k x → div-ℤ l y → div-ℤ (k *ℤ l) (x *ℤ y)
pr1 (preserves-div-mul-ℤ k l x y (q , α) (p , β)) = q *ℤ p
pr2 (preserves-div-mul-ℤ k l x y (q , α) (p , β)) =
  interchange-law-mul-mul-ℤ q p k l ∙ ap-mul-ℤ α β

preserves-div-left-mul-ℤ :
  (k x y : ℤ) → div-ℤ x y → div-ℤ (k *ℤ x) (k *ℤ y)
preserves-div-left-mul-ℤ k x y H =
  preserves-div-mul-ℤ k x k y (refl-div-ℤ k) H

preserves-div-right-mul-ℤ :
  (k x y : ℤ) → div-ℤ x y → div-ℤ (x *ℤ k) (y *ℤ k)
preserves-div-right-mul-ℤ k x y H =
  preserves-div-mul-ℤ x k y k H (refl-div-ℤ k)
```

### Multiplication by a nonzero number reflects divisibility

```agda
reflects-div-mul-ℤ :
  (k x y : ℤ) → is-nonzero-ℤ k → div-ℤ (k *ℤ x) (k *ℤ y) → div-ℤ x y
pr1 (reflects-div-mul-ℤ k x y H (pair q p)) = q
pr2 (reflects-div-mul-ℤ k x y H (pair q p)) =
  is-injective-left-mul-ℤ k H
    ( ( inv (associative-mul-ℤ k q x)) ∙
      ( ( ap (_*ℤ x) (commutative-mul-ℤ k q)) ∙
        ( ( associative-mul-ℤ q k x) ∙
          ( p))))
```

### If a nonzero number `d` divides `y`, then `dx` divides `y` if and only if `x` divides the quotient `y/d`

```agda
div-quotient-div-div-ℤ :
  (x y d : ℤ) (H : div-ℤ d y) → is-nonzero-ℤ d →
  div-ℤ (d *ℤ x) y → div-ℤ x (quotient-div-ℤ d y H)
div-quotient-div-div-ℤ x y d H f K =
  reflects-div-mul-ℤ d x
    ( quotient-div-ℤ d y H)
    ( f)
    ( tr (div-ℤ (d *ℤ x)) (inv (eq-quotient-div-ℤ' d y H)) K)

div-div-quotient-div-ℤ :
  (x y d : ℤ) (H : div-ℤ d y) →
  div-ℤ x (quotient-div-ℤ d y H) → div-ℤ (d *ℤ x) y
div-div-quotient-div-ℤ x y d H K =
  tr
    ( div-ℤ (d *ℤ x))
    ( eq-quotient-div-ℤ' d y H)
    ( preserves-div-left-mul-ℤ d x (quotient-div-ℤ d y H) K)
```

### `sim-unit-ℤ x y` holds if and only if `x|y` and `y|x`

```agda
antisymmetric-div-ℤ :
  (x y : ℤ) → div-ℤ x y → div-ℤ y x → sim-unit-ℤ x y
antisymmetric-div-ℤ x y (pair d p) (pair e q) H =
  f (is-decidable-is-zero-ℤ x)
  where
  f : is-decidable (is-zero-ℤ x) → presim-unit-ℤ x y
  f (inl refl) = presim-unit-eq-ℤ (inv (right-zero-law-mul-ℤ d) ∙ p)
  pr1 (pr1 (f (inr g))) = d
  pr2 (pr1 (f (inr g))) =
    is-unit-div-one-ℤ d
      ( e ,
        is-injective-left-mul-ℤ x g
          ( ( commutative-mul-ℤ x (e *ℤ d)) ∙
            ( ( associative-mul-ℤ e d x) ∙
              ( ( ap (e *ℤ_) p) ∙
                ( q ∙ inv (right-unit-law-mul-ℤ x))))))
  pr2 (f (inr g)) = p
```

### If `x ~ x'` and `y ~ y'` are unit similar, then `x | y` holds if and only if `x' | y'` holds

```agda
div-presim-unit-ℤ :
  {x y x' y' : ℤ} → presim-unit-ℤ x x' → presim-unit-ℤ y y' →
  div-ℤ x y → div-ℤ x' y'
pr1 (div-presim-unit-ℤ {x} {y} {x'} {y'} (pair u q) (pair v r) (pair d p)) =
  (int-unit-ℤ v *ℤ d) *ℤ (int-unit-ℤ u)
pr2 (div-presim-unit-ℤ {x} {y} {x'} {y'} (pair u q) (pair v r) (pair d p)) =
  ( ap ((((int-unit-ℤ v) *ℤ d) *ℤ (int-unit-ℤ u)) *ℤ_) (inv q)) ∙
  ( ( associative-mul-ℤ
      ( int-unit-ℤ v *ℤ d)
      ( int-unit-ℤ u)
      ( int-unit-ℤ u *ℤ x)) ∙
    ( ( ap
        ( (int-unit-ℤ v *ℤ d) *ℤ_)
        ( ( inv (associative-mul-ℤ (int-unit-ℤ u) (int-unit-ℤ u) x)) ∙
          ( ap (_*ℤ x) (idempotent-is-unit-ℤ (is-unit-unit-ℤ u))))) ∙
      ( ( associative-mul-ℤ (int-unit-ℤ v) d x) ∙
        ( ( ap (int-unit-ℤ v *ℤ_) p) ∙
          ( r)))))

div-sim-unit-ℤ :
  {x y x' y' : ℤ} → sim-unit-ℤ x x' → sim-unit-ℤ y y' →
  div-ℤ x y → div-ℤ x' y'
div-sim-unit-ℤ {x} {y} {x'} {y'} H K =
  div-presim-unit-ℤ (presim-unit-sim-unit-ℤ H) (presim-unit-sim-unit-ℤ K)
```

### An integer `x` divides an integer `y` if and only if its absolute value `|x|` divides `y`

```agda
div-int-abs-divisor-div-ℤ :
  {x y : ℤ} → div-ℤ x y → div-ℤ (int-abs-ℤ x) y
div-int-abs-divisor-div-ℤ {x} {y} =
  div-sim-unit-ℤ
    ( symmetric-sim-unit-ℤ (int-abs-ℤ x) x (sim-unit-abs-ℤ x))
    ( refl-sim-unit-ℤ y)

div-div-int-abs-divisor-ℤ :
  {x y : ℤ} → div-ℤ (int-abs-ℤ x) y → div-ℤ x y
div-div-int-abs-divisor-ℤ {x} {y} =
  div-sim-unit-ℤ (sim-unit-abs-ℤ x) (refl-sim-unit-ℤ y)
```

### An integer `a` divides an integer `b` if and only if the natural number `|a|` divides the natural number `|b|`

```agda
div-abs-div-ℤ :
  (a b : ℤ) → div-ℤ a b → div-ℕ (abs-ℤ a) (abs-ℤ b)
div-abs-div-ℤ a b H =
  div-div-int-ℕ
    ( div-sim-unit-ℤ
      ( symmetric-sim-unit-ℤ _ _ (sim-unit-abs-ℤ a))
      ( symmetric-sim-unit-ℤ _ _ (sim-unit-abs-ℤ b))
      ( H))

div-div-abs-ℤ :
  (a b : ℤ) → div-ℕ (abs-ℤ a) (abs-ℤ b) → div-ℤ a b
div-div-abs-ℤ a b H =
  div-sim-unit-ℤ
    ( sim-unit-abs-ℤ a)
    ( sim-unit-abs-ℤ b)
    ( div-int-div-ℕ H)
```

### Divisibility on the integers is decidable

```agda
is-decidable-div-ℤ :
  (a b : ℤ) → is-decidable (div-ℤ a b)
is-decidable-div-ℤ a b =
  is-decidable-iff
    ( div-div-abs-ℤ a b)
    ( div-abs-div-ℤ a b)
    ( is-decidable-div-ℕ _ _)
```
