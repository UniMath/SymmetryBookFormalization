# Addition on the integers

```agda
module elementary-number-theory.addition-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.interchange-law
open import foundation.sets
open import foundation.unit-type
```

</details>

## Idea

We introduce {{#concept "addition" Disambiguation="integers" Agda=add-ℤ}} on the
[integers](elementary-number-theory.integers.md) and derive its basic properties
with respect to `succ-ℤ` and `neg-ℤ`.

## Definition

```agda
add-ℤ : ℤ → ℤ → ℤ
add-ℤ (inl zero-ℕ) l = pred-ℤ l
add-ℤ (inl (succ-ℕ x)) l = pred-ℤ (add-ℤ (inl x) l)
add-ℤ (inr (inl star)) l = l
add-ℤ (inr (inr zero-ℕ)) l = succ-ℤ l
add-ℤ (inr (inr (succ-ℕ x))) l = succ-ℤ (add-ℤ (inr (inr x)) l)

add-ℤ' : ℤ → ℤ → ℤ
add-ℤ' x y = add-ℤ y x

infixl 35 _+ℤ_
_+ℤ_ = add-ℤ

ap-add-ℤ :
  {x y x' y' : ℤ} → x ＝ x' → y ＝ y' → x +ℤ y ＝ x' +ℤ y'
ap-add-ℤ p q = ap-binary add-ℤ p q
```

## Properties

### Unit laws

```agda
abstract
  left-unit-law-add-ℤ : (k : ℤ) → zero-ℤ +ℤ k ＝ k
  left-unit-law-add-ℤ k = refl

  right-unit-law-add-ℤ : (k : ℤ) → k +ℤ zero-ℤ ＝ k
  right-unit-law-add-ℤ (inl zero-ℕ) = refl
  right-unit-law-add-ℤ (inl (succ-ℕ x)) =
    ap pred-ℤ (right-unit-law-add-ℤ (inl x))
  right-unit-law-add-ℤ (inr (inl star)) = refl
  right-unit-law-add-ℤ (inr (inr zero-ℕ)) = refl
  right-unit-law-add-ℤ (inr (inr (succ-ℕ x))) =
    ap succ-ℤ (right-unit-law-add-ℤ (inr (inr x)))
```

### Left and right predecessor laws

```agda
abstract
  left-predecessor-law-add-ℤ :
    (x y : ℤ) → pred-ℤ x +ℤ y ＝ pred-ℤ (x +ℤ y)
  left-predecessor-law-add-ℤ (inl n) y = refl
  left-predecessor-law-add-ℤ (inr (inl star)) y = refl
  left-predecessor-law-add-ℤ (inr (inr zero-ℕ)) y =
    inv (is-retraction-pred-ℤ y)
  left-predecessor-law-add-ℤ (inr (inr (succ-ℕ x))) y =
    inv (is-retraction-pred-ℤ ((inr (inr x)) +ℤ y))

  right-predecessor-law-add-ℤ :
    (x y : ℤ) → x +ℤ pred-ℤ y ＝ pred-ℤ (x +ℤ y)
  right-predecessor-law-add-ℤ (inl zero-ℕ) n = refl
  right-predecessor-law-add-ℤ (inl (succ-ℕ m)) n =
    ap pred-ℤ (right-predecessor-law-add-ℤ (inl m) n)
  right-predecessor-law-add-ℤ (inr (inl star)) n = refl
  right-predecessor-law-add-ℤ (inr (inr zero-ℕ)) n =
    equational-reasoning
      succ-ℤ (pred-ℤ n)
      ＝ n
        by is-section-pred-ℤ n
      ＝ pred-ℤ (succ-ℤ n)
        by inv (is-retraction-pred-ℤ n)
  right-predecessor-law-add-ℤ (inr (inr (succ-ℕ x))) n =
    equational-reasoning
      succ-ℤ (inr (inr x) +ℤ pred-ℤ n)
      ＝ succ-ℤ (pred-ℤ (inr (inr x) +ℤ n))
        by ap succ-ℤ (right-predecessor-law-add-ℤ (inr (inr x)) n)
      ＝ inr (inr x) +ℤ n
        by is-section-pred-ℤ ((inr (inr x)) +ℤ n)
      ＝ pred-ℤ (succ-ℤ (inr (inr x) +ℤ n))
        by inv (is-retraction-pred-ℤ ((inr (inr x)) +ℤ n))
```

### Left and right successor laws

```agda
abstract
  left-successor-law-add-ℤ :
    (x y : ℤ) → succ-ℤ x +ℤ y ＝ succ-ℤ (x +ℤ y)
  left-successor-law-add-ℤ (inl zero-ℕ) y =
    inv (is-section-pred-ℤ y)
  left-successor-law-add-ℤ (inl (succ-ℕ x)) y =
    equational-reasoning
      inl x +ℤ y
      ＝ succ-ℤ (pred-ℤ (inl x +ℤ y))
        by inv (is-section-pred-ℤ ((inl x) +ℤ y))
      ＝ succ-ℤ (pred-ℤ (inl x) +ℤ y)
        by ap succ-ℤ (inv (left-predecessor-law-add-ℤ (inl x) y))
  left-successor-law-add-ℤ (inr (inl star)) y = refl
  left-successor-law-add-ℤ (inr (inr x)) y = refl

  right-successor-law-add-ℤ :
    (x y : ℤ) → x +ℤ succ-ℤ y ＝ succ-ℤ (x +ℤ y)
  right-successor-law-add-ℤ (inl zero-ℕ) y =
    equational-reasoning
      pred-ℤ (succ-ℤ y)
      ＝ y
        by is-retraction-pred-ℤ y
      ＝ succ-ℤ (pred-ℤ y)
        by inv (is-section-pred-ℤ y)
  right-successor-law-add-ℤ (inl (succ-ℕ x)) y =
    equational-reasoning
      pred-ℤ (inl x +ℤ succ-ℤ y)
      ＝ pred-ℤ (succ-ℤ (inl x +ℤ y))
        by ap pred-ℤ (right-successor-law-add-ℤ (inl x) y)
      ＝ inl x +ℤ y
        by is-retraction-pred-ℤ ((inl x) +ℤ y)
      ＝ succ-ℤ (pred-ℤ (inl x +ℤ y))
        by inv (is-section-pred-ℤ ((inl x) +ℤ y))
  right-successor-law-add-ℤ (inr (inl star)) y = refl
  right-successor-law-add-ℤ (inr (inr zero-ℕ)) y = refl
  right-successor-law-add-ℤ (inr (inr (succ-ℕ x))) y =
    ap succ-ℤ (right-successor-law-add-ℤ (inr (inr x)) y)
```

### The successor of an integer is that integer plus one

```agda
abstract
  is-right-add-one-succ-ℤ : (x : ℤ) → succ-ℤ x ＝ x +ℤ one-ℤ
  is-right-add-one-succ-ℤ x =
    equational-reasoning
      succ-ℤ x
      ＝ succ-ℤ (x +ℤ zero-ℤ)
        by inv (ap succ-ℤ (right-unit-law-add-ℤ x))
      ＝ x +ℤ one-ℤ
        by inv (right-successor-law-add-ℤ x zero-ℤ)

  is-left-add-one-succ-ℤ : (x : ℤ) → succ-ℤ x ＝ one-ℤ +ℤ x
  is-left-add-one-succ-ℤ x = inv (left-successor-law-add-ℤ zero-ℤ x)

  left-add-one-ℤ : (x : ℤ) → one-ℤ +ℤ x ＝ succ-ℤ x
  left-add-one-ℤ x = refl

  right-add-one-ℤ : (x : ℤ) → x +ℤ one-ℤ ＝ succ-ℤ x
  right-add-one-ℤ x = inv (is-right-add-one-succ-ℤ x)
```

### The predecessor of an integer is that integer minus one

```agda
  is-left-add-neg-one-pred-ℤ : (x : ℤ) → pred-ℤ x ＝ neg-one-ℤ +ℤ x
  is-left-add-neg-one-pred-ℤ x =
    inv (left-predecessor-law-add-ℤ zero-ℤ x)

  is-right-add-neg-one-pred-ℤ : (x : ℤ) → pred-ℤ x ＝ x +ℤ neg-one-ℤ
  is-right-add-neg-one-pred-ℤ x =
    equational-reasoning
      pred-ℤ x
      ＝ pred-ℤ (x +ℤ zero-ℤ)
        by inv (ap pred-ℤ (right-unit-law-add-ℤ x))
      ＝ x +ℤ neg-one-ℤ
        by inv (right-predecessor-law-add-ℤ x zero-ℤ)

  left-add-neg-one-ℤ : (x : ℤ) → neg-one-ℤ +ℤ x ＝ pred-ℤ x
  left-add-neg-one-ℤ x = refl

  right-add-neg-one-ℤ : (x : ℤ) → x +ℤ neg-one-ℤ ＝ pred-ℤ x
  right-add-neg-one-ℤ x = inv (is-right-add-neg-one-pred-ℤ x)
```

### Addition is associative

```agda
abstract
  associative-add-ℤ :
    (x y z : ℤ) → ((x +ℤ y) +ℤ z) ＝ (x +ℤ (y +ℤ z))
  associative-add-ℤ (inl zero-ℕ) y z =
    equational-reasoning
      (neg-one-ℤ +ℤ y) +ℤ z
      ＝ (pred-ℤ (zero-ℤ +ℤ y)) +ℤ z
        by ap (_+ℤ z) (left-predecessor-law-add-ℤ zero-ℤ y)
      ＝ pred-ℤ (y +ℤ z)
        by left-predecessor-law-add-ℤ y z
      ＝ neg-one-ℤ +ℤ (y +ℤ z)
        by inv (left-predecessor-law-add-ℤ zero-ℤ (y +ℤ z))
  associative-add-ℤ (inl (succ-ℕ x)) y z =
    equational-reasoning
      (pred-ℤ (inl x) +ℤ y) +ℤ z
      ＝ pred-ℤ (inl x +ℤ y) +ℤ z
        by ap (_+ℤ z) (left-predecessor-law-add-ℤ (inl x) y)
      ＝ pred-ℤ ((inl x +ℤ y) +ℤ z)
        by left-predecessor-law-add-ℤ ((inl x) +ℤ y) z
      ＝ pred-ℤ (inl x +ℤ (y +ℤ z))
        by ap pred-ℤ (associative-add-ℤ (inl x) y z)
      ＝ pred-ℤ (inl x) +ℤ (y +ℤ z)
        by inv (left-predecessor-law-add-ℤ (inl x) (y +ℤ z))
  associative-add-ℤ (inr (inl star)) y z =
    refl
  associative-add-ℤ (inr (inr zero-ℕ)) y z =
    equational-reasoning
      (one-ℤ +ℤ y) +ℤ z
      ＝ succ-ℤ (zero-ℤ +ℤ y) +ℤ z
        by ap (_+ℤ z) (left-successor-law-add-ℤ zero-ℤ y)
      ＝ succ-ℤ (y +ℤ z)
        by left-successor-law-add-ℤ y z
      ＝ one-ℤ +ℤ (y +ℤ z)
        by inv (left-successor-law-add-ℤ zero-ℤ (y +ℤ z))
  associative-add-ℤ (inr (inr (succ-ℕ x))) y z =
    equational-reasoning
      (succ-ℤ (inr (inr x)) +ℤ y) +ℤ z
      ＝ succ-ℤ (inr (inr x) +ℤ y) +ℤ z
        by ap (_+ℤ z) (left-successor-law-add-ℤ (inr (inr x)) y)
      ＝ succ-ℤ ((inr (inr x) +ℤ y) +ℤ z)
        by left-successor-law-add-ℤ ((inr (inr x)) +ℤ y) z
      ＝ succ-ℤ (inr (inr x) +ℤ (y +ℤ z))
        by ap succ-ℤ (associative-add-ℤ (inr (inr x)) y z)
      ＝ succ-ℤ (inr (inr x)) +ℤ (y +ℤ z)
        by inv (left-successor-law-add-ℤ (inr (inr x)) (y +ℤ z))
```

### Addition is commutative

```agda
abstract
  commutative-add-ℤ : (x y : ℤ) → x +ℤ y ＝ y +ℤ x
  commutative-add-ℤ (inl zero-ℕ) y =
    equational-reasoning
      neg-one-ℤ +ℤ y
      ＝ pred-ℤ (zero-ℤ +ℤ y)
        by left-predecessor-law-add-ℤ zero-ℤ y
      ＝ pred-ℤ (y +ℤ zero-ℤ)
        by inv (ap pred-ℤ (right-unit-law-add-ℤ y))
      ＝ y +ℤ neg-one-ℤ
        by inv (right-predecessor-law-add-ℤ y zero-ℤ)
  commutative-add-ℤ (inl (succ-ℕ x)) y =
    equational-reasoning
      (inl (succ-ℕ x)) +ℤ y
      ＝ pred-ℤ (y +ℤ (inl x))
        by ap pred-ℤ (commutative-add-ℤ (inl x) y)
      ＝ y +ℤ (inl (succ-ℕ x))
        by inv (right-predecessor-law-add-ℤ y (inl x))
  commutative-add-ℤ (inr (inl star)) y =
    inv (right-unit-law-add-ℤ y)
  commutative-add-ℤ (inr (inr zero-ℕ)) y =
    equational-reasoning
      succ-ℤ y
      ＝ succ-ℤ (y +ℤ zero-ℤ)
        by inv (ap succ-ℤ (right-unit-law-add-ℤ y))
      ＝ y +ℤ one-ℤ
        by inv (right-successor-law-add-ℤ y zero-ℤ)
  commutative-add-ℤ (inr (inr (succ-ℕ x))) y =
    equational-reasoning
      succ-ℤ ((inr (inr x)) +ℤ y)
      ＝ succ-ℤ (y +ℤ (inr (inr x)))
        by ap succ-ℤ (commutative-add-ℤ (inr (inr x)) y)
      ＝ y +ℤ (succ-ℤ (inr (inr x)))
        by inv (right-successor-law-add-ℤ y (inr (inr x)))
```

### The inverse laws for addition and negatives

```agda
abstract
  left-inverse-law-add-ℤ :
    (x : ℤ) → neg-ℤ x +ℤ x ＝ zero-ℤ
  left-inverse-law-add-ℤ (inl zero-ℕ) = refl
  left-inverse-law-add-ℤ (inl (succ-ℕ x)) =
    equational-reasoning
      succ-ℤ (inr (inr x) +ℤ pred-ℤ (inl x))
      ＝ succ-ℤ (pred-ℤ (inr (inr x) +ℤ inl x))
        by ap succ-ℤ (right-predecessor-law-add-ℤ (inr (inr x)) (inl x))
      ＝ inr (inr x) +ℤ inl x
        by is-section-pred-ℤ ((inr (inr x)) +ℤ (inl x))
      ＝ zero-ℤ
        by left-inverse-law-add-ℤ (inl x)
  left-inverse-law-add-ℤ (inr (inl star)) = refl
  left-inverse-law-add-ℤ (inr (inr x)) =
    equational-reasoning
      neg-ℤ (inr (inr x)) +ℤ inr (inr x)
      ＝ inr (inr x) +ℤ inl x
        by commutative-add-ℤ (inl x) (inr (inr x))
      ＝ zero-ℤ
        by left-inverse-law-add-ℤ (inl x)

  right-inverse-law-add-ℤ :
    (x : ℤ) → x +ℤ neg-ℤ x ＝ zero-ℤ
  right-inverse-law-add-ℤ x =
    equational-reasoning
      x +ℤ neg-ℤ x
      ＝ neg-ℤ x +ℤ x
        by commutative-add-ℤ x (neg-ℤ x)
      ＝ zero-ℤ
        by left-inverse-law-add-ℤ x
```

### Interchange law for addition with respect to addition

```agda
abstract
  interchange-law-add-add-ℤ :
    (x y u v : ℤ) → (x +ℤ y) +ℤ (u +ℤ v) ＝ (x +ℤ u) +ℤ (y +ℤ v)
  interchange-law-add-add-ℤ =
    interchange-law-commutative-and-associative
      add-ℤ
      commutative-add-ℤ
      associative-add-ℤ
```

### Swapping the order of iterated addition

```agda
abstract
  right-swap-add-ℤ :
    (x y z : ℤ) → (x +ℤ y) +ℤ z ＝ (x +ℤ z) +ℤ y
  right-swap-add-ℤ x y z =
    associative-add-ℤ x y z ∙
    ap (x +ℤ_) (commutative-add-ℤ y z) ∙
    inv (associative-add-ℤ x z y)

  left-swap-add-ℤ :
    (x y z : ℤ) → x +ℤ (y +ℤ z) ＝ y +ℤ (x +ℤ z)
  left-swap-add-ℤ x y z =
    inv (associative-add-ℤ x y z) ∙
    ap (_+ℤ z) (commutative-add-ℤ x y) ∙
    associative-add-ℤ y x z
```

### Addition by `x` is a binary equivalence

```agda
abstract
  is-section-left-add-neg-ℤ :
    (x y : ℤ) → x +ℤ (neg-ℤ x +ℤ y) ＝ y
  is-section-left-add-neg-ℤ x y =
    equational-reasoning
      x +ℤ (neg-ℤ x +ℤ y)
      ＝ (x +ℤ neg-ℤ x) +ℤ y
        by inv (associative-add-ℤ x (neg-ℤ x) y)
      ＝ y
        by ap (_+ℤ y) (right-inverse-law-add-ℤ x)

  is-retraction-left-add-neg-ℤ :
    (x y : ℤ) → (neg-ℤ x) +ℤ (x +ℤ y) ＝ y
  is-retraction-left-add-neg-ℤ x y =
    equational-reasoning
      neg-ℤ x +ℤ (x +ℤ y)
      ＝ (neg-ℤ x +ℤ x) +ℤ y
        by inv (associative-add-ℤ (neg-ℤ x) x y)
      ＝ y
        by ap (_+ℤ y) (left-inverse-law-add-ℤ x)

abstract
  is-equiv-left-add-ℤ : (x : ℤ) → is-equiv (x +ℤ_)
  pr1 (pr1 (is-equiv-left-add-ℤ x)) = add-ℤ (neg-ℤ x)
  pr2 (pr1 (is-equiv-left-add-ℤ x)) = is-section-left-add-neg-ℤ x
  pr1 (pr2 (is-equiv-left-add-ℤ x)) = add-ℤ (neg-ℤ x)
  pr2 (pr2 (is-equiv-left-add-ℤ x)) = is-retraction-left-add-neg-ℤ x

equiv-left-add-ℤ : ℤ → (ℤ ≃ ℤ)
pr1 (equiv-left-add-ℤ x) = add-ℤ x
pr2 (equiv-left-add-ℤ x) = is-equiv-left-add-ℤ x

abstract
  is-section-right-add-neg-ℤ :
    (x y : ℤ) → (y +ℤ neg-ℤ x) +ℤ x ＝ y
  is-section-right-add-neg-ℤ x y =
    equational-reasoning
      (y +ℤ neg-ℤ x) +ℤ x
      ＝ y +ℤ (neg-ℤ x +ℤ x)
        by associative-add-ℤ y (neg-ℤ x) x
      ＝ y +ℤ zero-ℤ
        by ap (y +ℤ_) (left-inverse-law-add-ℤ x)
      ＝ y
        by right-unit-law-add-ℤ y

  is-retraction-right-add-neg-ℤ :
    (x y : ℤ) → (y +ℤ x) +ℤ neg-ℤ x ＝ y
  is-retraction-right-add-neg-ℤ x y =
    equational-reasoning
      (y +ℤ x) +ℤ neg-ℤ x
      ＝ y +ℤ (x +ℤ neg-ℤ x)
        by associative-add-ℤ y x (neg-ℤ x)
      ＝ y +ℤ zero-ℤ
        by ap (y +ℤ_) (right-inverse-law-add-ℤ x)
      ＝ y
        by right-unit-law-add-ℤ y

abstract
  is-equiv-right-add-ℤ : (y : ℤ) → is-equiv (_+ℤ y)
  pr1 (pr1 (is-equiv-right-add-ℤ y)) = _+ℤ (neg-ℤ y)
  pr2 (pr1 (is-equiv-right-add-ℤ y)) = is-section-right-add-neg-ℤ y
  pr1 (pr2 (is-equiv-right-add-ℤ y)) = _+ℤ (neg-ℤ y)
  pr2 (pr2 (is-equiv-right-add-ℤ y)) = is-retraction-right-add-neg-ℤ y

equiv-right-add-ℤ : ℤ → (ℤ ≃ ℤ)
pr1 (equiv-right-add-ℤ y) = _+ℤ y
pr2 (equiv-right-add-ℤ y) = is-equiv-right-add-ℤ y

is-binary-equiv-left-add-ℤ : is-binary-equiv add-ℤ
pr1 is-binary-equiv-left-add-ℤ = is-equiv-right-add-ℤ
pr2 is-binary-equiv-left-add-ℤ = is-equiv-left-add-ℤ
```

### Addition by an integer is a binary embedding

```agda
abstract
  is-emb-left-add-ℤ :
    (x : ℤ) → is-emb (x +ℤ_)
  is-emb-left-add-ℤ x =
    is-emb-is-equiv (is-equiv-left-add-ℤ x)

  is-emb-right-add-ℤ :
    (y : ℤ) → is-emb (_+ℤ y)
  is-emb-right-add-ℤ y = is-emb-is-equiv (is-equiv-right-add-ℤ y)

  is-binary-emb-add-ℤ : is-binary-emb add-ℤ
  is-binary-emb-add-ℤ =
    is-binary-emb-is-binary-equiv is-binary-equiv-left-add-ℤ
```

### Addition by `x` is injective

```agda
abstract
  is-injective-right-add-ℤ : (x : ℤ) → is-injective (_+ℤ x)
  is-injective-right-add-ℤ x = is-injective-is-emb (is-emb-right-add-ℤ x)

  is-injective-left-add-ℤ : (x : ℤ) → is-injective (x +ℤ_)
  is-injective-left-add-ℤ x = is-injective-is-emb (is-emb-left-add-ℤ x)
```

### Negative laws for addition

```agda
abstract
  right-negative-law-add-ℤ :
    (k l : ℤ) → k +ℤ neg-ℤ l ＝ neg-ℤ (neg-ℤ k +ℤ l)
  right-negative-law-add-ℤ (inl zero-ℕ) l =
    equational-reasoning
      neg-one-ℤ +ℤ neg-ℤ l
      ＝ pred-ℤ (zero-ℤ +ℤ neg-ℤ l)
        by left-predecessor-law-add-ℤ zero-ℤ (neg-ℤ l)
      ＝ neg-ℤ (succ-ℤ l)
        by pred-neg-ℤ l
  right-negative-law-add-ℤ (inl (succ-ℕ x)) l =
    equational-reasoning
      pred-ℤ (inl x) +ℤ neg-ℤ l
      ＝ pred-ℤ (inl x +ℤ neg-ℤ l)
        by left-predecessor-law-add-ℤ (inl x) (neg-ℤ l)
      ＝ pred-ℤ (neg-ℤ (neg-ℤ (inl x) +ℤ l))
        by ap pred-ℤ (right-negative-law-add-ℤ (inl x) l)
      ＝ neg-ℤ (succ-ℤ (inr (inr x) +ℤ l))
        by pred-neg-ℤ (inr (inr x) +ℤ l)
  right-negative-law-add-ℤ (inr (inl star)) l =
    refl
  right-negative-law-add-ℤ (inr (inr zero-ℕ)) l =
    inv (neg-pred-ℤ l)
  right-negative-law-add-ℤ (inr (inr (succ-ℕ n))) l =
    equational-reasoning
      succ-ℤ (in-pos-ℤ n) +ℤ neg-ℤ l
      ＝ succ-ℤ (in-pos-ℤ n +ℤ neg-ℤ l)
        by left-successor-law-add-ℤ (in-pos-ℤ n) (neg-ℤ l)
      ＝ succ-ℤ (neg-ℤ (neg-ℤ (inr (inr n)) +ℤ l))
        by ap succ-ℤ (right-negative-law-add-ℤ (inr (inr n)) l)
      ＝ neg-ℤ (pred-ℤ ((inl n) +ℤ l))
        by inv (neg-pred-ℤ ((inl n) +ℤ l))
```

### Distributivity of negatives over addition

```agda
abstract
  distributive-neg-add-ℤ :
    (k l : ℤ) → neg-ℤ (k +ℤ l) ＝ neg-ℤ k +ℤ neg-ℤ l
  distributive-neg-add-ℤ (inl zero-ℕ) l =
    equational-reasoning
      neg-ℤ (inl zero-ℕ +ℤ l)
      ＝ neg-ℤ (pred-ℤ (zero-ℤ +ℤ l))
        by ap neg-ℤ (left-predecessor-law-add-ℤ zero-ℤ l)
      ＝ neg-ℤ (inl zero-ℕ) +ℤ neg-ℤ l
        by neg-pred-ℤ l
  distributive-neg-add-ℤ (inl (succ-ℕ n)) l =
    equational-reasoning
      neg-ℤ (pred-ℤ (inl n +ℤ l))
      ＝ succ-ℤ (neg-ℤ (inl n +ℤ l))
        by neg-pred-ℤ (inl n +ℤ l)
      ＝ succ-ℤ (neg-ℤ (inl n) +ℤ neg-ℤ l)
        by ap succ-ℤ (distributive-neg-add-ℤ (inl n) l)
      ＝ neg-ℤ (pred-ℤ (inl n)) +ℤ neg-ℤ l
        by ap (_+ℤ (neg-ℤ l)) (inv (neg-pred-ℤ (inl n)))
  distributive-neg-add-ℤ (inr (inl star)) l =
    refl
  distributive-neg-add-ℤ (inr (inr zero-ℕ)) l =
    inv (pred-neg-ℤ l)
  distributive-neg-add-ℤ (inr (inr (succ-ℕ n))) l =
    equational-reasoning
      neg-ℤ (succ-ℤ (in-pos-ℤ n +ℤ l))
      ＝ pred-ℤ (neg-ℤ (in-pos-ℤ n +ℤ l))
        by inv (pred-neg-ℤ (in-pos-ℤ n +ℤ l))
      ＝ pred-ℤ (neg-ℤ (inr (inr n)) +ℤ neg-ℤ l)
        by ap pred-ℤ (distributive-neg-add-ℤ (inr (inr n)) l)
```

### The inclusion of ℕ into ℤ preserves addition

```agda
abstract
  add-int-ℕ : (x y : ℕ) → (int-ℕ x) +ℤ (int-ℕ y) ＝ int-ℕ (x +ℕ y)
  add-int-ℕ x zero-ℕ = right-unit-law-add-ℤ (int-ℕ x)
  add-int-ℕ x (succ-ℕ y) =
    equational-reasoning
      int-ℕ x +ℤ int-ℕ (succ-ℕ y)
      ＝ int-ℕ x +ℤ succ-ℤ (int-ℕ y)
        by ap ((int-ℕ x) +ℤ_) (inv (succ-int-ℕ y))
      ＝ succ-ℤ (int-ℕ x +ℤ int-ℕ y)
        by right-successor-law-add-ℤ (int-ℕ x) (int-ℕ y)
      ＝ succ-ℤ (int-ℕ (x +ℕ y))
        by ap succ-ℤ (add-int-ℕ x y)
      ＝ int-ℕ (succ-ℕ (x +ℕ y))
        by succ-int-ℕ (x +ℕ y)
```

### If `x + y = y` then `x = 0`

```agda
abstract
  is-zero-left-add-ℤ :
    (x y : ℤ) → x +ℤ y ＝ y → is-zero-ℤ x
  is-zero-left-add-ℤ x y H =
    equational-reasoning
      x
      ＝ x +ℤ zero-ℤ
        by inv (right-unit-law-add-ℤ x)
      ＝ x +ℤ (y +ℤ neg-ℤ y)
        by inv (ap (x +ℤ_) (right-inverse-law-add-ℤ y))
      ＝ (x +ℤ y) +ℤ neg-ℤ y
        by inv (associative-add-ℤ x y (neg-ℤ y))
      ＝ y +ℤ neg-ℤ y
        by ap (_+ℤ (neg-ℤ y)) H
      ＝ zero-ℤ
        by right-inverse-law-add-ℤ y
```

### If `x + y = x` then `y = 0`

```agda
abstract
  is-zero-right-add-ℤ :
    (x y : ℤ) → x +ℤ y ＝ x → is-zero-ℤ y
  is-zero-right-add-ℤ x y H =
    is-zero-left-add-ℤ y x (commutative-add-ℤ y x ∙ H)
```

## See also

- Properties of addition with respect to positivity, nonnegativity, negativity
  and nonnpositivity are derived in
  [`addition-positive-and-negative-integers`](elementary-number-theory.addition-positive-and-negative-integers.md)
- Properties of addition with respect to the standard ordering on the integers
  are derived in
  [`inequality-integers`](elementary-number-theory.inequality-integers.md)
- Properties of addition with respect to the standard strict ordering on the
  integers are derived in
  [`strict-inequality-integers`](elementary-number-theory.strict-inequality-integers.md)
