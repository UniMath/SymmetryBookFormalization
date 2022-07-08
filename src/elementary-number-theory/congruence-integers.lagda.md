---
title: The congruence relations on the integers
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.congruence-integers where

open import elementary-number-theory.addition-integers using
  ( add-ℤ; ap-add-ℤ; right-unit-law-add-ℤ; right-predecessor-law-add-ℤ;
    right-inverse-law-add-ℤ; right-successor-law-add-ℤ; distributive-neg-add-ℤ)
open import elementary-number-theory.congruence-natural-numbers using (cong-ℕ)
open import elementary-number-theory.difference-integers using
  ( diff-ℤ; eq-diff-ℤ; is-zero-diff-ℤ'; distributive-neg-diff-ℤ;
    triangle-diff-ℤ)
open import elementary-number-theory.distance-integers using (dist-int-ℕ)
open import elementary-number-theory.divisibility-integers using
  ( div-ℤ; is-unit-ℤ; div-is-unit-ℤ; is-zero-div-zero-ℤ; div-sim-unit-ℤ;
    refl-sim-unit-ℤ; sim-unit-abs-ℤ; div-int-div-ℕ; div-div-int-ℕ;
    symm-sim-unit-ℤ)
open import elementary-number-theory.integers using
  ( ℤ; zero-ℤ; is-zero-ℤ; succ-ℤ; neg-ℤ; is-injective-neg-ℤ; neg-neg-ℤ; int-ℕ;
    neg-succ-ℤ; pred-ℤ; neg-pred-ℤ)
open import elementary-number-theory.multiplication-integers using
  ( mul-ℤ; left-negative-law-mul-ℤ; left-zero-law-mul-ℤ;
    right-distributive-mul-add-ℤ)
open import elementary-number-theory.natural-numbers using (ℕ)
open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (pair; pr1; pr2)
open import foundation.functions using (id)
open import foundation.identity-types using (_＝_; refl; _∙_; inv; ap; tr)
open import foundation.universe-levels using (UU; lzero)
```

# The congruence relations on the integers

```agda
cong-ℤ : ℤ → ℤ → ℤ → UU lzero
cong-ℤ k x y = div-ℤ k (diff-ℤ x y)

is-cong-zero-ℤ : ℤ → ℤ → UU lzero
is-cong-zero-ℤ k x = cong-ℤ k x zero-ℤ

is-cong-zero-div-ℤ : (k x : ℤ) → div-ℤ k x → is-cong-zero-ℤ k x
pr1 (is-cong-zero-div-ℤ k x (pair d p)) = d
pr2 (is-cong-zero-div-ℤ k x (pair d p)) = p ∙ inv (right-unit-law-add-ℤ x)

div-is-cong-zero-ℤ : (k x : ℤ) → is-cong-zero-ℤ k x → div-ℤ k x
pr1 (div-is-cong-zero-ℤ k x (pair d p)) = d
pr2 (div-is-cong-zero-ℤ k x (pair d p)) = p ∙ right-unit-law-add-ℤ x

is-indiscrete-cong-ℤ : (k : ℤ) → is-unit-ℤ k → (x y : ℤ) → cong-ℤ k x y
is-indiscrete-cong-ℤ k H x y = div-is-unit-ℤ k (diff-ℤ x y) H

is-discrete-cong-ℤ : (k : ℤ) → is-zero-ℤ k → (x y : ℤ) → cong-ℤ k x y → x ＝ y
is-discrete-cong-ℤ .zero-ℤ refl x y K =
  eq-diff-ℤ (is-zero-div-zero-ℤ (diff-ℤ x y) K)

is-unit-cong-succ-ℤ : (k x : ℤ) → cong-ℤ k x (succ-ℤ x) → is-unit-ℤ k
pr1 (is-unit-cong-succ-ℤ k x (pair y p)) = neg-ℤ y
pr2 (is-unit-cong-succ-ℤ k x (pair y p)) =
  ( left-negative-law-mul-ℤ y k) ∙
  ( is-injective-neg-ℤ
    ( ( neg-neg-ℤ (mul-ℤ y k)) ∙
      ( ( p) ∙
        ( ( ap (add-ℤ x) (neg-succ-ℤ x)) ∙
          ( ( right-predecessor-law-add-ℤ x (neg-ℤ x)) ∙
            ( ap pred-ℤ (right-inverse-law-add-ℤ x)))))))

is-unit-cong-pred-ℤ : (k x : ℤ) → cong-ℤ k x (pred-ℤ x) → is-unit-ℤ k
pr1 (is-unit-cong-pred-ℤ k x (pair y p)) = y
pr2 (is-unit-cong-pred-ℤ k x (pair y p)) =
  ( p) ∙
  ( ( ap (add-ℤ x) (neg-pred-ℤ x)) ∙
    ( ( right-successor-law-add-ℤ x (neg-ℤ x)) ∙
      ( ap succ-ℤ (right-inverse-law-add-ℤ x))))

refl-cong-ℤ : (k x : ℤ) → cong-ℤ k x x
pr1 (refl-cong-ℤ k x) = zero-ℤ
pr2 (refl-cong-ℤ k x) = left-zero-law-mul-ℤ k ∙ inv (is-zero-diff-ℤ' x)

symmetric-cong-ℤ : (k x y : ℤ) → cong-ℤ k x y → cong-ℤ k y x
pr1 (symmetric-cong-ℤ k x y (pair d p)) = neg-ℤ d
pr2 (symmetric-cong-ℤ k x y (pair d p)) =
  ( left-negative-law-mul-ℤ d k) ∙
  ( ( ap neg-ℤ p) ∙
    ( distributive-neg-diff-ℤ x y))

transitive-cong-ℤ : (k x y z : ℤ) → cong-ℤ k x y → cong-ℤ k y z → cong-ℤ k x z
pr1 (transitive-cong-ℤ k x y z (pair d p) (pair e q)) = add-ℤ d e
pr2 (transitive-cong-ℤ k x y z (pair d p) (pair e q)) =
  ( right-distributive-mul-add-ℤ d e k) ∙
  ( ( ap-add-ℤ p q) ∙
    ( triangle-diff-ℤ x y z))

concatenate-eq-cong-ℤ :
  (k x x' y : ℤ) → x ＝ x' → cong-ℤ k x' y → cong-ℤ k x y
concatenate-eq-cong-ℤ k x .x y refl = id

concatenate-cong-eq-ℤ :
  (k x y y' : ℤ) → cong-ℤ k x y → y ＝ y' → cong-ℤ k x y'
concatenate-cong-eq-ℤ k x y .y H refl = H

concatenate-eq-cong-eq-ℤ :
  (k x x' y' y : ℤ) → x ＝ x' → cong-ℤ k x' y' → y' ＝ y → cong-ℤ k x y
concatenate-eq-cong-eq-ℤ k x .x y .y refl H refl = H

concatenate-cong-eq-cong-ℤ :
  (k x y y' z : ℤ) → cong-ℤ k x y → y ＝ y' → cong-ℤ k y' z → cong-ℤ k x z
concatenate-cong-eq-cong-ℤ k x y .y z H refl K =
  transitive-cong-ℤ k x y z H K

concatenate-cong-cong-cong-ℤ :
  (k x y z w : ℤ) → cong-ℤ k x y → cong-ℤ k y z → cong-ℤ k z w → cong-ℤ k x w
concatenate-cong-cong-cong-ℤ k x y z w H K L =
  transitive-cong-ℤ k x y w H
    ( transitive-cong-ℤ k y z w K L)

cong-cong-neg-ℤ : (k x y : ℤ) → cong-ℤ k (neg-ℤ x) (neg-ℤ y) → cong-ℤ k x y
pr1 (cong-cong-neg-ℤ k x y (pair d p)) = neg-ℤ d
pr2 (cong-cong-neg-ℤ k x y (pair d p)) =
  ( left-negative-law-mul-ℤ d k) ∙
  ( ( ap neg-ℤ p) ∙
    ( ( distributive-neg-add-ℤ (neg-ℤ x) (neg-ℤ (neg-ℤ y))) ∙
      ( ap-add-ℤ (neg-neg-ℤ x) (neg-neg-ℤ (neg-ℤ y)))))

cong-neg-cong-ℤ : (k x y : ℤ) → cong-ℤ k x y → cong-ℤ k (neg-ℤ x) (neg-ℤ y)
pr1 (cong-neg-cong-ℤ k x y (pair d p)) = neg-ℤ d
pr2 (cong-neg-cong-ℤ k x y (pair d p)) =
  ( left-negative-law-mul-ℤ d k) ∙
  ( ( ap neg-ℤ p) ∙
    ( distributive-neg-add-ℤ x (neg-ℤ y)))
```

```agda
cong-int-cong-ℕ :
  (k x y : ℕ) → cong-ℕ k x y → cong-ℤ (int-ℕ k) (int-ℕ x) (int-ℕ y)
cong-int-cong-ℕ k x y H =
  div-sim-unit-ℤ
    ( refl-sim-unit-ℤ (int-ℕ k))
    ( sim-unit-abs-ℤ (diff-ℤ (int-ℕ x) (int-ℕ y)))
    ( tr
      ( div-ℤ (int-ℕ k))
      ( inv (ap int-ℕ (dist-int-ℕ x y)))
      ( div-int-div-ℕ H))

cong-cong-int-ℕ :
  (k x y : ℕ) → cong-ℤ (int-ℕ k) (int-ℕ x) (int-ℕ y) → cong-ℕ k x y
cong-cong-int-ℕ k x y H =
  div-div-int-ℕ
    ( tr
      ( div-ℤ (int-ℕ k))
      ( ap int-ℕ (dist-int-ℕ x y))
      ( div-sim-unit-ℤ
        ( refl-sim-unit-ℤ (int-ℕ k))
        ( symm-sim-unit-ℤ (sim-unit-abs-ℤ (diff-ℤ (int-ℕ x) (int-ℕ y))))
        ( H)))
```
