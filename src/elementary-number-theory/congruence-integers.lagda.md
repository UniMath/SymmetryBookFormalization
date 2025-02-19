# The congruence relations on the integers

```agda
module elementary-number-theory.congruence-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-integers
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.distance-integers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.unit-integers
open import elementary-number-theory.unit-similarity-integers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Definitions

```agda
cong-ℤ : ℤ → ℤ → ℤ → UU lzero
cong-ℤ k x y = div-ℤ k (x -ℤ y)

is-cong-zero-ℤ : ℤ → ℤ → UU lzero
is-cong-zero-ℤ k x = cong-ℤ k x zero-ℤ
```

## Properties

```agda
is-cong-zero-div-ℤ : (k x : ℤ) → div-ℤ k x → is-cong-zero-ℤ k x
pr1 (is-cong-zero-div-ℤ k x (pair d p)) = d
pr2 (is-cong-zero-div-ℤ k x (pair d p)) = p ∙ inv (right-unit-law-add-ℤ x)

div-is-cong-zero-ℤ : (k x : ℤ) → is-cong-zero-ℤ k x → div-ℤ k x
pr1 (div-is-cong-zero-ℤ k x (pair d p)) = d
pr2 (div-is-cong-zero-ℤ k x (pair d p)) = p ∙ right-unit-law-add-ℤ x

is-indiscrete-cong-ℤ : (k : ℤ) → is-unit-ℤ k → (x y : ℤ) → cong-ℤ k x y
is-indiscrete-cong-ℤ k H x y = div-is-unit-ℤ k (x -ℤ y) H

is-discrete-cong-ℤ : (k : ℤ) → is-zero-ℤ k → (x y : ℤ) → cong-ℤ k x y → x ＝ y
is-discrete-cong-ℤ .zero-ℤ refl x y K =
  eq-diff-ℤ (is-zero-div-zero-ℤ (x -ℤ y) K)

is-unit-cong-succ-ℤ : (k x : ℤ) → cong-ℤ k x (succ-ℤ x) → is-unit-ℤ k
is-unit-cong-succ-ℤ k x (y , p) =
  is-unit-div-one-ℤ k
    ( neg-ℤ y ,
      ( left-negative-law-mul-ℤ y k) ∙
      ( is-injective-neg-ℤ
        ( ( neg-neg-ℤ (y *ℤ k)) ∙
          ( ( p) ∙
            ( ( ap (x +ℤ_) (neg-succ-ℤ x)) ∙
              ( ( right-predecessor-law-add-ℤ x (neg-ℤ x)) ∙
                ( ap pred-ℤ (right-inverse-law-add-ℤ x))))))))

is-unit-cong-pred-ℤ : (k x : ℤ) → cong-ℤ k x (pred-ℤ x) → is-unit-ℤ k
is-unit-cong-pred-ℤ k x (y , p) =
  is-unit-div-one-ℤ k
    ( y ,
      ( p) ∙
      ( ( ap (x +ℤ_) (neg-pred-ℤ x)) ∙
        ( ( right-successor-law-add-ℤ x (neg-ℤ x)) ∙
          ( ap succ-ℤ (right-inverse-law-add-ℤ x)))))

refl-cong-ℤ : (k : ℤ) → is-reflexive (cong-ℤ k)
pr1 (refl-cong-ℤ k x) = zero-ℤ
pr2 (refl-cong-ℤ k x) = left-zero-law-mul-ℤ k ∙ inv (is-zero-diff-ℤ' x)

symmetric-cong-ℤ : (k : ℤ) → is-symmetric (cong-ℤ k)
pr1 (symmetric-cong-ℤ k x y (pair d p)) = neg-ℤ d
pr2 (symmetric-cong-ℤ k x y (pair d p)) =
  ( left-negative-law-mul-ℤ d k) ∙
  ( ( ap neg-ℤ p) ∙
    ( distributive-neg-diff-ℤ x y))

transitive-cong-ℤ : (k : ℤ) → is-transitive (cong-ℤ k)
pr1 (transitive-cong-ℤ k x y z (pair e q) (pair d p)) = d +ℤ e
pr2 (transitive-cong-ℤ k x y z (pair e q) (pair d p)) =
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
  transitive-cong-ℤ k x y z K H

concatenate-cong-cong-cong-ℤ :
  (k x y z w : ℤ) → cong-ℤ k x y → cong-ℤ k y z → cong-ℤ k z w → cong-ℤ k x w
concatenate-cong-cong-cong-ℤ k x y z w H K L =
  transitive-cong-ℤ k x y w (transitive-cong-ℤ k y z w L K) H

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
    ( sim-unit-abs-ℤ ((int-ℕ x) -ℤ (int-ℕ y)))
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
        ( symmetric-sim-unit-ℤ
          ( int-abs-ℤ (int-ℕ x -ℤ int-ℕ y))
          ( int-ℕ x -ℤ int-ℕ y)
          ( sim-unit-abs-ℤ ((int-ℕ x) -ℤ (int-ℕ y))))
        ( H)))
```
