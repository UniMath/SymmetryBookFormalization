---
title: Equality in the standard finite types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.equality-standard-finite-types where

open import elementary-number-theory.inequality-natural-numbers using (leq-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation-core.decidable-propositions using (decidable-Prop)

open import foundation.contractible-types using (is-contr)
open import foundation.coproduct-types using (coprod; inl; inr; is-prop-coprod; neq-inr-inl)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-empty; is-decidable-unit)
open import foundation.dependent-pair-types using (Σ; pr1; pr2)
open import foundation.empty-types using (empty; is-set-empty)
open import foundation.equality-coproduct-types using
  ( is-set-coprod)
open import foundation.equivalences using (_≃_)
open import foundation.functoriality-coproduct-types using (map-coprod)
open import foundation.identity-types using (Id; refl; ap; inv; _∙_)
open import foundation.negation using (¬; map-neg)
open import foundation.propositions using (is-prop; is-proof-irrelevant-is-prop)
open import foundation.raising-universe-levels using (raise-Set)
open import foundation.set-truncations using
  ( type-trunc-Set; equiv-unit-trunc-Set)
open import foundation.sets using (is-set; UU-Set)
open import foundation.unit-type using (unit; star; is-set-unit)
open import foundation.universe-levels using (Level; UU; lzero)

open import univalent-combinatorics.standard-finite-types using
  ( Fin; zero-Fin; is-zero-Fin; one-Fin; is-one-Fin; neg-one-Fin;
    is-neg-one-Fin; is-zero-or-one-Fin-two-ℕ; is-set-Fin; Fin-Set)
```

## Idea

Since the standard finite types are defined recursively by adding a point one at a time, it follows that equality in the standard finite types is decidable, and that they are sets.

## Properties

### Characterization of the identity types of the standard finite types

```agda
Eq-Fin : (k : ℕ) → Fin k → Fin k → UU lzero
Eq-Fin (succ-ℕ k) (inl x) (inl y) = Eq-Fin k x y
Eq-Fin (succ-ℕ k) (inl x) (inr y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inl y) = empty
Eq-Fin (succ-ℕ k) (inr x) (inr y) = unit

refl-Eq-Fin : (k : ℕ) (x : Fin k) → Eq-Fin k x x
refl-Eq-Fin (succ-ℕ k) (inl x) = refl-Eq-Fin k x
refl-Eq-Fin (succ-ℕ k) (inr x) = star

Eq-Fin-eq : (k : ℕ) {x y : Fin k} → Id x y → Eq-Fin k x y
Eq-Fin-eq k refl = refl-Eq-Fin k _

eq-Eq-Fin :
  (k : ℕ) {x y : Fin k} → Eq-Fin k x y → Id x y
eq-Eq-Fin (succ-ℕ k) {inl x} {inl y} e = ap inl (eq-Eq-Fin k e)
eq-Eq-Fin (succ-ℕ k) {inr star} {inr star} star = refl

is-decidable-Eq-Fin : (k : ℕ) (x y : Fin k) → is-decidable (Eq-Fin k x y)
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inl y) = is-decidable-Eq-Fin k x y
is-decidable-Eq-Fin (succ-ℕ k) (inl x) (inr y) = is-decidable-empty
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inl y) = is-decidable-empty
is-decidable-Eq-Fin (succ-ℕ k) (inr x) (inr y) = is-decidable-unit

has-decidable-equality-Fin :
  (k : ℕ) (x y : Fin k) → is-decidable (Id x y)
has-decidable-equality-Fin k x y =
  map-coprod (eq-Eq-Fin k) (map-neg (Eq-Fin-eq k)) (is-decidable-Eq-Fin k x y)

is-decidable-is-zero-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-zero-Fin k x)
is-decidable-is-zero-Fin {succ-ℕ k} x =
  has-decidable-equality-Fin (succ-ℕ k) x (zero-Fin k)

is-decidable-is-neg-one-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-neg-one-Fin k x)
is-decidable-is-neg-one-Fin {succ-ℕ k} x =
  has-decidable-equality-Fin (succ-ℕ k) x (neg-one-Fin k)

is-decidable-is-one-Fin :
  {k : ℕ} (x : Fin k) → is-decidable (is-one-Fin k x)
is-decidable-is-one-Fin {succ-ℕ k} x =
  has-decidable-equality-Fin (succ-ℕ k) x (one-Fin k)
```

### Being zero or being one is a proposition

```agda
is-prop-is-zero-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → is-prop (is-zero-Fin (succ-ℕ k) x)
is-prop-is-zero-Fin k x = is-set-Fin (succ-ℕ k) x (zero-Fin k)

is-prop-is-one-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → is-prop (is-one-Fin (succ-ℕ k) x)
is-prop-is-one-Fin k x = is-set-Fin (succ-ℕ k) x (one-Fin k)

is-prop-is-zero-or-one-Fin-two-ℕ :
  (x : Fin 2) → is-prop (coprod (is-zero-Fin 2 x) (is-one-Fin 2 x))
is-prop-is-zero-or-one-Fin-two-ℕ x =
  is-prop-coprod
    ( λ p q → Eq-Fin-eq 2 (inv p ∙ q))
    ( is-prop-is-zero-Fin 1 x)
    ( is-prop-is-one-Fin 1 x)
```

### Every element in the standard two-element type is either 0 or 1.

```agda
is-contr-is-zero-or-one-Fin-two-ℕ :
  (x : Fin 2) → is-contr (coprod (is-zero-Fin 2 x) (is-one-Fin 2 x))
is-contr-is-zero-or-one-Fin-two-ℕ x =
  is-proof-irrelevant-is-prop
    ( is-prop-is-zero-or-one-Fin-two-ℕ x)
    ( is-zero-or-one-Fin-two-ℕ x)
```

```agda
decidable-Eq-Fin :
  (n : ℕ) (i j : Fin n) → decidable-Prop lzero
pr1 (decidable-Eq-Fin n i j) = Id i j
pr1 (pr2 (decidable-Eq-Fin n i j)) = is-set-Fin n i j
pr2 (pr2 (decidable-Eq-Fin n i j)) = has-decidable-equality-Fin n i j
```

### The standard finite types are their own set truncations

```agda
equiv-unit-trunc-Fin-Set : (k : ℕ) → Fin k ≃ type-trunc-Set (Fin k)
equiv-unit-trunc-Fin-Set k = equiv-unit-trunc-Set (Fin-Set k)
```

### If `leq-ℕ 2 n`, then there exists two distinct elements in `Fin n`

```agda
two-distinct-elements-leq-2-Fin : (n : ℕ) → leq-ℕ 2 n →
  Σ (Fin n) (λ x → Σ (Fin n) (λ y → ¬ (Id x y)))
pr1 (two-distinct-elements-leq-2-Fin (succ-ℕ (succ-ℕ n)) ineq) = inr star
pr1 (pr2 (two-distinct-elements-leq-2-Fin (succ-ℕ (succ-ℕ n)) ineq)) = inl (inr star)
pr2 (pr2 (two-distinct-elements-leq-2-Fin (succ-ℕ (succ-ℕ n)) ineq)) = neq-inr-inl
```
