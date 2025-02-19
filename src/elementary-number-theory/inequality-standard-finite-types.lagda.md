# Inequality on the standard finite types

```agda
module elementary-number-theory.inequality-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.preorders

open import univalent-combinatorics.standard-finite-types
```

</details>

## Definitions

```agda
leq-Fin : (k : ℕ) → Fin k → Fin k → UU lzero
leq-Fin (succ-ℕ k) x (inr y) = unit
leq-Fin (succ-ℕ k) (inl x) (inl y) = leq-Fin k x y
leq-Fin (succ-ℕ k) (inr x) (inl y) = empty

abstract
  is-prop-leq-Fin :
    (k : ℕ) (x y : Fin k) → is-prop (leq-Fin k x y)
  is-prop-leq-Fin (succ-ℕ k) (inl x) (inl y) = is-prop-leq-Fin k x y
  is-prop-leq-Fin (succ-ℕ k) (inl x) (inr star) = is-prop-unit
  is-prop-leq-Fin (succ-ℕ k) (inr star) (inl y) = is-prop-empty
  is-prop-leq-Fin (succ-ℕ k) (inr star) (inr star) = is-prop-unit

leq-Fin-Prop : (k : ℕ) → Fin k → Fin k → Prop lzero
pr1 (leq-Fin-Prop k x y) = leq-Fin k x y
pr2 (leq-Fin-Prop k x y) = is-prop-leq-Fin k x y

leq-neg-one-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → leq-Fin (succ-ℕ k) x (neg-one-Fin k)
leq-neg-one-Fin k x = star

refl-leq-Fin : (k : ℕ) → is-reflexive (leq-Fin k)
refl-leq-Fin (succ-ℕ k) (inl x) = refl-leq-Fin k x
refl-leq-Fin (succ-ℕ k) (inr star) = star

antisymmetric-leq-Fin :
  (k : ℕ) (x y : Fin k) → leq-Fin k x y → leq-Fin k y x → x ＝ y
antisymmetric-leq-Fin (succ-ℕ k) (inl x) (inl y) H K =
  ap inl (antisymmetric-leq-Fin k x y H K)
antisymmetric-leq-Fin (succ-ℕ k) (inr star) (inr star) H K = refl

transitive-leq-Fin :
  (k : ℕ) → is-transitive (leq-Fin k)
transitive-leq-Fin (succ-ℕ k) (inl x) (inl y) (inl z) H K =
  transitive-leq-Fin k x y z H K
transitive-leq-Fin (succ-ℕ k) (inl x) (inl y) (inr star) H K = star
transitive-leq-Fin (succ-ℕ k) (inl x) (inr star) (inr star) H K = star
transitive-leq-Fin (succ-ℕ k) (inr star) (inr star) (inr star) H K = star

concatenate-eq-leq-eq-Fin :
  (k : ℕ) {x1 x2 x3 x4 : Fin k} →
  x1 ＝ x2 → leq-Fin k x2 x3 → x3 ＝ x4 → leq-Fin k x1 x4
concatenate-eq-leq-eq-Fin k refl H refl = H

leq-succ-Fin :
  (k : ℕ) (x : Fin k) →
  leq-Fin (succ-ℕ k) (inl-Fin k x) (succ-Fin (succ-ℕ k) (inl-Fin k x))
leq-succ-Fin (succ-ℕ k) (inl x) = leq-succ-Fin k x
leq-succ-Fin (succ-ℕ k) (inr star) = star

preserves-order-nat-Fin :
  (k : ℕ) {x y : Fin k} → leq-Fin k x y → leq-ℕ (nat-Fin k x) (nat-Fin k y)
preserves-order-nat-Fin (succ-ℕ k) {inl x} {inl y} H =
  preserves-order-nat-Fin k H
preserves-order-nat-Fin (succ-ℕ k) {inl x} {inr star} H =
  leq-le-ℕ (nat-Fin k x) k (strict-upper-bound-nat-Fin k x)
preserves-order-nat-Fin (succ-ℕ k) {inr star} {inr star} H =
  refl-leq-ℕ k

reflects-order-nat-Fin :
  (k : ℕ) {x y : Fin k} → leq-ℕ (nat-Fin k x) (nat-Fin k y) → leq-Fin k x y
reflects-order-nat-Fin (succ-ℕ k) {inl x} {inl y} H =
  reflects-order-nat-Fin k H
reflects-order-nat-Fin (succ-ℕ k) {inr star} {inl y} H =
  ex-falso
    ( contradiction-le-ℕ (nat-Fin k y) k (strict-upper-bound-nat-Fin k y) H)
reflects-order-nat-Fin (succ-ℕ k) {inl x} {inr star} H = star
reflects-order-nat-Fin (succ-ℕ k) {inr star} {inr star} H = star
```

### The partial order on the standard finite types

```agda
Fin-Preorder : ℕ → Preorder lzero lzero
pr1 (Fin-Preorder k) = Fin k
pr1 (pr2 (Fin-Preorder k)) = leq-Fin-Prop k
pr1 (pr2 (pr2 (Fin-Preorder k))) = refl-leq-Fin k
pr2 (pr2 (pr2 (Fin-Preorder k))) = transitive-leq-Fin k

Fin-Poset : ℕ → Poset lzero lzero
pr1 (Fin-Poset k) = Fin-Preorder k
pr2 (Fin-Poset k) = antisymmetric-leq-Fin k
```

## Properties

### Ordering on the standard finite types is decidable

```agda
is-decidable-leq-Fin : (k : ℕ) (x y : Fin k) → is-decidable (leq-Fin k x y)
is-decidable-leq-Fin (succ-ℕ k) (inl x) (inl y) = is-decidable-leq-Fin k x y
is-decidable-leq-Fin (succ-ℕ k) (inl x) (inr y) = inl star
is-decidable-leq-Fin (succ-ℕ k) (inr x) (inl y) = inr (λ x → x)
is-decidable-leq-Fin (succ-ℕ k) (inr x) (inr y) = inl star

leq-Fin-Decidable-Prop : (k : ℕ) → Fin k → Fin k → Decidable-Prop lzero
pr1 (leq-Fin-Decidable-Prop k x y) = leq-Fin k x y
pr1 (pr2 (leq-Fin-Decidable-Prop k x y)) = is-prop-leq-Fin k x y
pr2 (pr2 (leq-Fin-Decidable-Prop k x y)) = is-decidable-leq-Fin k x y
```

### Ordering on the standard finite types is linear

```agda
linear-leq-Fin : (k : ℕ) (x y : Fin k) → leq-Fin k x y + leq-Fin k y x
linear-leq-Fin (succ-ℕ k) (inl x) (inl y) = linear-leq-Fin k x y
linear-leq-Fin (succ-ℕ k) (inl x) (inr y) = inl star
linear-leq-Fin (succ-ℕ k) (inr x) y = inr star
```
