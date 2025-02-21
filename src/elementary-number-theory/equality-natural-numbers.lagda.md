# Equality of natural numbers

```agda
module elementary-number-theory.equality-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.tight-apartness-relations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.decidable-propositions
open import foundation-core.torsorial-type-families
```

</details>

## Definitions

### Observational equality on the natural numbers

```agda
Eq-ℕ : ℕ → ℕ → UU lzero
Eq-ℕ zero-ℕ zero-ℕ = unit
Eq-ℕ zero-ℕ (succ-ℕ n) = empty
Eq-ℕ (succ-ℕ m) zero-ℕ = empty
Eq-ℕ (succ-ℕ m) (succ-ℕ n) = Eq-ℕ m n
```

## Properties

### The type of natural numbers is a set

```agda
abstract
  is-prop-Eq-ℕ :
    (n m : ℕ) → is-prop (Eq-ℕ n m)
  is-prop-Eq-ℕ zero-ℕ zero-ℕ = is-prop-unit
  is-prop-Eq-ℕ zero-ℕ (succ-ℕ m) = is-prop-empty
  is-prop-Eq-ℕ (succ-ℕ n) zero-ℕ = is-prop-empty
  is-prop-Eq-ℕ (succ-ℕ n) (succ-ℕ m) = is-prop-Eq-ℕ n m

refl-Eq-ℕ : (n : ℕ) → Eq-ℕ n n
refl-Eq-ℕ zero-ℕ = star
refl-Eq-ℕ (succ-ℕ n) = refl-Eq-ℕ n

Eq-eq-ℕ : {x y : ℕ} → x ＝ y → Eq-ℕ x y
Eq-eq-ℕ {x} {.x} refl = refl-Eq-ℕ x

eq-Eq-ℕ : (x y : ℕ) → Eq-ℕ x y → x ＝ y
eq-Eq-ℕ zero-ℕ zero-ℕ e = refl
eq-Eq-ℕ (succ-ℕ x) (succ-ℕ y) e = ap succ-ℕ (eq-Eq-ℕ x y e)

abstract
  is-set-ℕ : is-set ℕ
  is-set-ℕ =
    is-set-prop-in-id
      Eq-ℕ
      is-prop-Eq-ℕ
      refl-Eq-ℕ
      eq-Eq-ℕ

ℕ-Set : Set lzero
pr1 ℕ-Set = ℕ
pr2 ℕ-Set = is-set-ℕ
```

### The property of being zero

```agda
is-prop-is-zero-ℕ : (n : ℕ) → is-prop (is-zero-ℕ n)
is-prop-is-zero-ℕ n = is-set-ℕ n zero-ℕ

is-zero-ℕ-Prop : ℕ → Prop lzero
pr1 (is-zero-ℕ-Prop n) = is-zero-ℕ n
pr2 (is-zero-ℕ-Prop n) = is-prop-is-zero-ℕ n
```

### The property of being one

```agda
is-prop-is-one-ℕ : (n : ℕ) → is-prop (is-one-ℕ n)
is-prop-is-one-ℕ n = is-set-ℕ n 1

is-one-ℕ-Prop : ℕ → Prop lzero
pr1 (is-one-ℕ-Prop n) = is-one-ℕ n
pr2 (is-one-ℕ-Prop n) = is-prop-is-one-ℕ n
```

### The type of natural numbers has decidable equality

```agda
is-decidable-Eq-ℕ :
  (m n : ℕ) → is-decidable (Eq-ℕ m n)
is-decidable-Eq-ℕ zero-ℕ zero-ℕ = inl star
is-decidable-Eq-ℕ zero-ℕ (succ-ℕ n) = inr id
is-decidable-Eq-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-Eq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-Eq-ℕ m n

has-decidable-equality-ℕ : has-decidable-equality ℕ
has-decidable-equality-ℕ x y =
  is-decidable-iff (eq-Eq-ℕ x y) Eq-eq-ℕ (is-decidable-Eq-ℕ x y)

ℕ-Discrete-Type : Discrete-Type lzero
ℕ-Discrete-Type = (ℕ , has-decidable-equality-ℕ)

decidable-eq-ℕ : ℕ → ℕ → Decidable-Prop lzero
pr1 (decidable-eq-ℕ m n) = (m ＝ n)
pr1 (pr2 (decidable-eq-ℕ m n)) = is-set-ℕ m n
pr2 (pr2 (decidable-eq-ℕ m n)) = has-decidable-equality-ℕ m n

is-decidable-is-zero-ℕ : (n : ℕ) → is-decidable (is-zero-ℕ n)
is-decidable-is-zero-ℕ n = has-decidable-equality-ℕ n zero-ℕ

is-decidable-is-zero-ℕ' : (n : ℕ) → is-decidable (is-zero-ℕ' n)
is-decidable-is-zero-ℕ' n = has-decidable-equality-ℕ zero-ℕ n

is-decidable-is-nonzero-ℕ : (n : ℕ) → is-decidable (is-nonzero-ℕ n)
is-decidable-is-nonzero-ℕ n =
  is-decidable-neg (is-decidable-is-zero-ℕ n)

is-decidable-is-one-ℕ : (n : ℕ) → is-decidable (is-one-ℕ n)
is-decidable-is-one-ℕ n = has-decidable-equality-ℕ n 1

is-decidable-is-one-ℕ' : (n : ℕ) → is-decidable (is-one-ℕ' n)
is-decidable-is-one-ℕ' n = has-decidable-equality-ℕ 1 n

is-decidable-is-not-one-ℕ :
  (x : ℕ) → is-decidable (is-not-one-ℕ x)
is-decidable-is-not-one-ℕ x =
  is-decidable-neg (is-decidable-is-one-ℕ x)
```

## The full characterization of the identity type of `ℕ`

```agda
map-total-Eq-ℕ :
  (m : ℕ) → Σ ℕ (Eq-ℕ m) → Σ ℕ (Eq-ℕ (succ-ℕ m))
pr1 (map-total-Eq-ℕ m (n , e)) = succ-ℕ n
pr2 (map-total-Eq-ℕ m (n , e)) = e

is-torsorial-Eq-ℕ :
  (m : ℕ) → is-torsorial (Eq-ℕ m)
pr1 (pr1 (is-torsorial-Eq-ℕ m)) = m
pr2 (pr1 (is-torsorial-Eq-ℕ m)) = refl-Eq-ℕ m
pr2 (is-torsorial-Eq-ℕ zero-ℕ) (pair zero-ℕ star) = refl
pr2 (is-torsorial-Eq-ℕ (succ-ℕ m)) (pair (succ-ℕ n) e) =
  ap (map-total-Eq-ℕ m) (pr2 (is-torsorial-Eq-ℕ m) (pair n e))

is-equiv-Eq-eq-ℕ :
  {m n : ℕ} → is-equiv (Eq-eq-ℕ {m} {n})
is-equiv-Eq-eq-ℕ {m} {n} =
  fundamental-theorem-id
    ( is-torsorial-Eq-ℕ m)
    ( λ y → Eq-eq-ℕ {m} {y})
    ( n)
```

### The type of natural numbers is its own set truncation

```agda
equiv-unit-trunc-ℕ-Set : ℕ ≃ type-trunc-Set ℕ
equiv-unit-trunc-ℕ-Set = equiv-unit-trunc-Set ℕ-Set
```

### The natural numbers have a tight apartness relation

```agda
ℕ-Type-With-Tight-Apartness : Type-With-Tight-Apartness lzero lzero
ℕ-Type-With-Tight-Apartness =
  type-with-tight-apartness-Discrete-Type ℕ-Discrete-Type
```
