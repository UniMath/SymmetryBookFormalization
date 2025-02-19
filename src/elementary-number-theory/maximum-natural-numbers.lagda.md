# Maximum on the natural numbers

```agda
module elementary-number-theory.maximum-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.coproduct-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type

open import order-theory.least-upper-bounds-posets

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The {{#concept "maximum" Disambiguation="natural numbers" Agda=max-ℕ}} of two
[natural numbers](elementary-number-theory.natural-numbers.md) is a binary
operation that returns the largest of two natural numbers. It is defined
recursively by

```text
  max-ℕ 0 n = n
  max-ℕ (m + 1) 0 = m + 1
  max-ℕ (m + 1) (n + 1) = (max m n) + 1.
```

Furthermore, we define the maximum of any
[standard finite](univalent-combinatorics.standard-finite-types.md) family of
natural numbers.

## Definition

### Maximum of natural numbers

```agda
max-ℕ : ℕ → (ℕ → ℕ)
max-ℕ 0 n = n
max-ℕ (succ-ℕ m) 0 = succ-ℕ m
max-ℕ (succ-ℕ m) (succ-ℕ n) = succ-ℕ (max-ℕ m n)

ap-max-ℕ : {x x' y y' : ℕ} → x ＝ x' → y ＝ y' → max-ℕ x y ＝ max-ℕ x' y'
ap-max-ℕ p q = ap-binary max-ℕ p q

max-ℕ' : ℕ → (ℕ → ℕ)
max-ℕ' x y = max-ℕ y x
```

### Maximum of elements of standard finite types

```agda
max-standard-finite-family-ℕ : (n : ℕ) → (Fin n → ℕ) → ℕ
max-standard-finite-family-ℕ zero-ℕ f = zero-ℕ
max-standard-finite-family-ℕ (succ-ℕ n) f =
  max-ℕ (max-standard-finite-family-ℕ n (λ k → f (inl k))) (f (inr star))
```

## Properties

### Maximum is a least upper bound

```agda
leq-max-ℕ :
  (k m n : ℕ) → m ≤-ℕ k → n ≤-ℕ k → (max-ℕ m n) ≤-ℕ k
leq-max-ℕ zero-ℕ zero-ℕ zero-ℕ H K = star
leq-max-ℕ (succ-ℕ k) zero-ℕ zero-ℕ H K = star
leq-max-ℕ (succ-ℕ k) zero-ℕ (succ-ℕ n) H K = K
leq-max-ℕ (succ-ℕ k) (succ-ℕ m) zero-ℕ H K = H
leq-max-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H K = leq-max-ℕ k m n H K

leq-left-leq-max-ℕ :
  (k m n : ℕ) → max-ℕ m n ≤-ℕ k → m ≤-ℕ k
leq-left-leq-max-ℕ k zero-ℕ zero-ℕ H = star
leq-left-leq-max-ℕ k zero-ℕ (succ-ℕ n) H = star
leq-left-leq-max-ℕ k (succ-ℕ m) zero-ℕ H = H
leq-left-leq-max-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
  leq-left-leq-max-ℕ k m n H

leq-right-leq-max-ℕ :
  (k m n : ℕ) → max-ℕ m n ≤-ℕ k → n ≤-ℕ k
leq-right-leq-max-ℕ k zero-ℕ zero-ℕ H = star
leq-right-leq-max-ℕ k zero-ℕ (succ-ℕ n) H = H
leq-right-leq-max-ℕ k (succ-ℕ m) zero-ℕ H = star
leq-right-leq-max-ℕ (succ-ℕ k) (succ-ℕ m) (succ-ℕ n) H =
  leq-right-leq-max-ℕ k m n H

left-leq-max-ℕ : (m n : ℕ) → m ≤-ℕ max-ℕ m n
left-leq-max-ℕ m n =
  leq-left-leq-max-ℕ (max-ℕ m n) m n (refl-leq-ℕ (max-ℕ m n))

right-leq-max-ℕ : (m n : ℕ) → n ≤-ℕ max-ℕ m n
right-leq-max-ℕ m n =
  leq-right-leq-max-ℕ (max-ℕ m n) m n (refl-leq-ℕ (max-ℕ m n))

is-least-upper-bound-max-ℕ :
  (m n : ℕ) → is-least-binary-upper-bound-Poset ℕ-Poset m n (max-ℕ m n)
is-least-upper-bound-max-ℕ m n =
  prove-is-least-binary-upper-bound-Poset
    ( ℕ-Poset)
    { m}
    { n}
    { max-ℕ m n}
    ( left-leq-max-ℕ m n , right-leq-max-ℕ m n)
    ( λ x (H , K) → leq-max-ℕ x m n H K)
```

### Associativity of `max-ℕ`

```agda
associative-max-ℕ :
  (x y z : ℕ) → max-ℕ (max-ℕ x y) z ＝ max-ℕ x (max-ℕ y z)
associative-max-ℕ zero-ℕ y z = refl
associative-max-ℕ (succ-ℕ x) zero-ℕ zero-ℕ = refl
associative-max-ℕ (succ-ℕ x) zero-ℕ (succ-ℕ z) = refl
associative-max-ℕ (succ-ℕ x) (succ-ℕ y) zero-ℕ = refl
associative-max-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) =
  ap succ-ℕ (associative-max-ℕ x y z)
```

### Unit laws for `max-ℕ`

```agda
left-unit-law-max-ℕ : (x : ℕ) → max-ℕ 0 x ＝ x
left-unit-law-max-ℕ x = refl

right-unit-law-max-ℕ : (x : ℕ) → max-ℕ x 0 ＝ x
right-unit-law-max-ℕ zero-ℕ = refl
right-unit-law-max-ℕ (succ-ℕ x) = refl
```

### Commutativity of `max-ℕ`

```agda
commutative-max-ℕ : (x y : ℕ) → max-ℕ x y ＝ max-ℕ y x
commutative-max-ℕ zero-ℕ zero-ℕ = refl
commutative-max-ℕ zero-ℕ (succ-ℕ y) = refl
commutative-max-ℕ (succ-ℕ x) zero-ℕ = refl
commutative-max-ℕ (succ-ℕ x) (succ-ℕ y) = ap succ-ℕ (commutative-max-ℕ x y)
```

### `max-ℕ` is idempotent

```agda
idempotent-max-ℕ : (x : ℕ) → max-ℕ x x ＝ x
idempotent-max-ℕ zero-ℕ = refl
idempotent-max-ℕ (succ-ℕ x) = ap succ-ℕ (idempotent-max-ℕ x)
```

### Successor diagonal laws for `max-ℕ`

```agda
left-successor-diagonal-law-max-ℕ : (x : ℕ) → max-ℕ (succ-ℕ x) x ＝ succ-ℕ x
left-successor-diagonal-law-max-ℕ zero-ℕ = refl
left-successor-diagonal-law-max-ℕ (succ-ℕ x) =
  ap succ-ℕ (left-successor-diagonal-law-max-ℕ x)

right-successor-diagonal-law-max-ℕ : (x : ℕ) → max-ℕ x (succ-ℕ x) ＝ succ-ℕ x
right-successor-diagonal-law-max-ℕ zero-ℕ = refl
right-successor-diagonal-law-max-ℕ (succ-ℕ x) =
  ap succ-ℕ (right-successor-diagonal-law-max-ℕ x)
```

### Addition distributes over `max-ℕ`

```agda
left-distributive-add-max-ℕ :
  (x y z : ℕ) → x +ℕ (max-ℕ y z) ＝ max-ℕ (x +ℕ y) (x +ℕ z)
left-distributive-add-max-ℕ zero-ℕ y z =
  ( left-unit-law-add-ℕ (max-ℕ y z)) ∙
  ( ap-max-ℕ (inv (left-unit-law-add-ℕ y)) (inv (left-unit-law-add-ℕ z)))
left-distributive-add-max-ℕ (succ-ℕ x) y z =
  ( left-successor-law-add-ℕ x (max-ℕ y z)) ∙
  ( ( ap succ-ℕ (left-distributive-add-max-ℕ x y z)) ∙
    ( ap-max-ℕ
      ( inv (left-successor-law-add-ℕ x y))
      ( inv (left-successor-law-add-ℕ x z))))

right-distributive-add-max-ℕ :
  (x y z : ℕ) → (max-ℕ x y) +ℕ z ＝ max-ℕ (x +ℕ z) (y +ℕ z)
right-distributive-add-max-ℕ x y z =
  ( commutative-add-ℕ (max-ℕ x y) z) ∙
  ( ( left-distributive-add-max-ℕ z x y) ∙
    ( ap-max-ℕ (commutative-add-ℕ z x) (commutative-add-ℕ z y)))
```

### Decide the maximum value

```agda
decide-max-ℕ :
  (m n : ℕ) → (max-ℕ m n ＝ m) + (max-ℕ m n ＝ n)
decide-max-ℕ zero-ℕ n =
  inr refl
decide-max-ℕ (succ-ℕ m) zero-ℕ =
  inl refl
decide-max-ℕ (succ-ℕ m) (succ-ℕ n) =
  map-coproduct (ap succ-ℕ) (ap succ-ℕ) (decide-max-ℕ m n)

is-left-max-ℕ :
  (m n : ℕ) → max-ℕ m n ≠ n → max-ℕ m n ＝ m
is-left-max-ℕ m n H =
  map-right-unit-law-coproduct-is-empty
    ( max-ℕ m n ＝ m)
    ( max-ℕ m n ＝ n)
    ( H)
    ( decide-max-ℕ m n)

is-right-max-ℕ :
  (m n : ℕ) → max-ℕ m n ≠ m → max-ℕ m n ＝ n
is-right-max-ℕ m n H =
  map-left-unit-law-coproduct-is-empty
    ( max-ℕ m n ＝ m)
    ( max-ℕ m n ＝ n)
    ( H)
    ( decide-max-ℕ m n)
```

### The maximum of a standard finite family of natural numbers with at least one element is attained

```agda
is-attained-max-standard-finite-family-succ-ℕ' :
  (n : ℕ) (f : Fin (succ-ℕ n) → ℕ) →
  is-decidable (max-standard-finite-family-ℕ (succ-ℕ n) f ＝ f (inr star)) →
  fiber f (max-standard-finite-family-ℕ (succ-ℕ n) f)
is-attained-max-standard-finite-family-succ-ℕ' zero-ℕ f d =
  ( inr star , refl)
is-attained-max-standard-finite-family-succ-ℕ' (succ-ℕ n) f (inl p) =
  ( inr star , inv p)
is-attained-max-standard-finite-family-succ-ℕ' (succ-ℕ n) f (inr np) =
  map-Σ
    ( λ k → f k ＝ _)
    ( inl)
    ( λ k p →
      ( p) ∙
      ( inv
        ( is-left-max-ℕ
          ( max-standard-finite-family-ℕ (succ-ℕ n) (f ∘ inl))
          ( f (inr star))
          ( np))))
    ( is-attained-max-standard-finite-family-succ-ℕ' n
      ( f ∘ inl)
      ( has-decidable-equality-ℕ _ _))

is-attained-max-standard-finite-family-succ-ℕ :
  (n : ℕ) (f : Fin (succ-ℕ n) → ℕ) →
  fiber f (max-standard-finite-family-ℕ (succ-ℕ n) f)
is-attained-max-standard-finite-family-succ-ℕ n f =
  is-attained-max-standard-finite-family-succ-ℕ' n f
    ( has-decidable-equality-ℕ _ _)
```

### The maximum of a standard finite family of natural numbers is an upper bound

```agda
is-upper-bound-max-standard-finite-family-ℕ :
  (n : ℕ) (f : Fin n → ℕ) (i : Fin n) →
  f i ≤-ℕ max-standard-finite-family-ℕ n f
is-upper-bound-max-standard-finite-family-ℕ (succ-ℕ n) f (inl x) =
  transitive-leq-ℕ
    ( f (inl x))
    ( max-standard-finite-family-ℕ n (f ∘ inl))
    ( max-standard-finite-family-ℕ (succ-ℕ n) f)
    ( left-leq-max-ℕ (max-standard-finite-family-ℕ n (f ∘ inl)) (f (inr star)))
    ( is-upper-bound-max-standard-finite-family-ℕ n (f ∘ inl) x)
is-upper-bound-max-standard-finite-family-ℕ (succ-ℕ n) f (inr star) =
  right-leq-max-ℕ (max-standard-finite-family-ℕ n (f ∘ inl)) (f (inr star))
```
