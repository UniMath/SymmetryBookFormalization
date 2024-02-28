# Strict inequality of natural numbers

```agda
module elementary-number-theory.strict-inequality-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Definition

### The strict ordering of the natural numbers

```agda
le-ℕ-Prop : ℕ → ℕ → Prop lzero
le-ℕ-Prop m zero-ℕ = empty-Prop
le-ℕ-Prop zero-ℕ (succ-ℕ m) = unit-Prop
le-ℕ-Prop (succ-ℕ n) (succ-ℕ m) = le-ℕ-Prop n m

le-ℕ : ℕ → ℕ → UU lzero
le-ℕ n m = type-Prop (le-ℕ-Prop n m)

is-prop-le-ℕ : (n : ℕ) → (m : ℕ) → is-prop (le-ℕ n m)
is-prop-le-ℕ n m = is-prop-type-Prop (le-ℕ-Prop n m)

infix 30 _<-ℕ_
_<-ℕ_ = le-ℕ
```

## Properties

### If `x` is less than `y`, then `x` is less than or equal to `y`

```agda
leq-le-ℕ :
  (x y : ℕ) → x <ℕ y → x ≤ℕ y
leq-le-ℕ zero-ℕ (succ-ℕ y) H = star
leq-le-ℕ (succ-ℕ x) (succ-ℕ y) H = leq-le-ℕ x y H
```

### Concatenating strict inequalities and equalities

```agda
concatenate-eq-le-eq-ℕ :
  {x y z w : ℕ} → x ＝ y → y <ℕ z → z ＝ w → x <ℕ w
concatenate-eq-le-eq-ℕ refl p refl = p

concatenate-eq-le-ℕ :
  {x y z : ℕ} → x ＝ y → y <ℕ z → x <ℕ z
concatenate-eq-le-ℕ refl p = p

concatenate-le-eq-ℕ :
  {x y z : ℕ} → x <ℕ y → y ＝ z → x <ℕ z
concatenate-le-eq-ℕ p refl = p
```

### Strict inequality is decidable

```agda
is-decidable-le-ℕ :
  (m n : ℕ) → is-decidable (m <ℕ n)
is-decidable-le-ℕ zero-ℕ zero-ℕ = inr id
is-decidable-le-ℕ zero-ℕ (succ-ℕ n) = inl star
is-decidable-le-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-le-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-le-ℕ m n
```

### If `m < n` then `n` must be nonzero

```agda
is-nonzero-le-ℕ : (m n : ℕ) → m <ℕ n → is-nonzero-ℕ n
is-nonzero-le-ℕ m .zero-ℕ () refl
```

### Any nonzero natural number is strictly greater than `0`

```agda
le-is-nonzero-ℕ : (n : ℕ) → is-nonzero-ℕ n → le-ℕ zero-ℕ n
le-is-nonzero-ℕ zero-ℕ H = H refl
le-is-nonzero-ℕ (succ-ℕ n) H = star
```

### No natural number is strictly less than zero

```agda
contradiction-le-zero-ℕ :
  (m : ℕ) → (m <ℕ zero-ℕ) → empty
contradiction-le-zero-ℕ zero-ℕ ()
contradiction-le-zero-ℕ (succ-ℕ m) ()
```

### No successor is strictly less than one

```agda
contradiction-le-one-ℕ :
  (n : ℕ) → succ-ℕ n <ℕ 1 → empty
contradiction-le-one-ℕ zero-ℕ ()
contradiction-le-one-ℕ (succ-ℕ n) ()
```

### The strict ordering of the natural numbers is irreflexive

```agda
irreflexive-le-ℕ : is-irreflexive _<-ℕ_
irreflexive-le-ℕ zero-ℕ ()
irreflexive-le-ℕ (succ-ℕ n) = irreflexive-le-ℕ n
```

### If `x < y` then `x ≠ y`

```agda
neq-le-ℕ : {x y : ℕ} → x <ℕ y → x ≠ y
neq-le-ℕ {zero-ℕ} {succ-ℕ y} H = is-nonzero-succ-ℕ y ∘ inv
neq-le-ℕ {succ-ℕ x} {succ-ℕ y} H p = neq-le-ℕ H (is-injective-succ-ℕ p)
```

### Strict inequality is antisymmetric

```agda
antisymmetric-le-ℕ : is-antisymmetric _<-ℕ_
antisymmetric-le-ℕ (succ-ℕ m) (succ-ℕ n) p q =
  ap succ-ℕ (antisymmetric-le-ℕ m n p q)
```

### The strict ordering of the natural numbers is transitive

```agda
transitive-le-ℕ : (n m l : ℕ) → n <ℕ m → m <ℕ l → n <ℕ l
transitive-le-ℕ zero-ℕ (succ-ℕ m) (succ-ℕ l) p q = star
transitive-le-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q =
  transitive-le-ℕ n m l p q
```

### A sharper variant of transitivity

```agda
transitive-le-ℕ' :
  (k l m : ℕ) → k <ℕ l → l <ℕ succ-ℕ m → k <ℕ m
transitive-le-ℕ' zero-ℕ zero-ℕ m () s
transitive-le-ℕ' (succ-ℕ k) zero-ℕ m () s
transitive-le-ℕ' zero-ℕ (succ-ℕ l) zero-ℕ star s =
  ex-falso (contradiction-le-one-ℕ l s)
transitive-le-ℕ' (succ-ℕ k) (succ-ℕ l) zero-ℕ t s =
  ex-falso (contradiction-le-one-ℕ l s)
transitive-le-ℕ' zero-ℕ (succ-ℕ l) (succ-ℕ m) star s = star
transitive-le-ℕ' (succ-ℕ k) (succ-ℕ l) (succ-ℕ m) t s =
  transitive-le-ℕ' k l m t s
```

### Strict inequality is linear

```agda
linear-le-ℕ : (x y : ℕ) → (x <ℕ y) + (x ＝ y) + (y <ℕ x)
linear-le-ℕ zero-ℕ zero-ℕ = inr (inl refl)
linear-le-ℕ zero-ℕ (succ-ℕ y) = inl star
linear-le-ℕ (succ-ℕ x) zero-ℕ = inr (inr star)
linear-le-ℕ (succ-ℕ x) (succ-ℕ y) =
  map-coproduct id (map-coproduct (ap succ-ℕ) id) (linear-le-ℕ x y)
```

### `n < m` if and only if there exists a nonzero natural number `l` such that `n + l = m`

```agda
subtraction-le-ℕ :
  (n m : ℕ) → n <ℕ m → Σ ℕ (λ l → (is-nonzero-ℕ l) × (l +ℕ n ＝ m))
subtraction-le-ℕ zero-ℕ m p = pair m (pair (is-nonzero-le-ℕ zero-ℕ m p) refl)
subtraction-le-ℕ (succ-ℕ n) (succ-ℕ m) p =
  pair (pr1 P) (pair (pr1 (pr2 P)) (ap succ-ℕ (pr2 (pr2 P))))
  where
  P : Σ ℕ (λ l' → (is-nonzero-ℕ l') × (l' +ℕ n ＝ m))
  P = subtraction-le-ℕ n m p

le-subtraction-ℕ : (n m l : ℕ) → is-nonzero-ℕ l → l +ℕ n ＝ m → n <ℕ m
le-subtraction-ℕ zero-ℕ m l q p =
  tr (λ x → le-ℕ zero-ℕ x) p (le-is-nonzero-ℕ l q)
le-subtraction-ℕ (succ-ℕ n) (succ-ℕ m) l q p =
  le-subtraction-ℕ n m l q (is-injective-succ-ℕ p)
```

### Any natural number is strictly less than its successor

```agda
succ-le-ℕ : (n : ℕ) → n <ℕ (succ-ℕ n)
succ-le-ℕ zero-ℕ = star
succ-le-ℕ (succ-ℕ n) = succ-le-ℕ n
```

### The successor function preserves strict inequality on the right

```agda
preserves-le-succ-ℕ :
  (m n : ℕ) → m <ℕ n → m <ℕ (succ-ℕ n)
preserves-le-succ-ℕ m n H =
  transitive-le-ℕ m n (succ-ℕ n) H (succ-le-ℕ n)
```

### Concatenating strict and nonstrict inequalities

```agda
concatenate-leq-le-ℕ :
  {x y z : ℕ} → x ≤ℕ y → y <ℕ z → x <ℕ z
concatenate-leq-le-ℕ {zero-ℕ} {zero-ℕ} {succ-ℕ z} H K = star
concatenate-leq-le-ℕ {zero-ℕ} {succ-ℕ y} {succ-ℕ z} H K = star
concatenate-leq-le-ℕ {succ-ℕ x} {succ-ℕ y} {succ-ℕ z} H K =
  concatenate-leq-le-ℕ {x} {y} {z} H K

concatenate-le-leq-ℕ :
  {x y z : ℕ} → x <ℕ y → y ≤ℕ z → x <ℕ z
concatenate-le-leq-ℕ {zero-ℕ} {succ-ℕ y} {succ-ℕ z} H K = star
concatenate-le-leq-ℕ {succ-ℕ x} {succ-ℕ y} {succ-ℕ z} H K =
  concatenate-le-leq-ℕ {x} {y} {z} H K
```

### If `m < n` then `n ≰ m`

```agda
contradiction-le-ℕ : (m n : ℕ) → m <ℕ n → ¬ (n ≤ℕ m)
contradiction-le-ℕ zero-ℕ (succ-ℕ n) H K = K
contradiction-le-ℕ (succ-ℕ m) (succ-ℕ n) H = contradiction-le-ℕ m n H
```

### If `n ≤ m` then `m ≮ n`

```agda
contradiction-le-ℕ' : (m n : ℕ) → n ≤ℕ m → ¬ (m <ℕ n)
contradiction-le-ℕ' m n K H = contradiction-le-ℕ m n H K
```

### If `m ≮ n` then `n ≤ m`

```agda
leq-not-le-ℕ : (m n : ℕ) → ¬ (m <ℕ n) → n ≤ℕ m
leq-not-le-ℕ zero-ℕ zero-ℕ H = star
leq-not-le-ℕ zero-ℕ (succ-ℕ n) H = ex-falso (H star)
leq-not-le-ℕ (succ-ℕ m) zero-ℕ H = star
leq-not-le-ℕ (succ-ℕ m) (succ-ℕ n) H = leq-not-le-ℕ m n H
```

### If `x < y + 1` then `x ≤ y`

```agda
leq-le-succ-ℕ :
  (x y : ℕ) → x <ℕ (succ-ℕ y) → x ≤ℕ y
leq-le-succ-ℕ zero-ℕ y H = star
leq-le-succ-ℕ (succ-ℕ x) (succ-ℕ y) H = leq-le-succ-ℕ x y H
```

### If `x < y` then `x + 1 ≤ y`

```agda
leq-succ-le-ℕ :
  (x y : ℕ) → x <ℕ y → succ-ℕ x ≤ℕ y
leq-succ-le-ℕ zero-ℕ (succ-ℕ y) H = star
leq-succ-le-ℕ (succ-ℕ x) (succ-ℕ y) H = leq-succ-le-ℕ x y H
```

### If `x ≤ y` then `x < y + 1`

```agda
le-succ-leq-ℕ :
  (x y : ℕ) → leq-ℕ x y → x <ℕ (succ-ℕ y)
le-succ-leq-ℕ zero-ℕ zero-ℕ H = star
le-succ-leq-ℕ zero-ℕ (succ-ℕ y) H = star
le-succ-leq-ℕ (succ-ℕ x) (succ-ℕ y) H = le-succ-leq-ℕ x y H
```

### `x ≤ y` if and only if `(x ＝ y) + (x < y)`

```agda
eq-or-le-leq-ℕ :
  (x y : ℕ) → leq-ℕ x y → (x ＝ y) + (x <ℕ y)
eq-or-le-leq-ℕ zero-ℕ zero-ℕ H = inl refl
eq-or-le-leq-ℕ zero-ℕ (succ-ℕ y) H = inr star
eq-or-le-leq-ℕ (succ-ℕ x) (succ-ℕ y) H =
  map-coproduct (ap succ-ℕ) id (eq-or-le-leq-ℕ x y H)

eq-or-le-leq-ℕ' :
  (x y : ℕ) → leq-ℕ x y → (y ＝ x) + (x <ℕ y)
eq-or-le-leq-ℕ' x y H = map-coproduct inv id (eq-or-le-leq-ℕ x y H)

leq-eq-or-le-ℕ :
  (x y : ℕ) → (x ＝ y) + (x <ℕ y) → leq-ℕ x y
leq-eq-or-le-ℕ x .x (inl refl) = refl-leq-ℕ x
leq-eq-or-le-ℕ x y (inr l) = leq-le-ℕ x y l
```

### If `x ≤ y` and `x ≠ y` then `x < y`

```agda
le-leq-neq-ℕ : {x y : ℕ} → x ≤ℕ y → x ≠ y → x <ℕ y
le-leq-neq-ℕ {zero-ℕ} {zero-ℕ} l f = ex-falso (f refl)
le-leq-neq-ℕ {zero-ℕ} {succ-ℕ y} l f = star
le-leq-neq-ℕ {succ-ℕ x} {succ-ℕ y} l f =
  le-leq-neq-ℕ {x} {y} l (λ p → f (ap succ-ℕ p))
```
