# Inequality of natural numbers

```agda
module elementary-number-theory.inequality-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
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
open import foundation.negation
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

The relation `≤` on the natural numbers is the unique relation such that `0` is
less than any natural number, and such that `m+1 ≤ n+1` is equivalent to
`m ≤ n`.

## Definitions

### Inequality on the natural numbers

```agda
leq-ℕ : ℕ → ℕ → UU lzero
leq-ℕ zero-ℕ m = unit
leq-ℕ (succ-ℕ n) zero-ℕ = empty
leq-ℕ (succ-ℕ n) (succ-ℕ m) = leq-ℕ n m

infix 30 _≤-ℕ_
_≤-ℕ_ = leq-ℕ
```

### Alternative definition of the inequality on the natural numbers

```agda
data leq-ℕ' : ℕ → ℕ → UU lzero where
  refl-leq-ℕ' : (n : ℕ) → leq-ℕ' n n
  propagate-leq-ℕ' : {x y z : ℕ} → succ-ℕ y ＝ z → (leq-ℕ' x y) → (leq-ℕ' x z)
```

## Properties

### Inequality on the natural numbers is a proposition

```agda
is-prop-leq-ℕ :
  (m n : ℕ) → is-prop (leq-ℕ m n)
is-prop-leq-ℕ zero-ℕ zero-ℕ = is-prop-unit
is-prop-leq-ℕ zero-ℕ (succ-ℕ n) = is-prop-unit
is-prop-leq-ℕ (succ-ℕ m) zero-ℕ = is-prop-empty
is-prop-leq-ℕ (succ-ℕ m) (succ-ℕ n) = is-prop-leq-ℕ m n

leq-ℕ-Prop : ℕ → ℕ → Prop lzero
pr1 (leq-ℕ-Prop m n) = leq-ℕ m n
pr2 (leq-ℕ-Prop m n) = is-prop-leq-ℕ m n
```

### Inequality on the natural numbers is decidable

```agda
is-decidable-leq-ℕ :
  (m n : ℕ) → is-decidable (leq-ℕ m n)
is-decidable-leq-ℕ zero-ℕ zero-ℕ = inl star
is-decidable-leq-ℕ zero-ℕ (succ-ℕ n) = inl star
is-decidable-leq-ℕ (succ-ℕ m) zero-ℕ = inr id
is-decidable-leq-ℕ (succ-ℕ m) (succ-ℕ n) = is-decidable-leq-ℕ m n
```

### Inequality on the natural numbers is a congruence

```agda
concatenate-eq-leq-eq-ℕ :
  {x' x y y' : ℕ} → x' ＝ x → x ≤-ℕ y → y ＝ y' → x' ≤-ℕ y'
concatenate-eq-leq-eq-ℕ refl H refl = H

concatenate-leq-eq-ℕ :
  (m : ℕ) {n n' : ℕ} → m ≤-ℕ n → n ＝ n' → m ≤-ℕ n'
concatenate-leq-eq-ℕ m H refl = H

concatenate-eq-leq-ℕ :
  {m m' : ℕ} (n : ℕ) → m' ＝ m → m ≤-ℕ n → m' ≤-ℕ n
concatenate-eq-leq-ℕ n refl H = H
```

### Inequality on the natural numbers is reflexive

```agda
refl-leq-ℕ : (n : ℕ) → n ≤-ℕ n
refl-leq-ℕ zero-ℕ = star
refl-leq-ℕ (succ-ℕ n) = refl-leq-ℕ n

leq-eq-ℕ : (m n : ℕ) → m ＝ n → m ≤-ℕ n
leq-eq-ℕ m .m refl = refl-leq-ℕ m
```

### Inequality on the natural numbers is transitive

```agda
transitive-leq-ℕ : is-transitive leq-ℕ
transitive-leq-ℕ zero-ℕ m l p q = star
transitive-leq-ℕ (succ-ℕ n) (succ-ℕ m) (succ-ℕ l) p q =
  transitive-leq-ℕ n m l p q
```

### Inequality on the natural numbers is antisymmetric

```agda
antisymmetric-leq-ℕ : (m n : ℕ) → m ≤-ℕ n → n ≤-ℕ m → m ＝ n
antisymmetric-leq-ℕ zero-ℕ zero-ℕ p q = refl
antisymmetric-leq-ℕ (succ-ℕ m) (succ-ℕ n) p q =
  ap succ-ℕ (antisymmetric-leq-ℕ m n p q)
```

### The partially ordered set of natural numbers ordered by inequality

```agda
ℕ-Preorder : Preorder lzero lzero
pr1 ℕ-Preorder = ℕ
pr1 (pr2 ℕ-Preorder) = leq-ℕ-Prop
pr1 (pr2 (pr2 ℕ-Preorder)) = refl-leq-ℕ
pr2 (pr2 (pr2 ℕ-Preorder)) = transitive-leq-ℕ

ℕ-Poset : Poset lzero lzero
pr1 ℕ-Poset = ℕ-Preorder
pr2 ℕ-Poset = antisymmetric-leq-ℕ
```

### The precategory of natural numbers ordered by inequality

```agda
ℕ-Precategory : Precategory lzero lzero
ℕ-Precategory = precategory-Preorder ℕ-Preorder
```

### For any two natural numbers we can decide which one is less than the other

```agda
linear-leq-ℕ :
  (m n : ℕ) → (m ≤-ℕ n) + (n ≤-ℕ m)
linear-leq-ℕ zero-ℕ zero-ℕ = inl star
linear-leq-ℕ zero-ℕ (succ-ℕ n) = inl star
linear-leq-ℕ (succ-ℕ m) zero-ℕ = inr star
linear-leq-ℕ (succ-ℕ m) (succ-ℕ n) = linear-leq-ℕ m n
```

### For any three natural numbers, there are three cases in how they can be ordered

```agda
cases-order-three-elements-ℕ :
  (x y z : ℕ) → UU lzero
cases-order-three-elements-ℕ x y z =
  ( ( leq-ℕ x y × leq-ℕ y z) +
    ( leq-ℕ x z × leq-ℕ z y)) +
  ( ( ( leq-ℕ y z × leq-ℕ z x) +
      ( leq-ℕ y x × leq-ℕ x z)) +
    ( ( leq-ℕ z x × leq-ℕ x y) +
      ( leq-ℕ z y × leq-ℕ y x)))

order-three-elements-ℕ :
  (x y z : ℕ) → cases-order-three-elements-ℕ x y z
order-three-elements-ℕ zero-ℕ zero-ℕ zero-ℕ =
  inl (inl (star , star))
order-three-elements-ℕ zero-ℕ zero-ℕ (succ-ℕ z) =
  inl (inl (star , star))
order-three-elements-ℕ zero-ℕ (succ-ℕ y) zero-ℕ =
  inl (inr (star , star))
order-three-elements-ℕ zero-ℕ (succ-ℕ y) (succ-ℕ z) =
  inl (map-coproduct (pair star) (pair star) (linear-leq-ℕ y z))
order-three-elements-ℕ (succ-ℕ x) zero-ℕ zero-ℕ =
  inr (inl (inl (star , star)))
order-three-elements-ℕ (succ-ℕ x) zero-ℕ (succ-ℕ z) =
  inr (inl (map-coproduct (pair star) (pair star) (linear-leq-ℕ z x)))
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) zero-ℕ =
  inr (inr (map-coproduct (pair star) (pair star) (linear-leq-ℕ x y)))
order-three-elements-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) =
  order-three-elements-ℕ x y z
```

### Zero is less than or equal to any natural number

```agda
leq-zero-ℕ :
  (n : ℕ) → zero-ℕ ≤-ℕ n
leq-zero-ℕ n = star
```

### Any natural number less than zero is zero

```agda
is-zero-leq-zero-ℕ :
  (x : ℕ) → x ≤-ℕ zero-ℕ → is-zero-ℕ x
is-zero-leq-zero-ℕ zero-ℕ star = refl

is-zero-leq-zero-ℕ' :
  (x : ℕ) → x ≤-ℕ zero-ℕ → is-zero-ℕ' x
is-zero-leq-zero-ℕ' zero-ℕ star = refl
```

### Any number is nonzero natural number if it is at least `1`

```agda
leq-one-is-nonzero-ℕ :
  (x : ℕ) → is-nonzero-ℕ x → leq-ℕ 1 x
leq-one-is-nonzero-ℕ zero-ℕ H = ex-falso (H refl)
leq-one-is-nonzero-ℕ (succ-ℕ x) H = star

is-nonzero-leq-one-ℕ :
  (x : ℕ) → leq-ℕ 1 x → is-nonzero-ℕ x
is-nonzero-leq-one-ℕ .zero-ℕ () refl
```

### Any natural number is less than or equal to its own successor

```agda
succ-leq-ℕ : (n : ℕ) → n ≤-ℕ (succ-ℕ n)
succ-leq-ℕ zero-ℕ = star
succ-leq-ℕ (succ-ℕ n) = succ-leq-ℕ n
```

### Any natural number less than or equal to `n+1` is either less than or equal to `n` or it is `n+1`

```agda
decide-leq-succ-ℕ :
  (m n : ℕ) → m ≤-ℕ (succ-ℕ n) → (m ≤-ℕ n) + (m ＝ succ-ℕ n)
decide-leq-succ-ℕ zero-ℕ zero-ℕ l = inl star
decide-leq-succ-ℕ zero-ℕ (succ-ℕ n) l = inl star
decide-leq-succ-ℕ (succ-ℕ m) zero-ℕ l =
  inr (ap succ-ℕ (is-zero-leq-zero-ℕ m l))
decide-leq-succ-ℕ (succ-ℕ m) (succ-ℕ n) l =
  map-coproduct id (ap succ-ℕ) (decide-leq-succ-ℕ m n l)
```

### If `m` is less than `n`, then it is less than `n+1`

```agda
preserves-leq-succ-ℕ :
  (m n : ℕ) → m ≤-ℕ n → m ≤-ℕ (succ-ℕ n)
preserves-leq-succ-ℕ m n p = transitive-leq-ℕ m n (succ-ℕ n) (succ-leq-ℕ n) p
```

### The successor of `n` is not less than or equal to `n`

```agda
neg-succ-leq-ℕ :
  (n : ℕ) → ¬ (leq-ℕ (succ-ℕ n) n)
neg-succ-leq-ℕ zero-ℕ = id
neg-succ-leq-ℕ (succ-ℕ n) = neg-succ-leq-ℕ n
```

### If `m ≤ n + 1` then either `m ≤ n` or `m = n + 1`

```agda
cases-leq-succ-ℕ :
  {m n : ℕ} → leq-ℕ m (succ-ℕ n) → (leq-ℕ m n) + (m ＝ succ-ℕ n)
cases-leq-succ-ℕ {zero-ℕ} {n} star = inl star
cases-leq-succ-ℕ {succ-ℕ m} {zero-ℕ} p =
  inr (ap succ-ℕ (antisymmetric-leq-ℕ m zero-ℕ p star))
cases-leq-succ-ℕ {succ-ℕ m} {succ-ℕ n} p =
  map-coproduct id (ap succ-ℕ) (cases-leq-succ-ℕ p)

cases-leq-succ-reflexive-leq-ℕ :
  {n : ℕ} → cases-leq-succ-ℕ {succ-ℕ n} {n} (refl-leq-ℕ n) ＝ inr refl
cases-leq-succ-reflexive-leq-ℕ {zero-ℕ} = refl
cases-leq-succ-reflexive-leq-ℕ {succ-ℕ n} =
  ap (map-coproduct id (ap succ-ℕ)) cases-leq-succ-reflexive-leq-ℕ
```

### `m ≤ n` if and only if `n + 1 ≰ m`

```agda
contradiction-leq-ℕ : (m n : ℕ) → m ≤-ℕ n → ¬ ((succ-ℕ n) ≤-ℕ m)
contradiction-leq-ℕ (succ-ℕ m) (succ-ℕ n) H K = contradiction-leq-ℕ m n H K

contradiction-leq-ℕ' : (m n : ℕ) → (succ-ℕ n) ≤-ℕ m → ¬ (m ≤-ℕ n)
contradiction-leq-ℕ' m n K H = contradiction-leq-ℕ m n H K
```

### Addition preserves inequality of natural numbers

```agda
preserves-leq-left-add-ℕ :
  (k m n : ℕ) → m ≤-ℕ n → (m +ℕ k) ≤-ℕ (n +ℕ k)
preserves-leq-left-add-ℕ zero-ℕ m n = id
preserves-leq-left-add-ℕ (succ-ℕ k) m n H = preserves-leq-left-add-ℕ k m n H

preserves-leq-right-add-ℕ : (k m n : ℕ) → m ≤-ℕ n → (k +ℕ m) ≤-ℕ (k +ℕ n)
preserves-leq-right-add-ℕ k m n H =
  concatenate-eq-leq-eq-ℕ
    ( commutative-add-ℕ k m)
    ( preserves-leq-left-add-ℕ k m n H)
    ( commutative-add-ℕ n k)

preserves-leq-add-ℕ :
  {m m' n n' : ℕ} → m ≤-ℕ m' → n ≤-ℕ n' → (m +ℕ n) ≤-ℕ (m' +ℕ n')
preserves-leq-add-ℕ {m} {m'} {n} {n'} H K =
  transitive-leq-ℕ
    ( m +ℕ n)
    ( m' +ℕ n)
    ( m' +ℕ n')
    ( preserves-leq-right-add-ℕ m' n n' K)
    ( preserves-leq-left-add-ℕ n m m' H)
```

### Addition reflects inequality of natural numbers

```agda
reflects-leq-left-add-ℕ :
  (k m n : ℕ) → (m +ℕ k) ≤-ℕ (n +ℕ k) → m ≤-ℕ n
reflects-leq-left-add-ℕ zero-ℕ m n = id
reflects-leq-left-add-ℕ (succ-ℕ k) m n = reflects-leq-left-add-ℕ k m n

reflects-leq-right-add-ℕ :
  (k m n : ℕ) → (k +ℕ m) ≤-ℕ (k +ℕ n) → m ≤-ℕ n
reflects-leq-right-add-ℕ k m n H =
  reflects-leq-left-add-ℕ k m n
    ( concatenate-eq-leq-eq-ℕ
      ( commutative-add-ℕ m k)
      ( H)
      ( commutative-add-ℕ k n))
```

### `m ≤ m + n` for any two natural numbers `m` and `n`

```agda
leq-add-ℕ : (m n : ℕ) → m ≤-ℕ (m +ℕ n)
leq-add-ℕ m zero-ℕ = refl-leq-ℕ m
leq-add-ℕ m (succ-ℕ n) =
  transitive-leq-ℕ
    ( m)
    ( m +ℕ n)
    ( succ-ℕ (m +ℕ n))
    ( succ-leq-ℕ (m +ℕ n))
    ( leq-add-ℕ m n)

leq-add-ℕ' : (m n : ℕ) → m ≤-ℕ (n +ℕ m)
leq-add-ℕ' m n =
  concatenate-leq-eq-ℕ m (leq-add-ℕ m n) (commutative-add-ℕ m n)
```

### We have `n ≤ m` if and only if there is a number `l` such that `l+n=m`

```agda
subtraction-leq-ℕ : (n m : ℕ) → n ≤-ℕ m → Σ ℕ (λ l → l +ℕ n ＝ m)
subtraction-leq-ℕ zero-ℕ m p = (m , refl)
subtraction-leq-ℕ (succ-ℕ n) (succ-ℕ m) p = (pr1 P , ap succ-ℕ (pr2 P))
  where
  P : Σ ℕ (λ l' → l' +ℕ n ＝ m)
  P = subtraction-leq-ℕ n m p

leq-subtraction-ℕ : (n m l : ℕ) → l +ℕ n ＝ m → n ≤-ℕ m
leq-subtraction-ℕ zero-ℕ m l p = leq-zero-ℕ m
leq-subtraction-ℕ (succ-ℕ n) (succ-ℕ m) l p =
  leq-subtraction-ℕ n m l (is-injective-succ-ℕ p)
```

### Multiplication preserves inequality of natural numbers

```agda
preserves-leq-left-mul-ℕ :
  (k m n : ℕ) → m ≤-ℕ n → (m *ℕ k) ≤-ℕ (n *ℕ k)
preserves-leq-left-mul-ℕ k zero-ℕ n p = star
preserves-leq-left-mul-ℕ k (succ-ℕ m) (succ-ℕ n) p =
  preserves-leq-left-add-ℕ k
    ( m *ℕ k)
    ( n *ℕ k)
    ( preserves-leq-left-mul-ℕ k m n p)

preserves-leq-right-mul-ℕ :
  (k m n : ℕ) → m ≤-ℕ n → (k *ℕ m) ≤-ℕ (k *ℕ n)
preserves-leq-right-mul-ℕ k m n H =
  concatenate-eq-leq-eq-ℕ
    ( commutative-mul-ℕ k m)
    ( preserves-leq-left-mul-ℕ k m n H)
    ( commutative-mul-ℕ n k)

preserves-leq-mul-ℕ :
  (m m' n n' : ℕ) → m ≤-ℕ m' → n ≤-ℕ n' → (m *ℕ n) ≤-ℕ (m' *ℕ n')
preserves-leq-mul-ℕ m m' n n' H K =
  transitive-leq-ℕ
    ( m *ℕ n)
    ( m' *ℕ n)
    ( m' *ℕ n')
    ( preserves-leq-right-mul-ℕ m' n n' K)
    ( preserves-leq-left-mul-ℕ n m m' H)
```

### Multiplication by a nonzero natural number reflects inequality of natural numbers

```agda
reflects-order-mul-ℕ :
  (k m n : ℕ) → (m *ℕ (succ-ℕ k)) ≤-ℕ (n *ℕ (succ-ℕ k)) → m ≤-ℕ n
reflects-order-mul-ℕ k zero-ℕ n p = star
reflects-order-mul-ℕ k (succ-ℕ m) (succ-ℕ n) p =
  reflects-order-mul-ℕ k m n
    ( reflects-leq-left-add-ℕ
      ( succ-ℕ k)
      ( m *ℕ (succ-ℕ k))
      ( n *ℕ (succ-ℕ k))
      ( p))

reflects-order-mul-ℕ' :
  (k m n : ℕ) → ((succ-ℕ k) *ℕ m) ≤-ℕ ((succ-ℕ k) *ℕ n) → m ≤-ℕ n
reflects-order-mul-ℕ' k m n H =
  reflects-order-mul-ℕ k m n
    ( concatenate-eq-leq-eq-ℕ
      ( commutative-mul-ℕ m (succ-ℕ k))
      ( H)
      ( commutative-mul-ℕ (succ-ℕ k) n))
```

### Any number `x` is less than or equal to a nonzero multiple of itself

```agda
leq-mul-ℕ :
  (k x : ℕ) → x ≤-ℕ (x *ℕ (succ-ℕ k))
leq-mul-ℕ k x =
  concatenate-eq-leq-ℕ
    ( x *ℕ (succ-ℕ k))
    ( inv (right-unit-law-mul-ℕ x))
    ( preserves-leq-right-mul-ℕ x 1 (succ-ℕ k) (leq-zero-ℕ k))

leq-mul-ℕ' :
  (k x : ℕ) → x ≤-ℕ ((succ-ℕ k) *ℕ x)
leq-mul-ℕ' k x =
  concatenate-leq-eq-ℕ x
    ( leq-mul-ℕ k x)
    ( commutative-mul-ℕ x (succ-ℕ k))

leq-mul-is-nonzero-ℕ :
  (k x : ℕ) → is-nonzero-ℕ k → x ≤-ℕ (x *ℕ k)
leq-mul-is-nonzero-ℕ k x H with is-successor-is-nonzero-ℕ H
... | (l , refl) = leq-mul-ℕ l x

leq-mul-is-nonzero-ℕ' :
  (k x : ℕ) → is-nonzero-ℕ k → x ≤-ℕ (k *ℕ x)
leq-mul-is-nonzero-ℕ' k x H with is-successor-is-nonzero-ℕ H
... | (l , refl) = leq-mul-ℕ' l x
```

## See also

- Strict inequality of the natural numbers is defined in
  [`strict-inequality-natural-numbers`](elementary-number-theory.strict-inequality-natural-numbers.md)
