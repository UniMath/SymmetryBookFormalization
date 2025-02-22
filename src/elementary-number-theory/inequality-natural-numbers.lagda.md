# Inequality of natural numbers

```agda
module elementary-number-theory.inequality-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositions
open import foundation.sections
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
  (m n : ℕ) → is-prop (m ≤-ℕ n)
is-prop-leq-ℕ zero-ℕ zero-ℕ = is-prop-unit
is-prop-leq-ℕ zero-ℕ (succ-ℕ n) = is-prop-unit
is-prop-leq-ℕ (succ-ℕ m) zero-ℕ = is-prop-empty
is-prop-leq-ℕ (succ-ℕ m) (succ-ℕ n) = is-prop-leq-ℕ m n

leq-ℕ-Prop : ℕ → ℕ → Prop lzero
pr1 (leq-ℕ-Prop m n) = leq-ℕ m n
pr2 (leq-ℕ-Prop m n) = is-prop-leq-ℕ m n

is-proof-irrelevant-leq-ℕ :
  (m n : ℕ) → m ≤-ℕ n → is-contr (m ≤-ℕ n)
is-proof-irrelevant-leq-ℕ m n =
  is-proof-irrelevant-is-prop (is-prop-leq-ℕ m n)
```

### Inequality on the natural numbers is decidable

```agda
is-decidable-leq-ℕ :
  (m n : ℕ) → is-decidable (m ≤-ℕ n)
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
transitive-leq-ℕ : is-transitive _≤-ℕ_
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
  ( x ≤-ℕ y × y ≤-ℕ z + x ≤-ℕ z × z ≤-ℕ y) +
  ( ( y ≤-ℕ z × z ≤-ℕ x + y ≤-ℕ x × x ≤-ℕ z) +
    ( z ≤-ℕ x × x ≤-ℕ y + z ≤-ℕ y × y ≤-ℕ x))

order-three-elements-ℕ :
  (x y z : ℕ) → cases-order-three-elements-ℕ x y z
order-three-elements-ℕ zero-ℕ zero-ℕ zero-ℕ = inl (inl (star , star))
order-three-elements-ℕ zero-ℕ zero-ℕ (succ-ℕ z) = inl (inl (star , star))
order-three-elements-ℕ zero-ℕ (succ-ℕ y) zero-ℕ = inl (inr (star , star))
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
  (n : ℕ) → 0 ≤-ℕ n
leq-zero-ℕ n = star

leq-is-zero-ℕ :
  (m n : ℕ) → is-zero-ℕ m → m ≤-ℕ n
leq-is-zero-ℕ .zero-ℕ n refl = leq-zero-ℕ n
```

### Any natural number less than zero is zero

```agda
is-zero-leq-zero-ℕ :
  (x : ℕ) → x ≤-ℕ 0 → is-zero-ℕ x
is-zero-leq-zero-ℕ zero-ℕ star = refl

is-zero-leq-zero-ℕ' :
  (x : ℕ) → x ≤-ℕ 0 → is-zero-ℕ' x
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
succ-leq-ℕ : (n : ℕ) → n ≤-ℕ succ-ℕ n
succ-leq-ℕ zero-ℕ = star
succ-leq-ℕ (succ-ℕ n) = succ-leq-ℕ n
```

### If `m` is less than `n`, then it is less than `n+1`

```agda
leq-succ-leq-ℕ :
  (m n : ℕ) → m ≤-ℕ n → m ≤-ℕ succ-ℕ n
leq-succ-leq-ℕ m n p = transitive-leq-ℕ m n (succ-ℕ n) (succ-leq-ℕ n) p
```

### The successor of `n` is not less than or equal to `n`

```agda
neg-succ-leq-ℕ :
  (n : ℕ) → ¬ (succ-ℕ n ≤-ℕ n)
neg-succ-leq-ℕ zero-ℕ = id
neg-succ-leq-ℕ (succ-ℕ n) = neg-succ-leq-ℕ n
```

### `m ≤ n` if and only if `n + 1 ≰ m`

```agda
contradiction-leq-ℕ : (m n : ℕ) → m ≤-ℕ n → ¬ (succ-ℕ n ≤-ℕ m)
contradiction-leq-ℕ (succ-ℕ m) (succ-ℕ n) H K = contradiction-leq-ℕ m n H K

contradiction-leq-ℕ' : (m n : ℕ) → succ-ℕ n ≤-ℕ m → ¬ (m ≤-ℕ n)
contradiction-leq-ℕ' m n K H = contradiction-leq-ℕ m n H K
```

### Any natural number less than or equal to `n+1` is either less than or equal to `n` or it is `n+1`

```agda
decide-leq-succ-ℕ :
  (m n : ℕ) → m ≤-ℕ succ-ℕ n → (m ≤-ℕ n) + (m ＝ succ-ℕ n)
decide-leq-succ-ℕ zero-ℕ zero-ℕ l = inl star
decide-leq-succ-ℕ zero-ℕ (succ-ℕ n) l = inl star
decide-leq-succ-ℕ (succ-ℕ m) zero-ℕ l =
  inr (ap succ-ℕ (is-zero-leq-zero-ℕ m l))
decide-leq-succ-ℕ (succ-ℕ m) (succ-ℕ n) l =
  map-coproduct id (ap succ-ℕ) (decide-leq-succ-ℕ m n l)

inv-decide-leq-succ-ℕ :
  (m n : ℕ) → (m ≤-ℕ n) + (m ＝ succ-ℕ n) → m ≤-ℕ succ-ℕ n
inv-decide-leq-succ-ℕ m n (inl H) =
  transitive-leq-ℕ m n (succ-ℕ n) (leq-succ-leq-ℕ n n (refl-leq-ℕ n)) H
inv-decide-leq-succ-ℕ m n (inr p) =
  leq-eq-ℕ m (succ-ℕ n) p

all-elements-equal-cases-leq-succ-ℕ :
  (m n : ℕ) → all-elements-equal ((m ≤-ℕ n) + (m ＝ succ-ℕ n))
all-elements-equal-cases-leq-succ-ℕ m n (inl H) (inl K) =
  ap inl (eq-is-prop (is-prop-leq-ℕ m n))
all-elements-equal-cases-leq-succ-ℕ .(succ-ℕ n) n (inl H) (inr refl) =
  ex-falso (neg-succ-leq-ℕ n H)
all-elements-equal-cases-leq-succ-ℕ .(succ-ℕ n) n (inr refl) (inl K) =
  ex-falso (neg-succ-leq-ℕ n K)
all-elements-equal-cases-leq-succ-ℕ .(succ-ℕ n) n (inr refl) (inr q) =
  ap inr (eq-is-prop (is-set-ℕ (succ-ℕ n) (succ-ℕ n)))

is-prop-cases-leq-succ-ℕ :
  (m n : ℕ) → is-prop ((m ≤-ℕ n) + (m ＝ succ-ℕ n))
is-prop-cases-leq-succ-ℕ m n =
  is-prop-all-elements-equal (all-elements-equal-cases-leq-succ-ℕ m n)

compute-leq-succ-ℕ :
  (m n : ℕ) → m ≤-ℕ succ-ℕ n ≃ (m ≤-ℕ n) + (m ＝ succ-ℕ n)
compute-leq-succ-ℕ m n =
  equiv-iff-is-prop
    ( is-prop-leq-ℕ m (succ-ℕ n))
    ( is-prop-cases-leq-succ-ℕ m n)
    ( decide-leq-succ-ℕ m n)
    ( inv-decide-leq-succ-ℕ m n)

decide-leq-refl-succ-ℕ :
  {n : ℕ} → decide-leq-succ-ℕ (succ-ℕ n) n (refl-leq-ℕ n) ＝ inr refl
decide-leq-refl-succ-ℕ {zero-ℕ} = refl
decide-leq-refl-succ-ℕ {succ-ℕ n} =
  ap (map-coproduct id (ap succ-ℕ)) decide-leq-refl-succ-ℕ
```

### The inequality `m ≤ n` holds if and only if either `m ＝ n` or the inequality `m + 1 ≤ n` holds

```agda
decide-leq-ℕ :
  (m n : ℕ) → m ≤-ℕ n → (m ＝ n) + (succ-ℕ m ≤-ℕ n)
decide-leq-ℕ m zero-ℕ H = inl (is-zero-leq-zero-ℕ m H)
decide-leq-ℕ zero-ℕ (succ-ℕ n) H = inr (leq-zero-ℕ n)
decide-leq-ℕ (succ-ℕ m) (succ-ℕ n) H =
  map-coproduct (ap succ-ℕ) id (decide-leq-ℕ m n H)
```

### Addition preserves inequality of natural numbers

```agda
preserves-order-left-add-ℕ :
  (k m n : ℕ) → m ≤-ℕ n → m +ℕ k ≤-ℕ n +ℕ k
preserves-order-left-add-ℕ zero-ℕ m n = id
preserves-order-left-add-ℕ (succ-ℕ k) m n H = preserves-order-left-add-ℕ k m n H

preserves-order-right-add-ℕ : (k m n : ℕ) → m ≤-ℕ n → k +ℕ m ≤-ℕ k +ℕ n
preserves-order-right-add-ℕ k m n H =
  concatenate-eq-leq-eq-ℕ
    ( commutative-add-ℕ k m)
    ( preserves-order-left-add-ℕ k m n H)
    ( commutative-add-ℕ n k)

preserves-order-add-ℕ :
  {m m' n n' : ℕ} → m ≤-ℕ m' → n ≤-ℕ n' → m +ℕ n ≤-ℕ m' +ℕ n'
preserves-order-add-ℕ {m} {m'} {n} {n'} H K =
  transitive-leq-ℕ
    ( m +ℕ n)
    ( m' +ℕ n)
    ( m' +ℕ n')
    ( preserves-order-right-add-ℕ m' n n' K)
    ( preserves-order-left-add-ℕ n m m' H)
```

### Addition reflects inequality of natural numbers

```agda
reflects-order-left-add-ℕ :
  (k m n : ℕ) → m +ℕ k ≤-ℕ n +ℕ k → m ≤-ℕ n
reflects-order-left-add-ℕ zero-ℕ m n = id
reflects-order-left-add-ℕ (succ-ℕ k) m n = reflects-order-left-add-ℕ k m n

reflects-order-right-add-ℕ :
  (k m n : ℕ) → k +ℕ m ≤-ℕ k +ℕ n → m ≤-ℕ n
reflects-order-right-add-ℕ k m n H =
  reflects-order-left-add-ℕ k m n
    ( concatenate-eq-leq-eq-ℕ
      ( commutative-add-ℕ m k)
      ( H)
      ( commutative-add-ℕ k n))
```

### `m ≤ m + n` for any two natural numbers `m` and `n`

```agda
leq-add-ℕ : (m n : ℕ) → m ≤-ℕ m +ℕ n
leq-add-ℕ m zero-ℕ = refl-leq-ℕ m
leq-add-ℕ m (succ-ℕ n) =
  transitive-leq-ℕ
    ( m)
    ( m +ℕ n)
    ( succ-ℕ (m +ℕ n))
    ( succ-leq-ℕ (m +ℕ n))
    ( leq-add-ℕ m n)

leq-add-ℕ' : (m n : ℕ) → m ≤-ℕ n +ℕ m
leq-add-ℕ' m n =
  concatenate-leq-eq-ℕ m (leq-add-ℕ m n) (commutative-add-ℕ m n)
```

### If `m + n ≤ k`, then both `m ≤ k` and `n ≤ k` hold

```agda
leq-right-summand-ℕ :
  (m n k : ℕ) → m +ℕ n ≤-ℕ k → n ≤-ℕ k
leq-right-summand-ℕ m n k H =
  transitive-leq-ℕ n (m +ℕ n) k H (leq-add-ℕ' n m)

leq-left-summand-ℕ :
  (m n k : ℕ) → m +ℕ n ≤-ℕ k → m ≤-ℕ k
leq-left-summand-ℕ m n k H =
  transitive-leq-ℕ m (m +ℕ n) k H (leq-add-ℕ m n)
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
preserves-order-left-mul-ℕ :
  (k m n : ℕ) → m ≤-ℕ n → m *ℕ k ≤-ℕ n *ℕ k
preserves-order-left-mul-ℕ k zero-ℕ n p = star
preserves-order-left-mul-ℕ k (succ-ℕ m) (succ-ℕ n) p =
  preserves-order-left-add-ℕ k
    ( m *ℕ k)
    ( n *ℕ k)
    ( preserves-order-left-mul-ℕ k m n p)

preserves-order-right-mul-ℕ :
  (k m n : ℕ) → m ≤-ℕ n → k *ℕ m ≤-ℕ k *ℕ n
preserves-order-right-mul-ℕ k m n H =
  concatenate-eq-leq-eq-ℕ
    ( commutative-mul-ℕ k m)
    ( preserves-order-left-mul-ℕ k m n H)
    ( commutative-mul-ℕ n k)

preserves-order-mul-ℕ :
  (m m' n n' : ℕ) → m ≤-ℕ m' → n ≤-ℕ n' → m *ℕ n ≤-ℕ m' *ℕ n'
preserves-order-mul-ℕ m m' n n' H K =
  transitive-leq-ℕ
    ( m *ℕ n)
    ( m' *ℕ n)
    ( m' *ℕ n')
    ( preserves-order-right-mul-ℕ m' n n' K)
    ( preserves-order-left-mul-ℕ n m m' H)
```

### Multiplication by a nonzero natural number reflects inequality of natural numbers

```agda
reflects-order-mul-succ-ℕ :
  (k m n : ℕ) → m *ℕ succ-ℕ k ≤-ℕ n *ℕ succ-ℕ k → m ≤-ℕ n
reflects-order-mul-succ-ℕ k zero-ℕ n p = star
reflects-order-mul-succ-ℕ k (succ-ℕ m) (succ-ℕ n) p =
  reflects-order-mul-succ-ℕ k m n
    ( reflects-order-left-add-ℕ
      ( succ-ℕ k)
      ( m *ℕ (succ-ℕ k))
      ( n *ℕ (succ-ℕ k))
      ( p))

reflects-order-mul-succ-ℕ' :
  (k m n : ℕ) → succ-ℕ k *ℕ m ≤-ℕ succ-ℕ k *ℕ n → m ≤-ℕ n
reflects-order-mul-succ-ℕ' k m n H =
  reflects-order-mul-succ-ℕ k m n
    ( concatenate-eq-leq-eq-ℕ
      ( commutative-mul-ℕ m (succ-ℕ k))
      ( H)
      ( commutative-mul-ℕ (succ-ℕ k) n))

reflects-order-mul-ℕ :
  (k m n : ℕ) → is-nonzero-ℕ k → m *ℕ k ≤-ℕ n *ℕ k → m ≤-ℕ n
reflects-order-mul-ℕ k m n H with
  is-successor-is-nonzero-ℕ H
... | (k' , refl) = reflects-order-mul-succ-ℕ k' m n

reflects-order-mul-ℕ' :
  (k m n : ℕ) → is-nonzero-ℕ k → k *ℕ m ≤-ℕ k *ℕ n → m ≤-ℕ n
reflects-order-mul-ℕ' k m n H K =
  reflects-order-mul-ℕ k m n H
    ( concatenate-eq-leq-eq-ℕ
      ( commutative-mul-ℕ m k)
      ( K)
      ( commutative-mul-ℕ k n))
```

### Any number `x` is less than or equal to a nonzero multiple of itself

```agda
leq-mul-ℕ :
  (k x : ℕ) → x ≤-ℕ x *ℕ succ-ℕ k
leq-mul-ℕ k x =
  concatenate-eq-leq-ℕ
    ( x *ℕ succ-ℕ k)
    ( inv (right-unit-law-mul-ℕ x))
    ( preserves-order-right-mul-ℕ x 1 (succ-ℕ k) (leq-zero-ℕ k))

leq-mul-ℕ' :
  (k x : ℕ) → x ≤-ℕ succ-ℕ k *ℕ x
leq-mul-ℕ' k x =
  concatenate-leq-eq-ℕ x
    ( leq-mul-ℕ k x)
    ( commutative-mul-ℕ x (succ-ℕ k))

leq-mul-is-nonzero-ℕ :
  (k x : ℕ) → is-nonzero-ℕ k → x ≤-ℕ x *ℕ k
leq-mul-is-nonzero-ℕ k x H with is-successor-is-nonzero-ℕ H
... | (l , refl) = leq-mul-ℕ l x

leq-mul-is-nonzero-ℕ' :
  (k x : ℕ) → is-nonzero-ℕ k → x ≤-ℕ k *ℕ x
leq-mul-is-nonzero-ℕ' k x H with is-successor-is-nonzero-ℕ H
... | (l , refl) = leq-mul-ℕ' l x
```

### If `m * n ≤ k` and `m` is nonzero, then `n ≤ k`

```agda
leq-right-factor-mul-succ-ℕ :
  (m n k : ℕ) → succ-ℕ m *ℕ n ≤-ℕ k → n ≤-ℕ k
leq-right-factor-mul-succ-ℕ m n =
  leq-right-summand-ℕ (m *ℕ n) n

leq-right-factor-ℕ :
  (m n k : ℕ) → is-nonzero-ℕ m → m *ℕ n ≤-ℕ k → n ≤-ℕ k
leq-right-factor-ℕ zero-ℕ n k H K = ex-falso (H refl)
leq-right-factor-ℕ (succ-ℕ m) n k H K = leq-right-factor-mul-succ-ℕ m n k K

leq-right-factor-eq-ℕ :
  (m n k : ℕ) → is-nonzero-ℕ m → m *ℕ n ＝ k → n ≤-ℕ k
leq-right-factor-eq-ℕ m n .(m *ℕ n) H refl =
  leq-mul-is-nonzero-ℕ' m n H
```

### If `m * n ≤ k` and `n` is nonzero, then `m ≤ k`

```agda
leq-left-factor-mul-succ-ℕ :
  (m n k : ℕ) → m *ℕ succ-ℕ n ≤-ℕ k → m ≤-ℕ k
leq-left-factor-mul-succ-ℕ m n k H =
  leq-right-summand-ℕ
    ( m *ℕ n)
    ( m)
    ( k)
    ( concatenate-eq-leq-ℕ k (inv (right-successor-law-mul-ℕ m n)) H)

leq-left-factor-ℕ :
  (m n k : ℕ) → is-nonzero-ℕ n → m *ℕ n ≤-ℕ k → m ≤-ℕ k
leq-left-factor-ℕ m zero-ℕ k H K = ex-falso (H refl)
leq-left-factor-ℕ m (succ-ℕ n) k H K = leq-left-factor-mul-succ-ℕ m n k K

leq-left-factor-eq-ℕ :
  (m n k : ℕ) → is-nonzero-ℕ n → m *ℕ n ＝ k → m ≤-ℕ k
leq-left-factor-eq-ℕ m n .(m *ℕ n) H refl =
  leq-mul-is-nonzero-ℕ n m H
```

## See also

- [The bounded natural numbers](elementary-number-theory.bounded-natural-numbers.md)
- [Strict inequality of the natural numbers](elementary-number-theory.strict-inequality-natural-numbers.md)
