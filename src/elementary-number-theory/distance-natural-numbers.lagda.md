# The distance between natural numbers

```agda
module elementary-number-theory.distance-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "distance function" Disambiguation="natural numbers" Agda=dist-ℕ}}
between [natural numbers](elementary-number-theory.natural-numbers.md) measures
how far two natural numbers are apart. If the
[inequality](elementary-number-theory.inequality-natural-numbers.md) $x \leq y$
holds, then the distance between $x$ and $y$ is the unique natural number $d$
equipped with an [identification](foundation-core.identity-types.md)
$x + d = y$.

**Note.** In the agda-unimath library, we often prefer to work with `dist-ℕ`
over the subtraction operation, which is either partially defined or it returns
nonsensical values. Not only is the distance function sensibly defined for any
pair of natural numbers, but it also satisfies the more pleasant and predictable
properties of a [metric](metric-spaces.metric-spaces.md).

## Definition

```agda
dist-ℕ : ℕ → ℕ → ℕ
dist-ℕ zero-ℕ n = n
dist-ℕ (succ-ℕ m) zero-ℕ = succ-ℕ m
dist-ℕ (succ-ℕ m) (succ-ℕ n) = dist-ℕ m n

dist-ℕ' : ℕ → ℕ → ℕ
dist-ℕ' m n = dist-ℕ n m

ap-dist-ℕ :
  {m n m' n' : ℕ} → m ＝ m' → n ＝ n' → dist-ℕ m n ＝ dist-ℕ m' n'
ap-dist-ℕ p q = ap-binary dist-ℕ p q
```

## Properties

### Two natural numbers are equal if and only if their distance is zero

```agda
eq-dist-ℕ : (m n : ℕ) → is-zero-ℕ (dist-ℕ m n) → m ＝ n
eq-dist-ℕ zero-ℕ zero-ℕ p = refl
eq-dist-ℕ (succ-ℕ m) (succ-ℕ n) p = ap succ-ℕ (eq-dist-ℕ m n p)

dist-eq-ℕ' : (n : ℕ) → is-zero-ℕ (dist-ℕ n n)
dist-eq-ℕ' zero-ℕ = refl
dist-eq-ℕ' (succ-ℕ n) = dist-eq-ℕ' n

dist-eq-ℕ : (m n : ℕ) → m ＝ n → is-zero-ℕ (dist-ℕ m n)
dist-eq-ℕ m .m refl = dist-eq-ℕ' m

is-one-dist-succ-ℕ : (x : ℕ) → is-one-ℕ (dist-ℕ x (succ-ℕ x))
is-one-dist-succ-ℕ zero-ℕ = refl
is-one-dist-succ-ℕ (succ-ℕ x) = is-one-dist-succ-ℕ x

is-one-dist-succ-ℕ' : (x : ℕ) → is-one-ℕ (dist-ℕ (succ-ℕ x) x)
is-one-dist-succ-ℕ' zero-ℕ = refl
is-one-dist-succ-ℕ' (succ-ℕ x) = is-one-dist-succ-ℕ' x
```

### The distance function is symmetric

```agda
symmetric-dist-ℕ :
  (m n : ℕ) → dist-ℕ m n ＝ dist-ℕ n m
symmetric-dist-ℕ zero-ℕ zero-ℕ = refl
symmetric-dist-ℕ zero-ℕ (succ-ℕ n) = refl
symmetric-dist-ℕ (succ-ℕ m) zero-ℕ = refl
symmetric-dist-ℕ (succ-ℕ m) (succ-ℕ n) = symmetric-dist-ℕ m n
```

### The distance from zero

```agda
left-unit-law-dist-ℕ :
  (n : ℕ) → dist-ℕ zero-ℕ n ＝ n
left-unit-law-dist-ℕ zero-ℕ = refl
left-unit-law-dist-ℕ (succ-ℕ n) = refl

right-unit-law-dist-ℕ :
  (n : ℕ) → dist-ℕ n zero-ℕ ＝ n
right-unit-law-dist-ℕ zero-ℕ = refl
right-unit-law-dist-ℕ (succ-ℕ n) = refl
```

## The triangle inequality

```agda
triangle-inequality-dist-ℕ :
  (m n k : ℕ) → dist-ℕ m n ≤-ℕ dist-ℕ m k +ℕ dist-ℕ k n
triangle-inequality-dist-ℕ zero-ℕ zero-ℕ zero-ℕ = star
triangle-inequality-dist-ℕ zero-ℕ zero-ℕ (succ-ℕ k) = star
triangle-inequality-dist-ℕ zero-ℕ (succ-ℕ n) zero-ℕ =
  tr
    ( succ-ℕ n ≤-ℕ_)
    ( inv (left-unit-law-add-ℕ (succ-ℕ n)))
    ( refl-leq-ℕ (succ-ℕ n))
triangle-inequality-dist-ℕ zero-ℕ (succ-ℕ n) (succ-ℕ k) =
  concatenate-eq-leq-eq-ℕ
    ( inv (ap succ-ℕ (left-unit-law-dist-ℕ n)))
    ( triangle-inequality-dist-ℕ zero-ℕ n k)
    ( ( ap (succ-ℕ ∘ (_+ℕ dist-ℕ k n)) (left-unit-law-dist-ℕ k)) ∙
      ( inv (left-successor-law-add-ℕ k (dist-ℕ k n))))
triangle-inequality-dist-ℕ (succ-ℕ m) zero-ℕ zero-ℕ = refl-leq-ℕ (succ-ℕ m)
triangle-inequality-dist-ℕ (succ-ℕ m) zero-ℕ (succ-ℕ k) =
  concatenate-eq-leq-eq-ℕ
    ( inv (ap succ-ℕ (right-unit-law-dist-ℕ m)))
    ( triangle-inequality-dist-ℕ m zero-ℕ k)
    ( ap (succ-ℕ ∘ (dist-ℕ m k +ℕ_)) (right-unit-law-dist-ℕ k))
triangle-inequality-dist-ℕ (succ-ℕ m) (succ-ℕ n) zero-ℕ =
  concatenate-leq-eq-ℕ
    ( dist-ℕ m n)
    ( transitive-leq-ℕ
      ( dist-ℕ m n)
      ( succ-ℕ (dist-ℕ m zero-ℕ +ℕ dist-ℕ zero-ℕ n))
      ( succ-ℕ (succ-ℕ (dist-ℕ m zero-ℕ +ℕ dist-ℕ zero-ℕ n)))
      ( succ-leq-ℕ (succ-ℕ (dist-ℕ m zero-ℕ +ℕ dist-ℕ zero-ℕ n)))
      ( transitive-leq-ℕ
        ( dist-ℕ m n)
        ( dist-ℕ m zero-ℕ +ℕ dist-ℕ zero-ℕ n)
        ( succ-ℕ (dist-ℕ m zero-ℕ +ℕ dist-ℕ zero-ℕ n))
        ( succ-leq-ℕ (dist-ℕ m zero-ℕ +ℕ dist-ℕ zero-ℕ n))
        ( triangle-inequality-dist-ℕ m n zero-ℕ)))
    ( ( ap
        ( succ-ℕ ∘ succ-ℕ)
        ( ap-add-ℕ (right-unit-law-dist-ℕ m) (left-unit-law-dist-ℕ n))) ∙
      ( inv (left-successor-law-add-ℕ m (succ-ℕ n))))
triangle-inequality-dist-ℕ (succ-ℕ m) (succ-ℕ n) (succ-ℕ k) =
  triangle-inequality-dist-ℕ m n k
```

### `dist-ℕ x y` is a solution in `z` to `x + z ＝ y`

```agda
is-additive-right-inverse-dist-ℕ :
  (x y : ℕ) → x ≤-ℕ y → x +ℕ dist-ℕ x y ＝ y
is-additive-right-inverse-dist-ℕ zero-ℕ zero-ℕ H = refl
is-additive-right-inverse-dist-ℕ zero-ℕ (succ-ℕ y) star =
  left-unit-law-add-ℕ (succ-ℕ y)
is-additive-right-inverse-dist-ℕ (succ-ℕ x) (succ-ℕ y) H =
  ( left-successor-law-add-ℕ x (dist-ℕ x y)) ∙
  ( ap succ-ℕ (is-additive-right-inverse-dist-ℕ x y H))

rewrite-left-add-dist-ℕ :
  (x y z : ℕ) → x +ℕ y ＝ z → x ＝ dist-ℕ y z
rewrite-left-add-dist-ℕ zero-ℕ zero-ℕ .zero-ℕ refl = refl
rewrite-left-add-dist-ℕ zero-ℕ (succ-ℕ y) .(succ-ℕ (zero-ℕ +ℕ y)) refl =
  ( inv (dist-eq-ℕ' y)) ∙
  ( inv (ap (dist-ℕ (succ-ℕ y)) (left-unit-law-add-ℕ (succ-ℕ y))))
rewrite-left-add-dist-ℕ (succ-ℕ x) zero-ℕ .(succ-ℕ x) refl = refl
rewrite-left-add-dist-ℕ (succ-ℕ x) (succ-ℕ y) ._ refl =
  rewrite-left-add-dist-ℕ (succ-ℕ x) y ((succ-ℕ x) +ℕ y) refl

rewrite-left-dist-add-ℕ :
  (x y z : ℕ) → y ≤-ℕ z → x ＝ dist-ℕ y z → x +ℕ y ＝ z
rewrite-left-dist-add-ℕ .(dist-ℕ y z) y z H refl =
  ( commutative-add-ℕ (dist-ℕ y z) y) ∙
  ( is-additive-right-inverse-dist-ℕ y z H)

rewrite-right-add-dist-ℕ :
  (x y z : ℕ) → x +ℕ y ＝ z → y ＝ dist-ℕ x z
rewrite-right-add-dist-ℕ x y z p =
  rewrite-left-add-dist-ℕ y x z (commutative-add-ℕ y x ∙ p)

rewrite-right-dist-add-ℕ :
  (x y z : ℕ) → x ≤-ℕ z → y ＝ dist-ℕ x z → x +ℕ y ＝ z
rewrite-right-dist-add-ℕ x .(dist-ℕ x z) z H refl =
  is-additive-right-inverse-dist-ℕ x z H

is-difference-dist-ℕ :
  (x y : ℕ) → x ≤-ℕ y → x +ℕ dist-ℕ x y ＝ y
is-difference-dist-ℕ zero-ℕ zero-ℕ H = refl
is-difference-dist-ℕ zero-ℕ (succ-ℕ y) H = left-unit-law-add-ℕ (succ-ℕ y)
is-difference-dist-ℕ (succ-ℕ x) (succ-ℕ y) H =
  ( left-successor-law-add-ℕ x (dist-ℕ x y)) ∙
  ( ap succ-ℕ (is-difference-dist-ℕ x y H))

is-difference-dist-ℕ' :
  (x y : ℕ) → x ≤-ℕ y → dist-ℕ x y +ℕ x ＝ y
is-difference-dist-ℕ' x y H =
  ( commutative-add-ℕ (dist-ℕ x y) x) ∙
  ( is-difference-dist-ℕ x y H)
```

### The distance from `n` to `n + m` is `m`

```agda
dist-add-ℕ : (x y : ℕ) → dist-ℕ x (x +ℕ y) ＝ y
dist-add-ℕ x y = inv (rewrite-right-add-dist-ℕ x y (x +ℕ y) refl)

dist-add-ℕ' : (x y : ℕ) → dist-ℕ (x +ℕ y) x ＝ y
dist-add-ℕ' x y = symmetric-dist-ℕ (x +ℕ y) x ∙ dist-add-ℕ x y
```

### If three elements are ordered linearly, then their distances add up

```agda
triangle-equality-dist-ℕ :
  (x y z : ℕ) → x ≤-ℕ y → y ≤-ℕ z →
  dist-ℕ x y +ℕ dist-ℕ y z ＝ dist-ℕ x z
triangle-equality-dist-ℕ zero-ℕ zero-ℕ zero-ℕ H1 H2 = refl
triangle-equality-dist-ℕ zero-ℕ zero-ℕ (succ-ℕ z) star star =
  ap succ-ℕ (left-unit-law-add-ℕ z)
triangle-equality-dist-ℕ zero-ℕ (succ-ℕ y) (succ-ℕ z) star H2 =
  left-successor-law-add-ℕ y (dist-ℕ y z) ∙
  ap succ-ℕ (is-additive-right-inverse-dist-ℕ y z H2)
triangle-equality-dist-ℕ (succ-ℕ x) (succ-ℕ y) (succ-ℕ z) H1 H2 =
  triangle-equality-dist-ℕ x y z H1 H2

cases-dist-ℕ :
  (x y z : ℕ) → UU lzero
cases-dist-ℕ x y z =
  ( dist-ℕ x y +ℕ dist-ℕ y z ＝ dist-ℕ x z) +
  ( ( dist-ℕ y z +ℕ dist-ℕ x z ＝ dist-ℕ x y) +
    ( dist-ℕ x z +ℕ dist-ℕ x y ＝ dist-ℕ y z))

is-total-dist-ℕ :
  (x y z : ℕ) → cases-dist-ℕ x y z
is-total-dist-ℕ x y z with order-three-elements-ℕ x y z
is-total-dist-ℕ x y z | inl (inl (H1 , H2)) =
  inl (triangle-equality-dist-ℕ x y z H1 H2)
is-total-dist-ℕ x y z | inl (inr (H1 , H2)) =
  inr
    ( inl
      ( ( commutative-add-ℕ (dist-ℕ y z) (dist-ℕ x z)) ∙
        ( ( ap (dist-ℕ x z +ℕ_) (symmetric-dist-ℕ y z)) ∙
          ( triangle-equality-dist-ℕ x z y H1 H2))))
is-total-dist-ℕ x y z | inr (inl (inl (H1 , H2))) =
  inr
    ( inl
      ( ( ap (dist-ℕ y z +ℕ_) (symmetric-dist-ℕ x z)) ∙
        ( ( triangle-equality-dist-ℕ y z x H1 H2) ∙
          ( symmetric-dist-ℕ y x))))
is-total-dist-ℕ x y z | inr (inl (inr (H1 , H2))) =
  inr
    ( inr
      ( ( ap (dist-ℕ x z +ℕ_) (symmetric-dist-ℕ x y)) ∙
        ( ( commutative-add-ℕ (dist-ℕ x z) (dist-ℕ y x)) ∙
          ( triangle-equality-dist-ℕ y x z H1 H2))))
is-total-dist-ℕ x y z | inr (inr (inl (H1 , H2))) =
  inr
    ( inr
      ( ( ap (_+ℕ dist-ℕ x y) (symmetric-dist-ℕ x z)) ∙
        ( ( triangle-equality-dist-ℕ z x y H1 H2) ∙
          ( symmetric-dist-ℕ z y))))
is-total-dist-ℕ x y z | inr (inr (inr (H1 , H2))) =
  inl
    ( ( ap-add-ℕ (symmetric-dist-ℕ x y) (symmetric-dist-ℕ y z)) ∙
      ( ( commutative-add-ℕ (dist-ℕ y x) (dist-ℕ z y)) ∙
        ( ( triangle-equality-dist-ℕ z y x H1 H2) ∙
          ( symmetric-dist-ℕ z x))))
```

### If `x ≤ y` then the distance between `x` and `y` is less than `y`

```agda
leq-dist-ℕ :
  (x y : ℕ) → x ≤-ℕ y → dist-ℕ x y ≤-ℕ y
leq-dist-ℕ zero-ℕ zero-ℕ H = refl-leq-ℕ zero-ℕ
leq-dist-ℕ zero-ℕ (succ-ℕ y) H = refl-leq-ℕ y
leq-dist-ℕ (succ-ℕ x) (succ-ℕ y) H =
  transitive-leq-ℕ (dist-ℕ x y) y (succ-ℕ y) (succ-leq-ℕ y) (leq-dist-ℕ x y H)
```

### If `x < b` and `y < b`, then `dist-ℕ x y < b`

```agda
strict-upper-bound-dist-ℕ :
  (b x y : ℕ) → x <-ℕ b → y <-ℕ b → dist-ℕ x y <-ℕ b
strict-upper-bound-dist-ℕ (succ-ℕ b) zero-ℕ y H K = K
strict-upper-bound-dist-ℕ (succ-ℕ b) (succ-ℕ x) zero-ℕ H K = H
strict-upper-bound-dist-ℕ (succ-ℕ b) (succ-ℕ x) (succ-ℕ y) H K =
  preserves-le-succ-ℕ (dist-ℕ x y) b (strict-upper-bound-dist-ℕ b x y H K)
```

### If `x < y` then `dist-ℕ x (succ-ℕ y) = succ-ℕ (dist-ℕ x y)`

```agda
right-successor-law-dist-ℕ :
  (x y : ℕ) → x ≤-ℕ y → dist-ℕ x (succ-ℕ y) ＝ succ-ℕ (dist-ℕ x y)
right-successor-law-dist-ℕ zero-ℕ zero-ℕ star = refl
right-successor-law-dist-ℕ zero-ℕ (succ-ℕ y) star = refl
right-successor-law-dist-ℕ (succ-ℕ x) (succ-ℕ y) H =
  right-successor-law-dist-ℕ x y H

left-successor-law-dist-ℕ :
  (x y : ℕ) → y ≤-ℕ x → dist-ℕ (succ-ℕ x) y ＝ succ-ℕ (dist-ℕ x y)
left-successor-law-dist-ℕ zero-ℕ zero-ℕ star = refl
left-successor-law-dist-ℕ (succ-ℕ x) zero-ℕ star = refl
left-successor-law-dist-ℕ (succ-ℕ x) (succ-ℕ y) H =
  left-successor-law-dist-ℕ x y H
```

### `dist-ℕ` is translation invariant

```agda
translation-invariant-dist-ℕ :
  (k m n : ℕ) → dist-ℕ (k +ℕ m) (k +ℕ n) ＝ dist-ℕ m n
translation-invariant-dist-ℕ zero-ℕ m n =
  ap-dist-ℕ (left-unit-law-add-ℕ m) (left-unit-law-add-ℕ n)
translation-invariant-dist-ℕ (succ-ℕ k) m n =
  ( ap-dist-ℕ (left-successor-law-add-ℕ k m) (left-successor-law-add-ℕ k n)) ∙
  ( translation-invariant-dist-ℕ k m n)

translation-invariant-dist-ℕ' :
  (k m n : ℕ) → dist-ℕ (m +ℕ k) (n +ℕ k) ＝ dist-ℕ m n
translation-invariant-dist-ℕ' k m n =
  ( ap-dist-ℕ (commutative-add-ℕ m k) (commutative-add-ℕ n k)) ∙
  ( translation-invariant-dist-ℕ k m n)
```

### `dist-ℕ` is linear with respect to scalar multiplication

```agda
left-distributive-mul-dist-ℕ :
  (m n k : ℕ) → k *ℕ dist-ℕ m n ＝ dist-ℕ (k *ℕ m) (k *ℕ n)
left-distributive-mul-dist-ℕ zero-ℕ zero-ℕ zero-ℕ = refl
left-distributive-mul-dist-ℕ zero-ℕ zero-ℕ (succ-ℕ k) =
  left-distributive-mul-dist-ℕ zero-ℕ zero-ℕ k
left-distributive-mul-dist-ℕ zero-ℕ (succ-ℕ n) zero-ℕ = refl
left-distributive-mul-dist-ℕ zero-ℕ (succ-ℕ n) (succ-ℕ k) =
  ap
    ( dist-ℕ' ((succ-ℕ k) *ℕ (succ-ℕ n)))
    ( inv (right-zero-law-mul-ℕ (succ-ℕ k)))
left-distributive-mul-dist-ℕ (succ-ℕ m) zero-ℕ zero-ℕ = refl
left-distributive-mul-dist-ℕ (succ-ℕ m) zero-ℕ (succ-ℕ k) =
  ap
    ( dist-ℕ ((succ-ℕ k) *ℕ (succ-ℕ m)))
    ( inv (right-zero-law-mul-ℕ (succ-ℕ k)))
left-distributive-mul-dist-ℕ (succ-ℕ m) (succ-ℕ n) zero-ℕ = refl
left-distributive-mul-dist-ℕ (succ-ℕ m) (succ-ℕ n) (succ-ℕ k) =
  inv
    ( ( ap-dist-ℕ
        ( right-successor-law-mul-ℕ (succ-ℕ k) m)
        ( right-successor-law-mul-ℕ (succ-ℕ k) n)) ∙
      ( translation-invariant-dist-ℕ'
        ( succ-ℕ k)
        ( succ-ℕ k *ℕ m)
        ( succ-ℕ k *ℕ n)) ∙
      ( inv (left-distributive-mul-dist-ℕ m n (succ-ℕ k))))

left-distributive-mul-dist-ℕ' :
  (m n k : ℕ) → dist-ℕ (k *ℕ m) (k *ℕ n) ＝ k *ℕ (dist-ℕ m n)
left-distributive-mul-dist-ℕ' m n k =
  inv (left-distributive-mul-dist-ℕ m n k)

right-distributive-mul-dist-ℕ :
  (x y k : ℕ) → dist-ℕ x y *ℕ k ＝ dist-ℕ (x *ℕ k) (y *ℕ k)
right-distributive-mul-dist-ℕ x y k =
  ( commutative-mul-ℕ (dist-ℕ x y) k) ∙
  ( ( left-distributive-mul-dist-ℕ x y k) ∙
    ( ap-dist-ℕ (commutative-mul-ℕ k x) (commutative-mul-ℕ k y)))
```
