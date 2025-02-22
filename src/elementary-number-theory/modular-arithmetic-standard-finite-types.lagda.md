# Modular arithmetic on the standard finite types

```agda
module elementary-number-theory.modular-arithmetic-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.sets
open import foundation.split-surjective-maps
open import foundation.surjective-maps
open import foundation.universe-levels

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Definitions

### The congruence class of a natural number modulo a successor

```agda
mod-succ-ℕ : (k : ℕ) → ℕ → Fin (succ-ℕ k)
mod-succ-ℕ k zero-ℕ = zero-Fin k
mod-succ-ℕ k (succ-ℕ n) = succ-Fin (succ-ℕ k) (mod-succ-ℕ k n)

mod-two-ℕ : ℕ → Fin 2
mod-two-ℕ = mod-succ-ℕ 1

mod-three-ℕ : ℕ → Fin 3
mod-three-ℕ = mod-succ-ℕ 2
```

## Properties

### `nat-Fin k (succ-Fin k x)` and `succ-ℕ (nat-Fin k x)` are congruent modulo `k`

```agda
cong-nat-succ-Fin :
  (k : ℕ) (x : Fin k) →
  nat-Fin k (succ-Fin k x) ≡ succ-ℕ (nat-Fin k x) mod-ℕ k
cong-nat-succ-Fin (succ-ℕ k) (inl x) =
  cong-identification-ℕ
    ( succ-ℕ k)
    { nat-Fin (succ-ℕ k) (succ-Fin (succ-ℕ k) (inl x))}
    { succ-ℕ (nat-Fin k x)}
    ( nat-succ-Fin k x)
cong-nat-succ-Fin (succ-ℕ k) (inr _) =
  concatenate-eq-cong-ℕ
    ( succ-ℕ k)
    { nat-Fin (succ-ℕ k) (zero-Fin k)}
    { zero-ℕ}
    { succ-ℕ k}
    ( is-zero-nat-zero-Fin {k})
    ( cong-zero-ℕ' (succ-ℕ k))

cong-nat-mod-succ-ℕ :
  (k x : ℕ) → nat-Fin (succ-ℕ k) (mod-succ-ℕ k x) ≡ x mod-ℕ succ-ℕ k
cong-nat-mod-succ-ℕ k zero-ℕ = cong-is-zero-nat-zero-Fin
cong-nat-mod-succ-ℕ k (succ-ℕ x) =
  transitive-cong-ℕ
    ( succ-ℕ k)
    ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k (succ-ℕ x)))
    ( succ-ℕ (nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)))
    ( succ-ℕ x)
    ( cong-nat-mod-succ-ℕ k x)
    ( cong-nat-succ-Fin (succ-ℕ k) (mod-succ-ℕ k x))
```

### If the congruence classes of `x` and `y` modulo `k + 1` are equal, then `x` and `y` are congruent modulo `k + 1`

```agda
cong-eq-mod-succ-ℕ :
  (k x y : ℕ) → mod-succ-ℕ k x ＝ mod-succ-ℕ k y → x ≡ y mod-ℕ succ-ℕ k
cong-eq-mod-succ-ℕ k x y p =
  concatenate-cong-eq-cong-ℕ {succ-ℕ k} {x}
    ( symmetric-cong-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)) x
      ( cong-nat-mod-succ-ℕ k x))
    ( ap (nat-Fin (succ-ℕ k)) p)
    ( cong-nat-mod-succ-ℕ k y)
```

### If `x` and `y` are congruent modulo `k + 1` then their congruence classes modulo `k + 1` are equal

```agda
eq-mod-succ-cong-ℕ :
  (k x y : ℕ) → x ≡ y mod-ℕ succ-ℕ k → mod-succ-ℕ k x ＝ mod-succ-ℕ k y
eq-mod-succ-cong-ℕ k x y H =
  eq-cong-nat-Fin
    ( succ-ℕ k)
    ( mod-succ-ℕ k x)
    ( mod-succ-ℕ k y)
    ( transitive-cong-ℕ
      ( succ-ℕ k)
      ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k x))
      ( x)
      ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k y))
      ( transitive-cong-ℕ (succ-ℕ k) x y (nat-Fin (succ-ℕ k) (mod-succ-ℕ k y))
        ( symmetric-cong-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) (mod-succ-ℕ k y)) y
          ( cong-nat-mod-succ-ℕ k y)) H)
      ( cong-nat-mod-succ-ℕ k x))
```

### `k + 1` divides `x` if and only if `x ≡ 0` modulo `k + 1`

```agda
is-zero-mod-succ-ℕ :
  (k x : ℕ) → div-ℕ (succ-ℕ k) x → is-zero-Fin (succ-ℕ k) (mod-succ-ℕ k x)
is-zero-mod-succ-ℕ k x d =
  eq-mod-succ-cong-ℕ k x zero-ℕ
    ( concatenate-div-eq-ℕ d (inv (right-unit-law-dist-ℕ x)))

div-is-zero-mod-succ-ℕ :
  (k x : ℕ) → is-zero-Fin (succ-ℕ k) (mod-succ-ℕ k x) → div-ℕ (succ-ℕ k) x
div-is-zero-mod-succ-ℕ k x p =
  concatenate-div-eq-ℕ
    ( cong-eq-mod-succ-ℕ k x zero-ℕ p)
    ( right-unit-law-dist-ℕ x)
```

### The inclusion of `Fin k` into `ℕ` is a section of `mod-succ-ℕ`

```agda
is-section-nat-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → mod-succ-ℕ k (nat-Fin (succ-ℕ k) x) ＝ x
is-section-nat-Fin k x =
  is-injective-nat-Fin (succ-ℕ k)
    ( eq-cong-le-ℕ
      ( succ-ℕ k)
      ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k (nat-Fin (succ-ℕ k) x)))
      ( nat-Fin (succ-ℕ k) x)
      ( strict-upper-bound-nat-Fin
        ( succ-ℕ k)
        ( mod-succ-ℕ k (nat-Fin (succ-ℕ k) x)))
      ( strict-upper-bound-nat-Fin (succ-ℕ k) x)
      ( cong-nat-mod-succ-ℕ k (nat-Fin (succ-ℕ k) x)))
```

### `mod-succ-ℕ` is split surjective

```agda
is-split-surjective-mod-succ-ℕ :
  (k : ℕ) → is-split-surjective (mod-succ-ℕ k)
pr1 (is-split-surjective-mod-succ-ℕ k x) = nat-Fin (succ-ℕ k) x
pr2 (is-split-surjective-mod-succ-ℕ k x) = is-section-nat-Fin k x
```

### `mod-succ-ℕ` is surjective

```agda
is-surjective-mod-succ-ℕ :
  (k : ℕ) → is-surjective (mod-succ-ℕ k)
is-surjective-mod-succ-ℕ k =
  is-surjective-is-split-surjective (is-split-surjective-mod-succ-ℕ k)
```

### The residue of `x` modulo `k + 1` is less than or equal to `x`

```agda
leq-nat-mod-succ-ℕ :
  (k x : ℕ) → leq-ℕ (nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)) x
leq-nat-mod-succ-ℕ k zero-ℕ =
  concatenate-eq-leq-ℕ zero-ℕ (is-zero-nat-zero-Fin {k}) (refl-leq-ℕ zero-ℕ)
leq-nat-mod-succ-ℕ k (succ-ℕ x) =
  transitive-leq-ℕ
    ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k (succ-ℕ x)))
    ( succ-ℕ (nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)))
    ( succ-ℕ x)
    ( leq-nat-mod-succ-ℕ k x)
    ( leq-nat-succ-Fin (succ-ℕ k) (mod-succ-ℕ k x))
```

### If `x < k + 1`, then `x` is equal to its residue modulo `k + 1`

```agda
eq-nat-mod-succ-ℕ :
  (k x : ℕ) → x <-ℕ succ-ℕ k → nat-Fin (succ-ℕ k) (mod-succ-ℕ k x) ＝ x
eq-nat-mod-succ-ℕ k x H =
  eq-cong-le-ℕ
    ( succ-ℕ k)
    ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k x))
    ( x)
    ( strict-upper-bound-nat-Fin (succ-ℕ k) (mod-succ-ℕ k x))
    ( H)
    ( cong-nat-mod-succ-ℕ k x)
```

## Operations

### Addition on the standard finite sets

```agda
add-Fin : (k : ℕ) → Fin k → Fin k → Fin k
add-Fin (succ-ℕ k) x y =
  mod-succ-ℕ k ((nat-Fin (succ-ℕ k) x) +ℕ (nat-Fin (succ-ℕ k) y))

add-Fin' : (k : ℕ) → Fin k → Fin k → Fin k
add-Fin' k x y = add-Fin k y x

ap-add-Fin :
  (k : ℕ) {x y x' y' : Fin k} →
  x ＝ x' → y ＝ y' → add-Fin k x y ＝ add-Fin k x' y'
ap-add-Fin k p q = ap-binary (add-Fin k) p q

cong-add-Fin :
  {k : ℕ} (x y : Fin k) →
  nat-Fin k (add-Fin k x y) ≡ (nat-Fin k x) +ℕ (nat-Fin k y) mod-ℕ k
cong-add-Fin {succ-ℕ k} x y =
  cong-nat-mod-succ-ℕ k ((nat-Fin (succ-ℕ k) x) +ℕ (nat-Fin (succ-ℕ k) y))

cong-add-ℕ :
  {k : ℕ} (x y : ℕ) →
  nat-Fin (k +ℕ 1) (mod-succ-ℕ k x) +ℕ nat-Fin (k +ℕ 1) (mod-succ-ℕ k y) ≡
  x +ℕ y mod-ℕ k +ℕ 1
cong-add-ℕ {k} x y =
  transitive-cong-ℕ
    ( succ-ℕ k)
    ( add-ℕ
      ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k x))
      ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k y)))
    ( x +ℕ (nat-Fin (succ-ℕ k) (mod-succ-ℕ k y)))
    ( x +ℕ y)
    ( translation-invariant-cong-ℕ
      ( succ-ℕ k)
      ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k y))
      ( y)
      ( x)
      ( cong-nat-mod-succ-ℕ k y))
    ( translation-invariant-cong-ℕ'
      ( succ-ℕ k)
      ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k x))
      ( x)
      ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k y))
      ( cong-nat-mod-succ-ℕ k x))

mod-succ-add-ℕ :
  (k x y : ℕ) →
  mod-succ-ℕ k (x +ℕ y) ＝
  add-Fin (succ-ℕ k) (mod-succ-ℕ k x) (mod-succ-ℕ k y)
mod-succ-add-ℕ k x y =
  eq-mod-succ-cong-ℕ k
    ( x +ℕ y)
    ( add-ℕ
      ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k x))
      ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k y)))
    ( congruence-add-ℕ
      ( succ-ℕ k)
      { x}
      { y}
      { nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)}
      { nat-Fin (succ-ℕ k) (mod-succ-ℕ k y)}
      ( symmetric-cong-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)) x
        ( cong-nat-mod-succ-ℕ k x))
      ( symmetric-cong-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) (mod-succ-ℕ k y)) y
        ( cong-nat-mod-succ-ℕ k y)))
```

### Distance on the standard finite sets

```agda
dist-Fin : (k : ℕ) → Fin k → Fin k → Fin k
dist-Fin (succ-ℕ k) x y =
  mod-succ-ℕ k (dist-ℕ (nat-Fin (succ-ℕ k) x) (nat-Fin (succ-ℕ k) y))

dist-Fin' : (k : ℕ) → Fin k → Fin k → Fin k
dist-Fin' k x y = dist-Fin k y x

ap-dist-Fin :
  (k : ℕ) {x y x' y' : Fin k} →
  x ＝ x' → y ＝ y' → dist-Fin k x y ＝ dist-Fin k x' y'
ap-dist-Fin k p q = ap-binary (dist-Fin k) p q

cong-dist-Fin :
  {k : ℕ} (x y : Fin k) →
  nat-Fin k (dist-Fin k x y) ≡ dist-ℕ (nat-Fin k x) (nat-Fin k y) mod-ℕ k
cong-dist-Fin {succ-ℕ k} x y =
  cong-nat-mod-succ-ℕ k (dist-ℕ (nat-Fin (succ-ℕ k) x) (nat-Fin (succ-ℕ k) y))
```

### The negative of an element of a standard finite set

```agda
neg-Fin :
  (k : ℕ) → Fin k → Fin k
neg-Fin (succ-ℕ k) x =
  mod-succ-ℕ k (dist-ℕ (nat-Fin (succ-ℕ k) x) (succ-ℕ k))

cong-neg-Fin :
  {k : ℕ} (x : Fin k) →
  nat-Fin k (neg-Fin k x) ≡ dist-ℕ (nat-Fin k x) k mod-ℕ k
cong-neg-Fin {succ-ℕ k} x =
  cong-nat-mod-succ-ℕ k (dist-ℕ (nat-Fin (succ-ℕ k) x) (succ-ℕ k))
```

### Multiplication on the standard finite sets

```agda
mul-Fin :
  (k : ℕ) → Fin k → Fin k → Fin k
mul-Fin (succ-ℕ k) x y =
  mod-succ-ℕ k ((nat-Fin (succ-ℕ k) x) *ℕ (nat-Fin (succ-ℕ k) y))

mul-Fin' :
  (k : ℕ) → Fin k → Fin k → Fin k
mul-Fin' k x y = mul-Fin k y x

ap-mul-Fin :
  (k : ℕ) {x y x' y' : Fin k} →
  x ＝ x' → y ＝ y' → mul-Fin k x y ＝ mul-Fin k x' y'
ap-mul-Fin k p q = ap-binary (mul-Fin k) p q

cong-mul-Fin :
  {k : ℕ} (x y : Fin k) →
  nat-Fin k (mul-Fin k x y) ≡ (nat-Fin k x) *ℕ (nat-Fin k y) mod-ℕ k
cong-mul-Fin {succ-ℕ k} x y =
  cong-nat-mod-succ-ℕ k ((nat-Fin (succ-ℕ k) x) *ℕ (nat-Fin (succ-ℕ k) y))
```

## Laws

### Laws for addition

```agda
commutative-add-Fin : (k : ℕ) (x y : Fin k) → add-Fin k x y ＝ add-Fin k y x
commutative-add-Fin (succ-ℕ k) x y =
  ap
    ( mod-succ-ℕ k)
    ( commutative-add-ℕ (nat-Fin (succ-ℕ k) x) (nat-Fin (succ-ℕ k) y))

associative-add-Fin :
  (k : ℕ) (x y z : Fin k) →
  add-Fin k (add-Fin k x y) z ＝ add-Fin k x (add-Fin k y z)
associative-add-Fin (succ-ℕ k) x y z =
  eq-mod-succ-cong-ℕ k
    ( add-ℕ
      ( nat-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) x y))
      ( nat-Fin (succ-ℕ k) z))
    ( add-ℕ
      ( nat-Fin (succ-ℕ k) x)
      ( nat-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) y z)))
    ( concatenate-cong-eq-cong-ℕ
      { x1 =
        add-ℕ
          ( nat-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) x y))
          ( nat-Fin (succ-ℕ k) z)}
      { x2 =
        add-ℕ
          ( (nat-Fin (succ-ℕ k) x) +ℕ (nat-Fin (succ-ℕ k) y))
          ( nat-Fin (succ-ℕ k) z)}
      { x3 =
        add-ℕ
          ( nat-Fin (succ-ℕ k) x)
          ( (nat-Fin (succ-ℕ k) y) +ℕ (nat-Fin (succ-ℕ k) z))}
      { x4 =
        add-ℕ
          ( nat-Fin (succ-ℕ k) x) (nat-Fin (succ-ℕ k)
          ( add-Fin (succ-ℕ k) y z))}
      ( congruence-add-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) x y)}
        { y = nat-Fin (succ-ℕ k) z}
        { x' = (nat-Fin (succ-ℕ k) x) +ℕ (nat-Fin (succ-ℕ k) y)}
        { y' = nat-Fin (succ-ℕ k) z}
        ( cong-add-Fin x y)
        ( refl-cong-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) z)))
      ( associative-add-ℕ
        ( nat-Fin (succ-ℕ k) x)
        ( nat-Fin (succ-ℕ k) y)
        ( nat-Fin (succ-ℕ k) z))
      ( congruence-add-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (succ-ℕ k) x}
        { y = (nat-Fin (succ-ℕ k) y) +ℕ (nat-Fin (succ-ℕ k) z)}
        { x' = nat-Fin (succ-ℕ k) x}
        { y' = nat-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) y z)}
        ( refl-cong-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) x))
        ( symmetric-cong-ℕ
          ( succ-ℕ k)
          ( nat-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) y z))
          ( (nat-Fin (succ-ℕ k) y) +ℕ (nat-Fin (succ-ℕ k) z))
          ( cong-add-Fin y z))))

right-unit-law-add-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → add-Fin (succ-ℕ k) x (zero-Fin k) ＝ x
right-unit-law-add-Fin k x =
  ( eq-mod-succ-cong-ℕ k
    ( (nat-Fin (succ-ℕ k) x) +ℕ (nat-Fin (succ-ℕ k) (zero-Fin k)))
    ( (nat-Fin (succ-ℕ k) x) +ℕ zero-ℕ)
    ( congruence-add-ℕ
      ( succ-ℕ k)
      { x = nat-Fin (succ-ℕ k) x}
      { y = nat-Fin (succ-ℕ k) (zero-Fin k)}
      { x' = nat-Fin (succ-ℕ k) x}
      { y' = zero-ℕ}
      ( refl-cong-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) x))
      ( cong-is-zero-nat-zero-Fin {k}))) ∙
  ( is-section-nat-Fin k x)

left-unit-law-add-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → add-Fin (succ-ℕ k) (zero-Fin k) x ＝ x
left-unit-law-add-Fin k x =
  ( commutative-add-Fin (succ-ℕ k) (zero-Fin k) x) ∙
  ( right-unit-law-add-Fin k x)

left-inverse-law-add-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  is-zero-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) (neg-Fin (succ-ℕ k) x) x)
left-inverse-law-add-Fin k x =
  eq-mod-succ-cong-ℕ k
    ( (nat-Fin (succ-ℕ k) (neg-Fin (succ-ℕ k) x)) +ℕ (nat-Fin (succ-ℕ k) x))
    ( zero-ℕ)
    ( concatenate-cong-eq-cong-ℕ
      { succ-ℕ k}
      { x1 =
        add-ℕ
          ( nat-Fin (succ-ℕ k) (neg-Fin (succ-ℕ k) x))
          ( nat-Fin (succ-ℕ k) x)}
      { x2 =
        (dist-ℕ (nat-Fin (succ-ℕ k) x) (succ-ℕ k)) +ℕ (nat-Fin (succ-ℕ k) x)}
      { x3 = succ-ℕ k}
      { x4 = zero-ℕ}
      ( translation-invariant-cong-ℕ' (succ-ℕ k)
        ( nat-Fin (succ-ℕ k) (neg-Fin (succ-ℕ k) x))
        ( dist-ℕ (nat-Fin (succ-ℕ k) x) (succ-ℕ k))
        ( nat-Fin (succ-ℕ k) x)
        ( cong-neg-Fin x))
      ( is-difference-dist-ℕ' (nat-Fin (succ-ℕ k) x) (succ-ℕ k)
        ( upper-bound-nat-Fin (succ-ℕ k) (inl x)))
      ( cong-zero-ℕ' (succ-ℕ k)))

right-inverse-law-add-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  is-zero-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) x (neg-Fin (succ-ℕ k) x))
right-inverse-law-add-Fin k x =
  ( commutative-add-Fin (succ-ℕ k) x (neg-Fin (succ-ℕ k) x)) ∙
  ( left-inverse-law-add-Fin k x)
```

### The successor function on a standard finite set adds one

```agda
is-add-one-succ-Fin' :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  succ-Fin (succ-ℕ k) x ＝ add-Fin (succ-ℕ k) x (one-Fin k)
is-add-one-succ-Fin' zero-ℕ (inr _) = refl
is-add-one-succ-Fin' (succ-ℕ k) x =
  ( ap (succ-Fin (succ-ℕ (succ-ℕ k))) (inv (is-section-nat-Fin (succ-ℕ k) x))) ∙
  ( ap
    ( mod-succ-ℕ (succ-ℕ k))
    ( ap
      ( (nat-Fin (succ-ℕ (succ-ℕ k)) x) +ℕ_)
      ( inv (is-one-nat-one-Fin (succ-ℕ k)))))

is-add-one-succ-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  succ-Fin (succ-ℕ k) x ＝ add-Fin (succ-ℕ k) (one-Fin k) x
is-add-one-succ-Fin k x =
  ( is-add-one-succ-Fin' k x) ∙
  ( commutative-add-Fin (succ-ℕ k) x (one-Fin k))
```

### Successor laws for addition on Fin k

```agda
right-successor-law-add-Fin :
  (k : ℕ) (x y : Fin k) →
  add-Fin k x (succ-Fin k y) ＝ succ-Fin k (add-Fin k x y)
right-successor-law-add-Fin (succ-ℕ k) x y =
  ( ap (add-Fin (succ-ℕ k) x) (is-add-one-succ-Fin' k y)) ∙
  ( ( inv (associative-add-Fin (succ-ℕ k) x y (one-Fin k))) ∙
    ( inv (is-add-one-succ-Fin' k (add-Fin (succ-ℕ k) x y))))

left-successor-law-add-Fin :
  (k : ℕ) (x y : Fin k) →
  add-Fin k (succ-Fin k x) y ＝ succ-Fin k (add-Fin k x y)
left-successor-law-add-Fin k x y =
  commutative-add-Fin k (succ-Fin k x) y ∙
  ( ( right-successor-law-add-Fin k y x) ∙
    ( ap (succ-Fin k) (commutative-add-Fin k y x)))
```

### Laws for multiplication on the standard finite types

```agda
associative-mul-Fin :
  (k : ℕ) (x y z : Fin k) →
  mul-Fin k (mul-Fin k x y) z ＝ mul-Fin k x (mul-Fin k y z)
associative-mul-Fin (succ-ℕ k) x y z =
  eq-mod-succ-cong-ℕ k
    ( ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x y)) *ℕ
      ( nat-Fin (succ-ℕ k) z))
    ( ( nat-Fin (succ-ℕ k) x) *ℕ
      ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) y z)))
    ( concatenate-cong-eq-cong-ℕ
      { x1 =
          ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x y)) *ℕ
          ( nat-Fin (succ-ℕ k) z)}
      { x2 =
          ( (nat-Fin (succ-ℕ k) x) *ℕ (nat-Fin (succ-ℕ k) y)) *ℕ
          ( nat-Fin (succ-ℕ k) z)}
      { x3 =
          ( nat-Fin (succ-ℕ k) x) *ℕ
          ( (nat-Fin (succ-ℕ k) y) *ℕ (nat-Fin (succ-ℕ k) z))}
      { x4 =
          ( nat-Fin (succ-ℕ k) x) *ℕ
          ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) y z))}
      ( congruence-mul-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x y)}
        { y = nat-Fin (succ-ℕ k) z}
        ( cong-mul-Fin x y)
        ( refl-cong-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) z)))
      ( associative-mul-ℕ
        ( nat-Fin (succ-ℕ k) x)
        ( nat-Fin (succ-ℕ k) y)
        ( nat-Fin (succ-ℕ k) z))
      ( symmetric-cong-ℕ
        ( succ-ℕ k)
        ( ( nat-Fin (succ-ℕ k) x) *ℕ
          ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) y z)))
        ( ( nat-Fin (succ-ℕ k) x) *ℕ
          ( (nat-Fin (succ-ℕ k) y) *ℕ (nat-Fin (succ-ℕ k) z)))
        ( congruence-mul-ℕ
          ( succ-ℕ k)
          { x = nat-Fin (succ-ℕ k) x}
          { y = nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) y z)}
          ( refl-cong-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) x))
          ( cong-mul-Fin y z))))

commutative-mul-Fin :
  (k : ℕ) (x y : Fin k) → mul-Fin k x y ＝ mul-Fin k y x
commutative-mul-Fin (succ-ℕ k) x y =
  eq-mod-succ-cong-ℕ k
    ( (nat-Fin (succ-ℕ k) x) *ℕ (nat-Fin (succ-ℕ k) y))
    ( (nat-Fin (succ-ℕ k) y) *ℕ (nat-Fin (succ-ℕ k) x))
    ( cong-identification-ℕ
      ( succ-ℕ k)
      ( commutative-mul-ℕ (nat-Fin (succ-ℕ k) x) (nat-Fin (succ-ℕ k) y)))

left-unit-law-mul-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → mul-Fin (succ-ℕ k) (one-Fin k) x ＝ x
left-unit-law-mul-Fin zero-ℕ (inr _) = refl
left-unit-law-mul-Fin (succ-ℕ k) x =
  ( eq-mod-succ-cong-ℕ (succ-ℕ k)
    ( ( nat-Fin (succ-ℕ (succ-ℕ k)) (one-Fin (succ-ℕ k))) *ℕ
      ( nat-Fin (succ-ℕ (succ-ℕ k)) x))
    ( nat-Fin (succ-ℕ (succ-ℕ k)) x)
    ( cong-identification-ℕ
      ( succ-ℕ (succ-ℕ k))
      ( ( ap
          ( _*ℕ (nat-Fin (succ-ℕ (succ-ℕ k)) x))
          ( is-one-nat-one-Fin k)) ∙
        ( left-unit-law-mul-ℕ (nat-Fin (succ-ℕ (succ-ℕ k)) x))))) ∙
  ( is-section-nat-Fin (succ-ℕ k) x)

right-unit-law-mul-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → mul-Fin (succ-ℕ k) x (one-Fin k) ＝ x
right-unit-law-mul-Fin k x =
  ( commutative-mul-Fin (succ-ℕ k) x (one-Fin k)) ∙
  ( left-unit-law-mul-Fin k x)

left-zero-law-mul-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → mul-Fin (succ-ℕ k) (zero-Fin k) x ＝ zero-Fin k
left-zero-law-mul-Fin k x =
  ( eq-mod-succ-cong-ℕ k
    ( (nat-Fin (succ-ℕ k) (zero-Fin k)) *ℕ (nat-Fin (succ-ℕ k) x))
    ( nat-Fin (succ-ℕ k) (zero-Fin k))
    ( cong-identification-ℕ
      ( succ-ℕ k)
      { (nat-Fin (succ-ℕ k) (zero-Fin k)) *ℕ (nat-Fin (succ-ℕ k) x)}
      { nat-Fin (succ-ℕ k) (zero-Fin k)}
      ( ( ap (_*ℕ (nat-Fin (succ-ℕ k) x)) (is-zero-nat-zero-Fin {k})) ∙
        ( inv (is-zero-nat-zero-Fin {k}))))) ∙
  ( is-section-nat-Fin k (zero-Fin k))

right-zero-law-mul-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) → mul-Fin (succ-ℕ k) x (zero-Fin k) ＝ zero-Fin k
right-zero-law-mul-Fin k x =
  ( commutative-mul-Fin (succ-ℕ k) x (zero-Fin k)) ∙
  ( left-zero-law-mul-Fin k x)

left-distributive-mul-add-Fin :
  (k : ℕ) (x y z : Fin k) →
  mul-Fin k x (add-Fin k y z) ＝ add-Fin k (mul-Fin k x y) (mul-Fin k x z)
left-distributive-mul-add-Fin (succ-ℕ k) x y z =
  eq-mod-succ-cong-ℕ k
    ( ( nat-Fin (succ-ℕ k) x) *ℕ
      ( nat-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) y z)))
    ( add-ℕ
      ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x y))
      ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x z)))
    ( concatenate-cong-eq-cong-ℕ
      { k = succ-ℕ k}
      { x1 =
          ( nat-Fin (succ-ℕ k) x) *ℕ
          ( nat-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) y z))}
      { x2 =
          ( nat-Fin (succ-ℕ k) x) *ℕ
          ( (nat-Fin (succ-ℕ k) y) +ℕ (nat-Fin (succ-ℕ k) z))}
      { x3 =
        add-ℕ
          ( (nat-Fin (succ-ℕ k) x) *ℕ (nat-Fin (succ-ℕ k) y))
          ( (nat-Fin (succ-ℕ k) x) *ℕ (nat-Fin (succ-ℕ k) z))}
      { x4 =
        add-ℕ
          ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x y))
          ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x z))}
      ( congruence-mul-ℕ
        ( succ-ℕ k)
        { x = nat-Fin (succ-ℕ k) x}
        { y = nat-Fin (succ-ℕ k) (add-Fin (succ-ℕ k) y z)}
        { x' = nat-Fin (succ-ℕ k) x}
        { y' = (nat-Fin (succ-ℕ k) y) +ℕ (nat-Fin (succ-ℕ k) z)}
        ( refl-cong-ℕ (succ-ℕ k) (nat-Fin (succ-ℕ k) x))
        ( cong-add-Fin y z))
      ( left-distributive-mul-add-ℕ
        ( nat-Fin (succ-ℕ k) x)
        ( nat-Fin (succ-ℕ k) y)
        ( nat-Fin (succ-ℕ k) z))
      ( symmetric-cong-ℕ (succ-ℕ k)
        ( add-ℕ
          ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x y))
          ( nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x z)))
        ( add-ℕ
          ( (nat-Fin (succ-ℕ k) x) *ℕ (nat-Fin (succ-ℕ k) y))
          ( (nat-Fin (succ-ℕ k) x) *ℕ (nat-Fin (succ-ℕ k) z)))
        ( congruence-add-ℕ
          ( succ-ℕ k)
          { x = nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x y)}
          { y = nat-Fin (succ-ℕ k) (mul-Fin (succ-ℕ k) x z)}
          { x' = (nat-Fin (succ-ℕ k) x) *ℕ (nat-Fin (succ-ℕ k) y)}
          { y' = (nat-Fin (succ-ℕ k) x) *ℕ (nat-Fin (succ-ℕ k) z)}
          ( cong-mul-Fin x y)
          ( cong-mul-Fin x z))))

right-distributive-mul-add-Fin :
  (k : ℕ) (x y z : Fin k) →
  mul-Fin k (add-Fin k x y) z ＝ add-Fin k (mul-Fin k x z) (mul-Fin k y z)
right-distributive-mul-add-Fin k x y z =
  ( commutative-mul-Fin k (add-Fin k x y) z) ∙
  ( ( left-distributive-mul-add-Fin k z x y) ∙
    ( ap-add-Fin k (commutative-mul-Fin k z x) (commutative-mul-Fin k z y)))
```

## Properties

### Addition on `Fin k` is a binary equivalence

```agda
add-add-neg-Fin :
  (k : ℕ) (x y : Fin k) → add-Fin k x (add-Fin k (neg-Fin k x) y) ＝ y
add-add-neg-Fin (succ-ℕ k) x y =
  ( inv (associative-add-Fin (succ-ℕ k) x (neg-Fin (succ-ℕ k) x) y)) ∙
  ( ( ap (add-Fin' (succ-ℕ k) y) (right-inverse-law-add-Fin k x)) ∙
    ( left-unit-law-add-Fin k y))

add-neg-add-Fin :
  (k : ℕ) (x y : Fin k) → add-Fin k (neg-Fin k x) (add-Fin k x y) ＝ y
add-neg-add-Fin (succ-ℕ k) x y =
  ( inv (associative-add-Fin (succ-ℕ k) (neg-Fin (succ-ℕ k) x) x y)) ∙
  ( ( ap (add-Fin' (succ-ℕ k) y) (left-inverse-law-add-Fin k x)) ∙
    ( left-unit-law-add-Fin k y))

is-equiv-add-Fin :
  (k : ℕ) (x : Fin k) → is-equiv (add-Fin k x)
pr1 (pr1 (is-equiv-add-Fin k x)) = add-Fin k (neg-Fin k x)
pr2 (pr1 (is-equiv-add-Fin k x)) = add-add-neg-Fin k x
pr1 (pr2 (is-equiv-add-Fin k x)) = add-Fin k (neg-Fin k x)
pr2 (pr2 (is-equiv-add-Fin k x)) = add-neg-add-Fin k x

equiv-add-Fin :
  (k : ℕ) (x : Fin k) → Fin k ≃ Fin k
pr1 (equiv-add-Fin k x) = add-Fin k x
pr2 (equiv-add-Fin k x) = is-equiv-add-Fin k x

add-add-neg-Fin' :
  (k : ℕ) (x y : Fin k) → add-Fin' k x (add-Fin' k (neg-Fin k x) y) ＝ y
add-add-neg-Fin' (succ-ℕ k) x y =
  ( associative-add-Fin (succ-ℕ k) y (neg-Fin (succ-ℕ k) x) x) ∙
  ( ( ap (add-Fin (succ-ℕ k) y) (left-inverse-law-add-Fin k x)) ∙
    ( right-unit-law-add-Fin k y))

add-neg-add-Fin' :
  (k : ℕ) (x y : Fin k) → add-Fin' k (neg-Fin k x) (add-Fin' k x y) ＝ y
add-neg-add-Fin' (succ-ℕ k) x y =
  ( associative-add-Fin (succ-ℕ k) y x (neg-Fin (succ-ℕ k) x)) ∙
  ( ( ap (add-Fin (succ-ℕ k) y) (right-inverse-law-add-Fin k x)) ∙
    ( right-unit-law-add-Fin k y))

is-equiv-add-Fin' :
  (k : ℕ) (x : Fin k) → is-equiv (add-Fin' k x)
pr1 (pr1 (is-equiv-add-Fin' k x)) = add-Fin' k (neg-Fin k x)
pr2 (pr1 (is-equiv-add-Fin' k x)) = add-add-neg-Fin' k x
pr1 (pr2 (is-equiv-add-Fin' k x)) = add-Fin' k (neg-Fin k x)
pr2 (pr2 (is-equiv-add-Fin' k x)) = add-neg-add-Fin' k x

equiv-add-Fin' :
  (k : ℕ) (x : Fin k) → Fin k ≃ Fin k
pr1 (equiv-add-Fin' k x) = add-Fin' k x
pr2 (equiv-add-Fin' k x) = is-equiv-add-Fin' k x

is-injective-add-Fin :
  (k : ℕ) (x : Fin k) → is-injective (add-Fin k x)
is-injective-add-Fin k x {y} {z} p =
  ( inv (add-neg-add-Fin k x y)) ∙
  ( ( ap (add-Fin k (neg-Fin k x)) p) ∙
    ( add-neg-add-Fin k x z))

is-injective-add-Fin' :
  (k : ℕ) (x : Fin k) → is-injective (add-Fin' k x)
is-injective-add-Fin' k x {y} {z} p =
  is-injective-add-Fin k x
    ( commutative-add-Fin k x y ∙ (p ∙ commutative-add-Fin k z x))
```

### `neg-Fin` multiplies by `-1`

```agda
mul-neg-one-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) →
  mul-Fin (succ-ℕ k) (neg-one-Fin k) x ＝ neg-Fin (succ-ℕ k) x
mul-neg-one-Fin {k} x =
  is-injective-add-Fin
    ( succ-ℕ k)
    ( x)
    ( ( ( ap
          ( add-Fin' (succ-ℕ k) (mul-Fin (succ-ℕ k) (neg-one-Fin k) x))
          ( inv (left-unit-law-mul-Fin k x))) ∙
        ( ( inv
            ( right-distributive-mul-add-Fin
              ( succ-ℕ k)
              ( one-Fin k)
              ( neg-one-Fin k)
              ( x))) ∙
          ( ( ap
              ( mul-Fin' (succ-ℕ k) x)
              ( inv (is-add-one-succ-Fin k (neg-one-Fin k)))) ∙
            ( left-zero-law-mul-Fin k x)))) ∙
      ( inv (right-inverse-law-add-Fin k x)))
```

### The negative of `-1` is `1`

```agda
is-one-neg-neg-one-Fin :
  (k : ℕ) → is-one-Fin (succ-ℕ k) (neg-Fin (succ-ℕ k) (neg-one-Fin k))
is-one-neg-neg-one-Fin k =
  eq-mod-succ-cong-ℕ k
    ( dist-ℕ k (succ-ℕ k))
    ( 1)
    ( cong-identification-ℕ
      ( succ-ℕ k)
      ( is-one-dist-succ-ℕ k))
```

### The negative of `1` is `-1`

```agda
is-neg-one-neg-one-Fin :
  (k : ℕ) → neg-Fin (succ-ℕ k) (one-Fin k) ＝ (neg-one-Fin k)
is-neg-one-neg-one-Fin k =
  is-injective-add-Fin (succ-ℕ k) (one-Fin k)
    ( ( right-inverse-law-add-Fin k (one-Fin k)) ∙
      ( ( inv (left-inverse-law-add-Fin k (neg-one-Fin k))) ∙
        ( ap (add-Fin' (succ-ℕ k) (neg-one-Fin k)) (is-one-neg-neg-one-Fin k))))
```

### The predecessor function adds `-1`

```agda
is-add-neg-one-pred-Fin' :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  pred-Fin (succ-ℕ k) x ＝ add-Fin (succ-ℕ k) x (neg-one-Fin k)
is-add-neg-one-pred-Fin' k x =
  is-injective-succ-Fin
    ( succ-ℕ k)
    ( ( is-section-pred-Fin (succ-ℕ k) x) ∙
      ( ( ( ( inv (right-unit-law-add-Fin k x)) ∙
            ( ap
              ( add-Fin (succ-ℕ k) x)
              ( inv
                ( ( ap
                    ( add-Fin' (succ-ℕ k) (one-Fin k))
                    ( inv (is-neg-one-neg-one-Fin k))) ∙
                  ( left-inverse-law-add-Fin k (one-Fin k)))))) ∙
          ( inv
            ( associative-add-Fin (succ-ℕ k) x (neg-one-Fin k) (one-Fin k)))) ∙
        ( inv (is-add-one-succ-Fin' k (add-Fin (succ-ℕ k) x (neg-one-Fin k))))))

is-add-neg-one-pred-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  pred-Fin (succ-ℕ k) x ＝ add-Fin (succ-ℕ k) (neg-one-Fin k) x
is-add-neg-one-pred-Fin k x =
  ( is-add-neg-one-pred-Fin' k x) ∙
  ( commutative-add-Fin (succ-ℕ k) x (neg-one-Fin k))
```

### `neg-Fin` multiplies by `-1`

```agda
is-mul-neg-one-neg-Fin :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  neg-Fin (succ-ℕ k) x ＝ mul-Fin (succ-ℕ k) (neg-one-Fin k) x
is-mul-neg-one-neg-Fin k x =
  is-injective-add-Fin (succ-ℕ k) x
    ( ( right-inverse-law-add-Fin k x) ∙
      ( ( ( ( inv (left-zero-law-mul-Fin k x)) ∙
            ( ap
              ( mul-Fin' (succ-ℕ k) x)
              ( inv
                ( ( ap
                  ( add-Fin (succ-ℕ k) (one-Fin k))
                  ( inv (is-neg-one-neg-one-Fin k))) ∙
                  ( right-inverse-law-add-Fin k (one-Fin k)))))) ∙
          ( right-distributive-mul-add-Fin
            ( succ-ℕ k)
            ( one-Fin k)
            ( neg-one-Fin k)
            ( x))) ∙
        ( ap
          ( add-Fin'
            ( succ-ℕ k)
            ( mul-Fin (succ-ℕ k) (neg-one-Fin k) x))
          ( left-unit-law-mul-Fin k x))))

is-mul-neg-one-neg-Fin' :
  (k : ℕ) (x : Fin (succ-ℕ k)) →
  neg-Fin (succ-ℕ k) x ＝ mul-Fin (succ-ℕ k) x (neg-one-Fin k)
is-mul-neg-one-neg-Fin' k x =
  is-mul-neg-one-neg-Fin k x ∙ commutative-mul-Fin (succ-ℕ k) (neg-one-Fin k) x
```

### The negative of `0` is `0`

```agda
neg-zero-Fin : (k : ℕ) → neg-Fin (succ-ℕ k) (zero-Fin k) ＝ zero-Fin k
neg-zero-Fin k =
  ( inv (left-unit-law-add-Fin k (neg-Fin (succ-ℕ k) (zero-Fin k)))) ∙
  ( right-inverse-law-add-Fin k (zero-Fin k))
```

### The negative of a successor is the predecessor of the negative

```agda
neg-succ-Fin :
  (k : ℕ) (x : Fin k) → neg-Fin k (succ-Fin k x) ＝ pred-Fin k (neg-Fin k x)
neg-succ-Fin (succ-ℕ k) x =
  ( ap (neg-Fin (succ-ℕ k)) (is-add-one-succ-Fin' k x)) ∙
  ( ( is-mul-neg-one-neg-Fin k (add-Fin (succ-ℕ k) x (one-Fin k))) ∙
    ( ( left-distributive-mul-add-Fin
        ( succ-ℕ k)
        ( neg-one-Fin k)
        ( x)
        ( one-Fin k)) ∙
      ( ( ap-add-Fin
          ( succ-ℕ k)
          ( inv (is-mul-neg-one-neg-Fin k x))
          ( ( inv (is-mul-neg-one-neg-Fin k (one-Fin k))) ∙
            ( is-neg-one-neg-one-Fin k))) ∙
        ( inv (is-add-neg-one-pred-Fin' k (neg-Fin (succ-ℕ k) x))))))
```

### The negative of a predecessor is the successor of a negative

```agda
neg-pred-Fin :
  (k : ℕ) (x : Fin k) → neg-Fin k (pred-Fin k x) ＝ succ-Fin k (neg-Fin k x)
neg-pred-Fin (succ-ℕ k) x =
  ( ap (neg-Fin (succ-ℕ k)) (is-add-neg-one-pred-Fin' k x)) ∙
  ( ( is-mul-neg-one-neg-Fin k (add-Fin (succ-ℕ k) x (neg-one-Fin k))) ∙
    ( ( left-distributive-mul-add-Fin
        ( succ-ℕ k)
        ( neg-one-Fin k)
        ( x)
        ( neg-one-Fin k)) ∙
      ( ( ap-add-Fin
          ( succ-ℕ k)
          ( inv (is-mul-neg-one-neg-Fin k x))
          ( ( inv (is-mul-neg-one-neg-Fin k (neg-one-Fin k))) ∙
            ( is-one-neg-neg-one-Fin k))) ∙
        ( inv (is-add-one-succ-Fin' k (neg-Fin (succ-ℕ k) x))))))
```

### Taking negatives distributes over addition

```agda
distributive-neg-add-Fin :
  (k : ℕ) (x y : Fin k) →
  neg-Fin k (add-Fin k x y) ＝ add-Fin k (neg-Fin k x) (neg-Fin k y)
distributive-neg-add-Fin (succ-ℕ k) x y =
  ( is-mul-neg-one-neg-Fin k (add-Fin (succ-ℕ k) x y)) ∙
  ( ( left-distributive-mul-add-Fin (succ-ℕ k) (neg-one-Fin k) x y) ∙
    ( inv
      ( ap-add-Fin
        ( succ-ℕ k)
        ( is-mul-neg-one-neg-Fin k x)
        ( is-mul-neg-one-neg-Fin k y))))
```

### Predecessor laws of addition

```agda
left-predecessor-law-add-Fin :
  (k : ℕ) (x y : Fin k) →
  add-Fin k (pred-Fin k x) y ＝ pred-Fin k (add-Fin k x y)
left-predecessor-law-add-Fin (succ-ℕ k) x y =
  ( ap (add-Fin' (succ-ℕ k) y) (is-add-neg-one-pred-Fin k x)) ∙
  ( ( associative-add-Fin (succ-ℕ k) (neg-one-Fin k) x y) ∙
    ( inv (is-add-neg-one-pred-Fin k (add-Fin (succ-ℕ k) x y))))

right-predecessor-law-add-Fin :
  (k : ℕ) (x y : Fin k) →
  add-Fin k x (pred-Fin k y) ＝ pred-Fin k (add-Fin k x y)
right-predecessor-law-add-Fin (succ-ℕ k) x y =
  ( ap (add-Fin (succ-ℕ k) x) (is-add-neg-one-pred-Fin' k y)) ∙
  ( ( inv (associative-add-Fin (succ-ℕ k) x y (neg-one-Fin k))) ∙
    ( inv (is-add-neg-one-pred-Fin' k (add-Fin (succ-ℕ k) x y))))
```

### Negative laws of multiplication

```agda
left-negative-law-mul-Fin :
  (k : ℕ) (x y : Fin k) →
  mul-Fin k (neg-Fin k x) y ＝ neg-Fin k (mul-Fin k x y)
left-negative-law-mul-Fin (succ-ℕ k) x y =
  ( ap (mul-Fin' (succ-ℕ k) y) (is-mul-neg-one-neg-Fin k x)) ∙
  ( ( associative-mul-Fin (succ-ℕ k) (neg-one-Fin k) x y) ∙
    ( inv (is-mul-neg-one-neg-Fin k (mul-Fin (succ-ℕ k) x y))))

right-negative-law-mul-Fin :
  (k : ℕ) (x y : Fin k) →
  mul-Fin k x (neg-Fin k y) ＝ neg-Fin k (mul-Fin k x y)
right-negative-law-mul-Fin (succ-ℕ k) x y =
  ( commutative-mul-Fin (succ-ℕ k) x (neg-Fin (succ-ℕ k) y)) ∙
  ( ( left-negative-law-mul-Fin (succ-ℕ k) y x) ∙
    ( ap (neg-Fin (succ-ℕ k)) (commutative-mul-Fin (succ-ℕ k) y x)))
```

### Successor laws of multiplication

```agda
left-successor-law-mul-Fin :
  (k : ℕ) (x y : Fin k) →
  mul-Fin k (succ-Fin k x) y ＝ add-Fin k y (mul-Fin k x y)
left-successor-law-mul-Fin (succ-ℕ k) x y =
  ( ap (mul-Fin' (succ-ℕ k) y) (is-add-one-succ-Fin k x)) ∙
  ( ( right-distributive-mul-add-Fin (succ-ℕ k) (one-Fin k) x y) ∙
    ( ap
      ( add-Fin' (succ-ℕ k) (mul-Fin (succ-ℕ k) x y))
      ( left-unit-law-mul-Fin k y)))

right-successor-law-mul-Fin :
  (k : ℕ) (x y : Fin k) →
  mul-Fin k x (succ-Fin k y) ＝ add-Fin k x (mul-Fin k x y)
right-successor-law-mul-Fin (succ-ℕ k) x y =
  ( ap (mul-Fin (succ-ℕ k) x) (is-add-one-succ-Fin k y)) ∙
  ( ( left-distributive-mul-add-Fin (succ-ℕ k) x (one-Fin k) y) ∙
    ( ap
      ( add-Fin' (succ-ℕ k) (mul-Fin (succ-ℕ k) x y))
      ( right-unit-law-mul-Fin k x)))
```

### Predecessor laws of multiplication

```agda
left-predecessor-law-mul-Fin :
  (k : ℕ) (x y : Fin k) →
  mul-Fin k (pred-Fin k x) y ＝ add-Fin k (neg-Fin k y) (mul-Fin k x y)
left-predecessor-law-mul-Fin (succ-ℕ k) x y =
  ( ap (mul-Fin' (succ-ℕ k) y) (is-add-neg-one-pred-Fin k x)) ∙
  ( ( right-distributive-mul-add-Fin (succ-ℕ k) (neg-one-Fin k) x y) ∙
    ( ap
      ( add-Fin' (succ-ℕ k) (mul-Fin (succ-ℕ k) x y))
      ( inv (is-mul-neg-one-neg-Fin k y))))

right-predecessor-law-mul-Fin :
  (k : ℕ) (x y : Fin k) →
  mul-Fin k x (pred-Fin k y) ＝ add-Fin k (neg-Fin k x) (mul-Fin k x y)
right-predecessor-law-mul-Fin (succ-ℕ k) x y =
  ( ap (mul-Fin (succ-ℕ k) x) (is-add-neg-one-pred-Fin k y)) ∙
  ( ( left-distributive-mul-add-Fin (succ-ℕ k) x (neg-one-Fin k) y) ∙
    ( ap
      ( add-Fin' (succ-ℕ k) (mul-Fin (succ-ℕ k) x y))
      ( inv (is-mul-neg-one-neg-Fin' k x))))
```

### Taking negatives is an involution

```agda
neg-neg-Fin :
  (k : ℕ) (x : Fin k) → neg-Fin k (neg-Fin k x) ＝ x
neg-neg-Fin (succ-ℕ k) x =
  ( inv
    ( right-unit-law-add-Fin k (neg-Fin (succ-ℕ k) (neg-Fin (succ-ℕ k) x)))) ∙
  ( ( ap
      ( add-Fin (succ-ℕ k) (neg-Fin (succ-ℕ k) (neg-Fin (succ-ℕ k) x)))
      ( inv (left-inverse-law-add-Fin k x))) ∙
    ( ( inv
        ( associative-add-Fin
          ( succ-ℕ k)
          ( neg-Fin (succ-ℕ k) (neg-Fin (succ-ℕ k) x))
          ( neg-Fin (succ-ℕ k) x)
          ( x))) ∙
      ( ( ap
          ( add-Fin' (succ-ℕ k) x)
          ( left-inverse-law-add-Fin k (neg-Fin (succ-ℕ k) x))) ∙
        ( left-unit-law-add-Fin k x))))

is-equiv-neg-Fin :
  (k : ℕ) → is-equiv (neg-Fin k)
pr1 (pr1 (is-equiv-neg-Fin k)) = neg-Fin k
pr2 (pr1 (is-equiv-neg-Fin k)) = neg-neg-Fin k
pr1 (pr2 (is-equiv-neg-Fin k)) = neg-Fin k
pr2 (pr2 (is-equiv-neg-Fin k)) = neg-neg-Fin k

equiv-neg-Fin :
  (k : ℕ) → Fin k ≃ Fin k
pr1 (equiv-neg-Fin k) = neg-Fin k
pr2 (equiv-neg-Fin k) = is-equiv-neg-Fin k
```
