# The well-ordering principle of the natural numbers

```agda
module elementary-number-theory.well-ordering-principle-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.lower-bounds-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-type-families
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.functoriality-dependent-pair-types
open import foundation.hilberts-epsilon-operators
open import foundation.identity-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

The well-ordering principle of the natural numbers asserts that for every family
of decidable types over ℕ equipped with a natural number `n` and an element
`p : P n`, we can find a least natural number `n₀` with an element `p₀ : P n₀`.

## Theorem

```agda
minimal-element-ℕ :
  {l : Level} (P : ℕ → UU l) → UU l
minimal-element-ℕ P = Σ ℕ (λ n → (P n) × (is-lower-bound-ℕ P n))

module _
  {l1 : Level} (P : ℕ → Prop l1)
  where

  all-elements-equal-minimal-element-ℕ :
    all-elements-equal (minimal-element-ℕ (λ n → type-Prop (P n)))
  all-elements-equal-minimal-element-ℕ
    (pair x (pair p l)) (pair y (pair q k)) =
    eq-type-subtype
      ( λ n →
        product-Prop
          ( pair _ (is-prop-type-Prop (P n)))
          ( is-lower-bound-ℕ-Prop n))
      ( antisymmetric-leq-ℕ x y (l y q) (k x p))

  is-prop-minimal-element-ℕ :
    is-prop (minimal-element-ℕ (λ n → type-Prop (P n)))
  is-prop-minimal-element-ℕ =
    is-prop-all-elements-equal all-elements-equal-minimal-element-ℕ

  minimal-element-ℕ-Prop : Prop l1
  pr1 minimal-element-ℕ-Prop = minimal-element-ℕ (λ n → type-Prop (P n))
  pr2 minimal-element-ℕ-Prop = is-prop-minimal-element-ℕ

is-minimal-element-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-family P)
  (m : ℕ) (pm : P (succ-ℕ m))
  (is-lower-bound-m : is-lower-bound-ℕ (λ x → P (succ-ℕ x)) m) →
  ¬ (P zero-ℕ) → is-lower-bound-ℕ P (succ-ℕ m)
is-minimal-element-succ-ℕ P d m pm is-lower-bound-m neg-p0 zero-ℕ p0 =
  ex-falso (neg-p0 p0)
is-minimal-element-succ-ℕ
  P d zero-ℕ pm is-lower-bound-m neg-p0 (succ-ℕ n) psuccn =
  leq-zero-ℕ n
is-minimal-element-succ-ℕ
  P d (succ-ℕ m) pm is-lower-bound-m neg-p0 (succ-ℕ n) psuccn =
  is-lower-bound-m n psuccn

well-ordering-principle-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-family P)
  (n : ℕ) (p : P (succ-ℕ n)) →
  is-decidable (P zero-ℕ) →
  minimal-element-ℕ (λ m → P (succ-ℕ m)) → minimal-element-ℕ P
well-ordering-principle-succ-ℕ P d n p (inl p0) u =
  ( 0 , p0 , λ m q → leq-zero-ℕ m)
well-ordering-principle-succ-ℕ P d n p (inr neg-p0) (m , pm , is-min-m) =
  ( succ-ℕ m , pm , is-minimal-element-succ-ℕ P d m pm is-min-m neg-p0)

well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-family P) →
  Σ ℕ P → minimal-element-ℕ P
pr1 (well-ordering-principle-ℕ P d (pair zero-ℕ p)) = zero-ℕ
pr1 (pr2 (well-ordering-principle-ℕ P d (pair zero-ℕ p))) = p
pr2 (pr2 (well-ordering-principle-ℕ P d (pair zero-ℕ p))) m q = leq-zero-ℕ m
well-ordering-principle-ℕ P d (pair (succ-ℕ n) p) =
  well-ordering-principle-succ-ℕ P d n p (d zero-ℕ)
    ( well-ordering-principle-ℕ
      ( λ m → P (succ-ℕ m))
      ( λ m → d (succ-ℕ m))
      ( pair n p))

number-well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-family P) (nP : Σ ℕ P) → ℕ
number-well-ordering-principle-ℕ P d nP =
  pr1 (well-ordering-principle-ℕ P d nP)
```

### The well-ordering principle returns `0` if `P 0` holds

This is independently of the input `(pair n p) : Σ ℕ P`.

```agda
is-zero-well-ordering-principle-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-family P)
  (n : ℕ) (p : P (succ-ℕ n)) (d0 : is-decidable (P zero-ℕ)) →
  (x : minimal-element-ℕ (λ m → P (succ-ℕ m))) (p0 : P zero-ℕ) →
  pr1 (well-ordering-principle-succ-ℕ P d n p d0 x) ＝ zero-ℕ
is-zero-well-ordering-principle-succ-ℕ P d n p (inl p0) x q0 =
  refl
is-zero-well-ordering-principle-succ-ℕ P d n p (inr np0) x q0 =
  ex-falso (np0 q0)

is-zero-well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-family P) →
  (x : Σ ℕ P) → P zero-ℕ → is-zero-ℕ (number-well-ordering-principle-ℕ P d x)
is-zero-well-ordering-principle-ℕ P d (pair zero-ℕ p) p0 = refl
is-zero-well-ordering-principle-ℕ P d (pair (succ-ℕ m) p) =
  is-zero-well-ordering-principle-succ-ℕ P d m p (d zero-ℕ)
    ( well-ordering-principle-ℕ
      ( λ z → P (succ-ℕ z))
      ( λ x → d (succ-ℕ x))
      ( pair m p))
```

### The ε-operator for decidable subtypes of ℕ

```agda
ε-operator-decidable-subtype-ℕ :
  {l1 : Level} (P : ℕ → Prop l1)
  (d : (x : ℕ) → is-decidable (type-Prop (P x))) →
  ε-operator-Hilbert (type-subtype P)
ε-operator-decidable-subtype-ℕ {l1} P d t =
  tot ( λ x → pr1)
      ( apply-universal-property-trunc-Prop t
        ( minimal-element-ℕ-Prop P)
        ( well-ordering-principle-ℕ (λ x → type-Prop (P x)) d))
```
