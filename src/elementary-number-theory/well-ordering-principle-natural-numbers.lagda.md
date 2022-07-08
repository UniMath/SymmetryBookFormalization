---
title: The Well-Ordering Principle of the natural numbers
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.well-ordering-principle-natural-numbers where

open import elementary-number-theory.inequality-natural-numbers using
  ( leq-ℕ; leq-zero-ℕ; le-ℕ; leq-le-ℕ; contradiction-leq-ℕ; is-decidable-leq-ℕ;
    is-decidable-le-ℕ; is-prop-leq-ℕ; antisymmetric-leq-ℕ)
open import elementary-number-theory.lower-bounds-natural-numbers using
  ( is-lower-bound-ℕ; is-lower-bound-ℕ-Prop)
open import elementary-number-theory.natural-numbers using
  ( ℕ; zero-ℕ; succ-ℕ; ind-ℕ; is-zero-ℕ)
  
open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-fam; is-decidable-function-type;
    is-decidable-prod)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using (empty; ex-falso)
open import foundation.functions using (id; _∘_)
open import foundation.functoriality-dependent-pair-types using (tot)
open import foundation.hilberts-epsilon-operators using (ε-operator-Hilbert)
open import foundation.identity-types using (_＝_; refl)
open import foundation.negation using (¬)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop)
open import foundation.propositions using
  ( is-prop; is-prop-Π; is-prop-function-type; UU-Prop; all-elements-equal;
    type-Prop; prod-Prop; is-prop-type-Prop; is-prop-all-elements-equal)
open import foundation.subtypes using (eq-subtype; type-subtype)
open import foundation.unit-type using (star)
open import foundation.universe-levels using (UU; Level)
```

## Idea

The well-ordering principle of the natural numbers asserts that for every family of decidable types over ℕ equipped with a natural number `n` and an element `p : P n`, we can find a least natural number `n₀` with an element `p₀ : P n₀`. 

## Theorem

```agda
minimal-element-ℕ :
  {l : Level} (P : ℕ → UU l) → UU l
minimal-element-ℕ P = Σ ℕ (λ n → (P n) × (is-lower-bound-ℕ P n))

module _
  {l1 : Level} (P : ℕ → UU-Prop l1)
  where

  abstract
    all-elements-equal-minimal-element-ℕ :
      all-elements-equal (minimal-element-ℕ (λ n → type-Prop (P n)))
    all-elements-equal-minimal-element-ℕ
      (pair x (pair p l)) (pair y (pair q k)) =
      eq-subtype
        ( λ n →
          prod-Prop
            ( pair _ (is-prop-type-Prop (P n)))
            ( is-lower-bound-ℕ-Prop n))
        ( antisymmetric-leq-ℕ x y (l y q) (k x p))

  abstract
    is-prop-minimal-element-ℕ :
      is-prop (minimal-element-ℕ (λ n → type-Prop (P n)))
    is-prop-minimal-element-ℕ =
      is-prop-all-elements-equal all-elements-equal-minimal-element-ℕ

  minimal-element-ℕ-Prop : UU-Prop l1
  pr1 minimal-element-ℕ-Prop = minimal-element-ℕ (λ n → type-Prop (P n))
  pr2 minimal-element-ℕ-Prop = is-prop-minimal-element-ℕ

is-minimal-element-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P)
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
  is-minimal-element-succ-ℕ (λ x → P (succ-ℕ x)) (λ x → d (succ-ℕ x)) m pm
    ( λ m → is-lower-bound-m (succ-ℕ m))
    ( is-lower-bound-m zero-ℕ)
    ( n)
    ( psuccn)

well-ordering-principle-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P)
  (n : ℕ) (p : P (succ-ℕ n)) →
  is-decidable (P zero-ℕ) →
  minimal-element-ℕ (λ m → P (succ-ℕ m)) → minimal-element-ℕ P
pr1 (well-ordering-principle-succ-ℕ P d n p (inl p0) _) = zero-ℕ
pr1 (pr2 (well-ordering-principle-succ-ℕ P d n p (inl p0) _)) = p0
pr2 (pr2 (well-ordering-principle-succ-ℕ P d n p (inl p0) _)) m q = leq-zero-ℕ m
pr1
  ( well-ordering-principle-succ-ℕ P d n p
    (inr neg-p0) (pair m (pair pm is-min-m))) = succ-ℕ m
pr1
  ( pr2
    ( well-ordering-principle-succ-ℕ P d n p
      (inr neg-p0) (pair m (pair pm is-min-m)))) = pm
pr2
  ( pr2
    ( well-ordering-principle-succ-ℕ P d n p
      (inr neg-p0) (pair m (pair pm is-min-m)))) =
  is-minimal-element-succ-ℕ P d m pm is-min-m neg-p0

well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) →
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
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) (nP : Σ ℕ P) → ℕ
number-well-ordering-principle-ℕ P d nP =
  pr1 (well-ordering-principle-ℕ P d nP)

{- Also show that the well-ordering principle returns 0 if P 0 holds,
   independently of the input (pair n p) : Σ ℕ P. -}

is-zero-well-ordering-principle-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P)
  (n : ℕ) (p : P (succ-ℕ n)) (d0 : is-decidable (P zero-ℕ)) →
  (x : minimal-element-ℕ (λ m → P (succ-ℕ m))) (p0 : P zero-ℕ) →
  pr1 (well-ordering-principle-succ-ℕ P d n p d0 x) ＝ zero-ℕ
is-zero-well-ordering-principle-succ-ℕ P d n p (inl p0) x q0 =
  refl
is-zero-well-ordering-principle-succ-ℕ P d n p (inr np0) x q0 =
  ex-falso (np0 q0)

is-zero-well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) →
  (x : Σ ℕ P) → P zero-ℕ → is-zero-ℕ (number-well-ordering-principle-ℕ P d x)
is-zero-well-ordering-principle-ℕ P d (pair zero-ℕ p) p0 = refl
is-zero-well-ordering-principle-ℕ P d (pair (succ-ℕ m) p) =
  is-zero-well-ordering-principle-succ-ℕ P d m p (d zero-ℕ)
    ( well-ordering-principle-ℕ
      ( λ z → P (succ-ℕ z))
      ( λ x → d (succ-ℕ x))
      ( pair m p))
```

### Global choice

```agda
ε-operator-decidable-subtype-ℕ :
  {l1 : Level} (P : ℕ → UU-Prop l1)
  (d : (x : ℕ) → is-decidable (type-Prop (P x))) →
  ε-operator-Hilbert (type-subtype P)
ε-operator-decidable-subtype-ℕ {l1} P d t =
  tot ( λ x → pr1)
      ( apply-universal-property-trunc-Prop t
        ( minimal-element-ℕ-Prop P)
        ( well-ordering-principle-ℕ (λ x → type-Prop (P x)) d))
```
