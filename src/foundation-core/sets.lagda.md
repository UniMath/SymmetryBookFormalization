---
title: Sets
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.sets where

open import foundation-core.contractible-types using (contraction)
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.equivalences using (is-equiv; _≃_)
open import foundation-core.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id-retr)
open import foundation-core.identity-types using
  ( _＝_; refl; inv; _∙_; ind-Id)
open import foundation-core.propositions using
  ( is-prop; UU-Prop; all-elements-equal; is-prop-all-elements-equal;
    is-proof-irrelevant-is-prop; eq-is-prop; is-prop-is-equiv')
open import foundation-core.truncated-types using
  ( is-trunc-succ-is-trunc; truncated-type-succ-Truncated-Type;
    is-trunc-is-equiv; is-trunc-equiv; is-trunc-is-equiv'; is-trunc-equiv')
open import foundation-core.truncation-levels using
  ( neg-one-𝕋; zero-𝕋)
open import foundation-core.universe-levels using (Level; UU; _⊔_; lsuc)
```

## Idea

A type is a set if its identity types are propositions.

## Definition

```agda
is-set :
  {i : Level} → UU i → UU i
is-set A = (x y : A) → is-prop (x ＝ y)

UU-Set :
  (i : Level) → UU (lsuc i)
UU-Set i = Σ (UU i) is-set

module _
  {l : Level} (X : UU-Set l)
  where

  type-Set : UU l
  type-Set = pr1 X

  abstract
    is-set-type-Set : is-set type-Set
    is-set-type-Set = pr2 X

  Id-Prop : (x y : type-Set) → UU-Prop l
  pr1 (Id-Prop x y) = (x ＝ y)
  pr2 (Id-Prop x y) = is-set-type-Set x y
```

## Properties

### A type is a set if and only if it satisfies Streicher's axiom K

```agda
axiom-K :
  {i : Level} → UU i → UU i
axiom-K A = (x : A) (p : x ＝ x) → refl ＝ p

module _
  {l : Level} {A : UU l}
  where

  abstract
    is-set-axiom-K' : axiom-K A → (x y : A) → all-elements-equal (x ＝ y)
    is-set-axiom-K' K x .x refl q with K x q
    ... | refl = refl

  abstract
    is-set-axiom-K : axiom-K A → is-set A
    is-set-axiom-K H x y = is-prop-all-elements-equal (is-set-axiom-K' H x y) 

  abstract
    axiom-K-is-set : is-set A → axiom-K A
    axiom-K-is-set H x p =
      ( inv (contraction (is-proof-irrelevant-is-prop (H x x) refl) refl)) ∙ 
      ( contraction (is-proof-irrelevant-is-prop (H x x) refl) p)
```

### If a reflexive binary relation maps into the identity type of A, then A is a set

```
module _
  {l1 l2 : Level} {A : UU l1} (R : A → A → UU l2)
  (p : (x y : A) → is-prop (R x y)) (ρ : (x : A) → R x x)
  (i : (x y : A) → R x y → x ＝ y)
  where

  abstract
    is-equiv-prop-in-id : (x y : A) → is-equiv (i x y)
    is-equiv-prop-in-id x =
      fundamental-theorem-id-retr x (i x)
        ( λ y →
          pair
            ( ind-Id x (λ z p → R x z) (ρ x) y)
            ( λ r → eq-is-prop (p x y)))

  abstract
    is-set-prop-in-id : is-set A
    is-set-prop-in-id x y = is-prop-is-equiv' (is-equiv-prop-in-id x y) (p x y)
```

### Any proposition is a set

```agda
abstract
  is-set-is-prop :
    {l : Level} {P : UU l} → is-prop P → is-set P
  is-set-is-prop = is-trunc-succ-is-trunc neg-one-𝕋

set-Prop :
  {l : Level} → UU-Prop l → UU-Set l
set-Prop P = truncated-type-succ-Truncated-Type neg-one-𝕋 P
```

### Sets are closed under equivalences

```agda
abstract
  is-set-is-equiv :
    {i j : Level} {A : UU i} (B : UU j) (f : A → B) → is-equiv f →
    is-set B → is-set A
  is-set-is-equiv = is-trunc-is-equiv zero-𝕋

abstract
  is-set-equiv :
    {i j : Level} {A : UU i} (B : UU j) (e : A ≃ B) →
    is-set B → is-set A
  is-set-equiv = is-trunc-equiv zero-𝕋

abstract
  is-set-is-equiv' :
    {i j : Level} (A : UU i) {B : UU j} (f : A → B) → is-equiv f →
    is-set A → is-set B
  is-set-is-equiv' = is-trunc-is-equiv' zero-𝕋

abstract
  is-set-equiv' :
    {i j : Level} (A : UU i) {B : UU j} (e : A ≃ B) →
    is-set A → is-set B
  is-set-equiv' = is-trunc-equiv' zero-𝕋
```
