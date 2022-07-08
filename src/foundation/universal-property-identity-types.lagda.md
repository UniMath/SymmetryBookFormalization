---
title: The universal property of identity types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.universal-property-identity-types where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( is-equiv; is-equiv-has-inverse; _≃_)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.identity-types using (_＝_; refl; ind-Id)
open import foundation.universe-levels using (Level; UU)
```

## Idea

The universal property of identity types characterizes families of maps out of the identity type. This universal property is also known as the type theoretic Yoneda lemma.

## Theorem

```agda
ev-refl :
  {l1 l2 : Level} {A : UU l1} (a : A) {B : (x : A) → a ＝ x → UU l2} →
  ((x : A) (p : a ＝ x) → B x p) → B a refl
ev-refl a f = f a refl

abstract
  is-equiv-ev-refl :
    {l1 l2 : Level} {A : UU l1} (a : A)
    {B : (x : A) → a ＝ x → UU l2} → is-equiv (ev-refl a {B = B})
  is-equiv-ev-refl a =
    is-equiv-has-inverse
      ( ind-Id a _)
      ( λ b → refl)
      ( λ f → eq-htpy
        ( λ x → eq-htpy
          ( ind-Id a
            ( λ x' p' → ind-Id a _ (f a refl) x' p' ＝ f x' p')
            ( refl) x)))

equiv-ev-refl :
  {l1 l2 : Level} {A : UU l1} (a : A) {B : (x : A) → a ＝ x → UU l2} →
  ((x : A) (p : a ＝ x) → B x p) ≃ (B a refl)
pr1 (equiv-ev-refl a) = ev-refl a
pr2 (equiv-ev-refl a) = is-equiv-ev-refl a
```
