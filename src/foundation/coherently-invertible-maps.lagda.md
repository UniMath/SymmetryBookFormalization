---
title: Coherently invertible maps
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.coherently-invertible-maps where

open import foundation-core.coherently-invertible-maps public

open import foundation-core.contractible-maps using (is-contr-map-is-equiv)
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.fibers-of-maps using (fib)
open import foundation-core.functions using (_∘_; id)
open import foundation-core.functoriality-dependent-pair-types using (equiv-tot)
open import foundation-core.homotopies using
  ( _~_; htpy-right-whisk; htpy-left-whisk; refl-htpy)
open import foundation-core.propositions using
  ( is-prop; is-prop-is-proof-irrelevant; is-equiv-is-prop)
open import foundation-core.sections using (sec)
open import foundation-core.type-arithmetic-dependent-pair-types using
  ( assoc-Σ; map-assoc-Σ; map-inv-left-unit-law-Σ-is-contr;
    is-equiv-map-inv-left-unit-law-Σ-is-contr; is-equiv-map-assoc-Σ)
open import foundation-core.universe-levels using (Level; UU)

open import foundation.contractible-types using
  ( is-contr-equiv'; is-contr-Σ; is-contr-Π)
open import foundation.equivalences using
  ( is-equiv; is-equiv-is-coherently-invertible; is-contr-sec-is-equiv;
    is-emb-is-equiv; is-coherently-invertible-is-equiv; is-property-is-equiv;
    is-equiv-id; is-equiv-comp)
open import foundation.identity-types using (Id; ap; equiv-inv; refl)
open import foundation.type-theoretic-principle-of-choice using
  ( distributive-Π-Σ)
```

## Properties

### Being coherently invertible is a property

```agda
abstract
  is-prop-is-coherently-invertible :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-prop (is-coherently-invertible f)
  is-prop-is-coherently-invertible {l1} {l2} {A} {B} f =
    is-prop-is-proof-irrelevant
      ( λ H →
        is-contr-equiv'
          ( Σ (sec f)
            ( λ sf → Σ (((pr1 sf) ∘ f) ~ id)
              ( λ H → (htpy-right-whisk (pr2 sf) f) ~ (htpy-left-whisk f H))))
          ( assoc-Σ (B → A)
            ( λ g → ((f ∘ g) ~ id))
            ( λ sf → Σ (((pr1 sf) ∘ f) ~ id)
              ( λ H → (htpy-right-whisk (pr2 sf) f) ~ (htpy-left-whisk f H))))
          ( is-contr-Σ
            ( is-contr-sec-is-equiv (E H))
            ( pair (g H) (G H))
            ( is-contr-equiv'
              ( (x : A) →
                Σ ( Id (g H (f x)) x)
                  ( λ p → Id (G H (f x)) (ap f p)))
              ( distributive-Π-Σ)
              ( is-contr-Π
                ( λ x →
                  is-contr-equiv'
                    ( fib (ap f) (G H (f x)))
                    ( equiv-tot
                      ( λ p → equiv-inv (ap f p) (G H (f x))))
                    ( is-contr-map-is-equiv
                      ( is-emb-is-equiv (E H) (g H (f x)) x)
                      ( (G H) (f x))))))))
    where
    E : is-coherently-invertible f → is-equiv f
    E H = is-equiv-is-coherently-invertible H
    g : is-coherently-invertible f → (B → A)
    g H = pr1 H
    G : (H : is-coherently-invertible f) → (f ∘ g H) ~ id
    G H = pr1 (pr2 H)

abstract
  is-equiv-is-coherently-invertible-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-equiv (is-coherently-invertible-is-equiv {f = f})
  is-equiv-is-coherently-invertible-is-equiv f =
    is-equiv-is-prop
      ( is-property-is-equiv f)
      ( is-prop-is-coherently-invertible f)
      ( is-equiv-is-coherently-invertible)
```

### The type `has-inverse id` is equivalent to `id ~ id`

```agda
is-invertible-id-htpy-id-id :
  {l : Level} (A : UU l) →
  (id {A = A} ~ id {A = A}) → has-inverse (id {A = A})
pr1 (is-invertible-id-htpy-id-id A H) = id
pr1 (pr2 (is-invertible-id-htpy-id-id A H)) = refl-htpy
pr2 (pr2 (is-invertible-id-htpy-id-id A H)) = H

triangle-is-invertible-id-htpy-id-id :
  {l : Level} (A : UU l) →
  ( is-invertible-id-htpy-id-id A) ~
    ( ( map-assoc-Σ (A → A) (λ g → (id ∘ g) ~ id) (λ s → ((pr1 s) ∘ id) ~ id)) ∘
      ( map-inv-left-unit-law-Σ-is-contr
        { B = λ s → ((pr1 s) ∘ id) ~ id}
        ( is-contr-sec-is-equiv (is-equiv-id {_} {A}))
        ( pair id refl-htpy)))
triangle-is-invertible-id-htpy-id-id A H = refl

abstract
  is-equiv-invertible-id-htpy-id-id :
    {l : Level} (A : UU l) → is-equiv (is-invertible-id-htpy-id-id A)
  is-equiv-invertible-id-htpy-id-id A =
    is-equiv-comp
      ( is-invertible-id-htpy-id-id A)
      ( map-assoc-Σ (A → A) (λ g → (id ∘ g) ~ id) (λ s → ((pr1 s) ∘ id) ~ id))
      ( map-inv-left-unit-law-Σ-is-contr
        ( is-contr-sec-is-equiv is-equiv-id)
        ( pair id refl-htpy))
      ( triangle-is-invertible-id-htpy-id-id A)
      ( is-equiv-map-inv-left-unit-law-Σ-is-contr
        ( is-contr-sec-is-equiv is-equiv-id)
        ( pair id refl-htpy))
      ( is-equiv-map-assoc-Σ _ _ _)
```
