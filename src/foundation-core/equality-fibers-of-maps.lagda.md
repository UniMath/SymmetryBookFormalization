---
title: Equality in the fibers of a map
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.equality-fibers-of-maps where

open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.equality-dependent-pair-types using
  ( pair-eq-Σ; is-equiv-pair-eq-Σ)
open import foundation-core.equivalences using
  ( is-fiberwise-equiv; is-equiv-comp; is-equiv; _≃_)
open import foundation-core.fibers-of-maps using (fib)
open import foundation-core.functions using (_∘_)
open import foundation-core.functoriality-dependent-pair-types using
  ( tot; is-equiv-tot-is-fiberwise-equiv)
open import foundation-core.homotopies using (refl-htpy; _~_)
open import foundation.identity-types using
  ( _＝_; tr; ap; _∙_; inv; concat; right-unit; right-inv; refl;
    is-equiv-concat; is-equiv-inv; is-equiv-tr)
open import foundation-core.universe-levels using (Level; UU)
```

## Idea

In the file `foundation-core.fibers-of-a-map` we already gave one characterization of the identity type of `fib f b`, for an arbitrary map `f : A → B`. Here we give a second characterization, using the fibers of the action on identifications of `f`.

## Theorem

For any map `f : A → B` any `b : B` and any `x y : fib f b`, there is an equivalence

```md
(x ＝ y) ≃ fib (ap f) ((pr2 x) ∙ (inv (pr2 y)))
```

### Proof

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) {b : B}
  where

  fib-ap-eq-fib-fiberwise :
    (s t : fib f b) (p : (pr1 s) ＝ (pr1 t)) →
    ((tr (λ (a : A) → (f a) ＝ b) p (pr2 s)) ＝ (pr2 t)) →
    (ap f p ＝ ((pr2 s) ∙ (inv (pr2 t))))
  fib-ap-eq-fib-fiberwise (pair .x' p) (pair x' refl) refl =
    inv ∘ (concat right-unit refl)

  abstract
    is-fiberwise-equiv-fib-ap-eq-fib-fiberwise :
      (s t : fib f b) → is-fiberwise-equiv (fib-ap-eq-fib-fiberwise s t)
    is-fiberwise-equiv-fib-ap-eq-fib-fiberwise (pair x y) (pair .x refl) refl =
      is-equiv-comp
        ( fib-ap-eq-fib-fiberwise (pair x y) (pair x refl) refl)
        ( inv)
        ( concat right-unit refl)
        ( refl-htpy)
        ( is-equiv-concat right-unit refl)
        ( is-equiv-inv (y ∙ refl) refl)

  fib-ap-eq-fib :
    (s t : fib f b) → s ＝ t →
    fib (ap f {x = pr1 s} {y = pr1 t}) ((pr2 s) ∙ (inv (pr2 t)))
  pr1 (fib-ap-eq-fib s .s refl) = refl
  pr2 (fib-ap-eq-fib s .s refl) = inv (right-inv (pr2 s))

  triangle-fib-ap-eq-fib :
    (s t : fib f b) →
    ( fib-ap-eq-fib s t) ~
    ( (tot (fib-ap-eq-fib-fiberwise s t)) ∘ (pair-eq-Σ {s = s} {t}))
  triangle-fib-ap-eq-fib (pair x refl) .(pair x refl) refl = refl

  abstract
    is-equiv-fib-ap-eq-fib : (s t : fib f b) → is-equiv (fib-ap-eq-fib s t)
    is-equiv-fib-ap-eq-fib s t =
      is-equiv-comp
        ( fib-ap-eq-fib s t)
        ( tot (fib-ap-eq-fib-fiberwise s t))
        ( pair-eq-Σ {s = s} {t})
        ( triangle-fib-ap-eq-fib s t)
        ( is-equiv-pair-eq-Σ s t)
        ( is-equiv-tot-is-fiberwise-equiv
          ( is-fiberwise-equiv-fib-ap-eq-fib-fiberwise s t))

  equiv-fib-ap-eq-fib :
    (s t : fib f b) →
    (s ＝ t) ≃ fib (ap f {x = pr1 s} {y = pr1 t}) ((pr2 s) ∙ (inv (pr2 t)))
  pr1 (equiv-fib-ap-eq-fib s t) = fib-ap-eq-fib s t
  pr2 (equiv-fib-ap-eq-fib s t) = is-equiv-fib-ap-eq-fib s t

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (x y : A)
  where
  
  eq-fib-fib-ap :
    (q : f x ＝ f y) → (pair x q) ＝ (pair y refl) → fib (ap f {x} {y}) q
  eq-fib-fib-ap q =
    (tr (fib (ap f)) right-unit) ∘ (fib-ap-eq-fib f (pair x q) (pair y refl))

  abstract
    is-equiv-eq-fib-fib-ap :
      (q : (f x) ＝ (f y)) → is-equiv (eq-fib-fib-ap q)
    is-equiv-eq-fib-fib-ap q =
      is-equiv-comp
        ( eq-fib-fib-ap q)
        ( tr (fib (ap f)) right-unit)
        ( fib-ap-eq-fib f (pair x q) (pair y refl))
        ( refl-htpy)
        ( is-equiv-fib-ap-eq-fib f (pair x q) (pair y refl))
        ( is-equiv-tr (fib (ap f)) right-unit)
```
