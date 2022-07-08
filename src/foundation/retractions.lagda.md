---
title: Retractions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.retractions where

open import foundation-core.retractions public

open import foundation.coslice using
  ( htpy-hom-coslice; extensionality-hom-coslice; eq-htpy-hom-coslice)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.functions using (_∘_; id)
open import foundation.equivalences using
  ( retraction-comp; retraction-comp'; _≃_)
open import foundation.identity-types using (inv; _∙_; ap)
open import foundation.injective-maps using (is-injective)
open import foundation.homotopies using
  ( _~_; _·l_; inv-htpy; assoc-htpy; _·r_; _∙h_; ap-concat-htpy'; refl-htpy;
    left-inv-htpy)
open import foundation.identity-types using (Id)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Properties

### Characterizing the identity type of `retr f`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where
  
  htpy-retr : retr f → retr f → UU (l1 ⊔ l2)
  htpy-retr = htpy-hom-coslice

  extensionality-retr : (g h : retr f) → Id g h ≃ htpy-retr g h
  extensionality-retr g h = extensionality-hom-coslice g h

  eq-htpy-retr :
    ( g h : retr f) (H : pr1 g ~ pr1 h) (K : (pr2 g) ~ ((H ·r f) ∙h pr2 h)) →
    Id g h
  eq-htpy-retr g h = eq-htpy-hom-coslice g h 
```

### If the left factor in a commuting traingle has a retraction, then the type of retractions of the right factor is a retract of the type of retractions of the composite

```agda
isretr-retraction-comp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (retr-g : retr g) →
  ((retraction-comp f g h H retr-g) ∘ (retraction-comp' f g h H retr-g)) ~ id
isretr-retraction-comp f g h H (pair l L) (pair k K) =
  eq-htpy-retr
    ( ( retraction-comp f g h H (pair l L)
        ( retraction-comp' f g h H (pair l L)
          ( pair k K))))
    ( pair k K)
    ( k ·l L)
    ( ( inv-htpy
        ( assoc-htpy
          ( inv-htpy ((k ∘ l) ·l H))
          ( (k ∘ l) ·l H)
          ( (k ·l (L ·r h)) ∙h K))) ∙h
      ( ap-concat-htpy'
        ( (inv-htpy ((k ∘ l) ·l H)) ∙h ((k ∘ l) ·l H))
        ( refl-htpy)
        ( (k ·l (L ·r h)) ∙h K)
        ( left-inv-htpy ((k ∘ l) ·l H))))
  
retr-right-factor-retract-of-retr-left-factor :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  retr g → (retr h) retract-of (retr f)
pr1 (retr-right-factor-retract-of-retr-left-factor f g h H retr-g) =
  retraction-comp' f g h H retr-g
pr1 (pr2 (retr-right-factor-retract-of-retr-left-factor f g h H retr-g)) =
  retraction-comp f g h H retr-g
pr2 (pr2 (retr-right-factor-retract-of-retr-left-factor f g h H retr-g)) =
  isretr-retraction-comp f g h H retr-g
```

```agda
abstract
  is-injective-retr :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → retr f →
    is-injective f
  is-injective-retr f (pair h H) {x} {y} p = (inv (H x)) ∙ (ap h p ∙ H y)
```
