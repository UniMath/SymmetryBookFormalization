---
title: The uniqueness of set quotients
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.uniqueness-set-quotients where

open import foundation.contractible-types using (is-contr; center)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalence-relations using
  ( Eq-Rel)
open import foundation.equivalences using
  ( is-equiv; is-equiv-has-inverse; is-equiv-comp; is-equiv-precomp-is-equiv;
    is-equiv-left-factor; _≃_; map-equiv; is-property-is-equiv)
open import foundation.function-extensionality using (htpy-eq)
open import foundation.functions using  (_∘_; id; precomp)
open import foundation.homotopies using (_~_; refl-htpy; inv-htpy; _·l_)
open import foundation.identity-types using (_＝_; _∙_; ap; inv)
open import foundation.injective-maps using (is-injective-is-equiv)
open import foundation.reflecting-maps-equivalence-relations using
  ( reflecting-map-Eq-Rel; eq-htpy-reflecting-map-Eq-Rel;
    map-reflecting-map-Eq-Rel)
open import foundation.sets using (UU-Set; type-Set; type-hom-Set)
open import foundation.subtype-identity-principle using
  ( is-contr-total-Eq-subtype)
open import foundation.universal-property-set-quotients using
  ( precomp-Set-Quotient; is-set-quotient; precomp-id-Set-Quotient;
    universal-property-set-quotient-is-set-quotient;
    map-universal-property-set-quotient-is-set-quotient;
    triangle-universal-property-set-quotient-is-set-quotient)
open import foundation.universe-levels using (Level; UU)
```

## Idea

The universal property of set quotients implies that set quotients are uniquely unique.

## Properties

### Uniqueness of set quotients

```agda
precomp-comp-Set-Quotient :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : UU-Set l3) (f : reflecting-map-Eq-Rel R (type-Set B))
  (C : UU-Set l4) (g : type-hom-Set B C)
  (D : UU-Set l5) (h : type-hom-Set C D) →
  ( precomp-Set-Quotient R B f D (h ∘ g)) ＝
  ( precomp-Set-Quotient R C (precomp-Set-Quotient R B f C g) D h)
precomp-comp-Set-Quotient R B f C g D h =
  eq-htpy-reflecting-map-Eq-Rel R D
    ( precomp-Set-Quotient R B f D (h ∘ g))
    ( precomp-Set-Quotient R C (precomp-Set-Quotient R B f C g) D h)
    ( refl-htpy)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : UU-Set l3) (f : reflecting-map-Eq-Rel R (type-Set B))
  (C : UU-Set l4) (g : reflecting-map-Eq-Rel R (type-Set C))
  {h : type-Set B → type-Set C}
  (H : (h ∘ map-reflecting-map-Eq-Rel R f) ~ map-reflecting-map-Eq-Rel R g)
  where

  abstract
    is-equiv-is-set-quotient-is-set-quotient :
      ({l : Level} → is-set-quotient l R B f) →
      ({l : Level} → is-set-quotient l R C g) →
      is-equiv h
    is-equiv-is-set-quotient-is-set-quotient Uf Ug =
      is-equiv-has-inverse 
        ( pr1 (center K))
        ( htpy-eq
          ( is-injective-is-equiv
            ( Ug C)
            { h ∘ k}
            { id}
            ( ( precomp-comp-Set-Quotient R C g B k C h) ∙
              ( ( ap (λ t → precomp-Set-Quotient R B t C h) α) ∙
                ( ( eq-htpy-reflecting-map-Eq-Rel R C
                    ( precomp-Set-Quotient R B f C h) g H) ∙
                  ( inv (precomp-id-Set-Quotient R C g)))))))
        ( htpy-eq
          ( is-injective-is-equiv
            ( Uf B)
            { k ∘ h}
            { id}
            ( ( precomp-comp-Set-Quotient R B f C h B k) ∙
              ( ( ap
                  ( λ t → precomp-Set-Quotient R C t B k)
                  ( eq-htpy-reflecting-map-Eq-Rel R C
                    ( precomp-Set-Quotient R B f C h) g H)) ∙
                ( ( α) ∙
                  ( inv (precomp-id-Set-Quotient R B f)))))))
      where
      K : is-contr
            ( Σ ( type-hom-Set C B)
                ( λ h →
                  ( h ∘ map-reflecting-map-Eq-Rel R g) ~
                  ( map-reflecting-map-Eq-Rel R f)))
      K = universal-property-set-quotient-is-set-quotient R C g Ug B f
      k : type-Set C → type-Set B
      k = pr1 (center K)
      α : precomp-Set-Quotient R C g B k ＝ f
      α = eq-htpy-reflecting-map-Eq-Rel R B
            ( precomp-Set-Quotient R C g B k)
            ( f)
            ( pr2 (center K))

  abstract
    is-set-quotient-is-set-quotient-is-equiv :
      is-equiv h → ({l : Level} → is-set-quotient l R B f) →
      {l : Level} → is-set-quotient l R C g
    is-set-quotient-is-set-quotient-is-equiv E Uf {l} X =
      is-equiv-comp
        ( precomp-Set-Quotient R C g X)
        ( precomp-Set-Quotient R B f X)
        ( precomp h (type-Set X))
        ( λ k →
          eq-htpy-reflecting-map-Eq-Rel R X
            ( precomp-Set-Quotient R C g X k)
            ( precomp-Set-Quotient R B f X (k ∘ h))
            ( inv-htpy (k ·l H)))
        ( is-equiv-precomp-is-equiv h E (type-Set X))
        ( Uf X)

  abstract
    is-set-quotient-is-equiv-is-set-quotient :
      ({l : Level} → is-set-quotient l R C g) → is-equiv h →
      {l : Level} → is-set-quotient l R B f
    is-set-quotient-is-equiv-is-set-quotient Ug E {l} X =
      is-equiv-left-factor
        ( precomp-Set-Quotient R C g X)
        ( precomp-Set-Quotient R B f X)
        ( precomp h (type-Set X))
        ( λ k →
          eq-htpy-reflecting-map-Eq-Rel R X
            ( precomp-Set-Quotient R C g X k)
            ( precomp-Set-Quotient R B f X (k ∘ h))
            ( inv-htpy (k ·l H)))
        ( Ug X)
        ( is-equiv-precomp-is-equiv h E (type-Set X))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : UU-Set l3) (f : reflecting-map-Eq-Rel R (type-Set B)) 
  (Uf : {l : Level} → is-set-quotient l R B f)
  (C : UU-Set l4) (g : reflecting-map-Eq-Rel R (type-Set C))
  (Ug : {l : Level} → is-set-quotient l R C g)
  where

  abstract
    uniqueness-set-quotient :
      is-contr
        ( Σ ( type-Set B ≃ type-Set C)
            ( λ e →
              ( map-equiv e ∘ map-reflecting-map-Eq-Rel R f) ~
              ( map-reflecting-map-Eq-Rel R g)))
    uniqueness-set-quotient =
      is-contr-total-Eq-subtype
        ( universal-property-set-quotient-is-set-quotient R B f Uf C g)
        ( is-property-is-equiv)
        ( map-universal-property-set-quotient-is-set-quotient R B f Uf C g)
        ( triangle-universal-property-set-quotient-is-set-quotient R B f Uf C g)
        ( is-equiv-is-set-quotient-is-set-quotient R B f C g
          ( triangle-universal-property-set-quotient-is-set-quotient
            R B f Uf C g)
          ( Uf)
          ( Ug))

  equiv-uniqueness-set-quotient : type-Set B ≃ type-Set C
  equiv-uniqueness-set-quotient =
    pr1 (center uniqueness-set-quotient)

  map-equiv-uniqueness-set-quotient : type-Set B → type-Set C
  map-equiv-uniqueness-set-quotient =  map-equiv equiv-uniqueness-set-quotient

  triangle-uniqueness-set-quotient :
    ( map-equiv-uniqueness-set-quotient ∘ map-reflecting-map-Eq-Rel R f) ~
    ( map-reflecting-map-Eq-Rel R g)
  triangle-uniqueness-set-quotient =
    pr2 (center uniqueness-set-quotient)
```
