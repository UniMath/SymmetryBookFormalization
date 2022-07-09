---
title: Isomorphisms of semigroups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.isomorphisms-semigroups where

open import category-theory.isomorphisms-large-precategories using
  ( is-iso-Large-Precat; iso-Large-Precat; hom-iso-Large-Precat;
    is-iso-hom-iso-Large-Precat; hom-inv-iso-Large-Precat;
    is-sec-hom-inv-iso-Large-Precat; is-retr-hom-inv-iso-Large-Precat;
    is-prop-is-iso-Large-Precat; id-iso-Large-Precat; iso-eq-Large-Precat)

open import foundation.contractible-types using (is-contr; is-contr-equiv')
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( is-equiv; map-inv-is-equiv; is-emb-is-equiv; issec-map-inv-is-equiv;
    isretr-map-inv-is-equiv; is-equiv-has-inverse; _≃_;
    is-property-is-equiv; _∘e_)
open import foundation.function-extensionality using (htpy-eq)
open import foundation.functoriality-dependent-pair-types using (equiv-tot)
open import foundation.identity-types using (Id; _∙_; ap; inv)
open import foundation.propositions using (is-prop)
open import foundation.subtypes using (equiv-type-subtype)
open import foundation.type-arithmetic-dependent-pair-types using
  ( equiv-right-swap-Σ)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import group-theory.equivalences-semigroups using
  ( preserves-mul-equiv-Semigroup; equiv-Semigroup;
    is-contr-total-equiv-Semigroup)
open import group-theory.homomorphisms-semigroups using
  ( type-hom-Semigroup; comp-hom-Semigroup; id-hom-Semigroup;
    map-hom-Semigroup; preserves-mul-Semigroup; eq-htpy-hom-Semigroup)
open import group-theory.precategory-of-semigroups using
  ( Semigroup-Large-Precat)
open import group-theory.semigroups using
  ( Semigroup; mul-Semigroup; type-Semigroup)
```

## Idea

Isomorphisms of semigroups are homomorphisms that have a two-sided inverse.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where
  
  is-iso-hom-Semigroup : (f : type-hom-Semigroup G H) → UU (l1 ⊔ l2)
  is-iso-hom-Semigroup f =
    is-iso-Large-Precat Semigroup-Large-Precat {X = G} {Y = H} f

  inv-is-iso-hom-Semigroup :
    (f : type-hom-Semigroup G H) →
    is-iso-hom-Semigroup f → type-hom-Semigroup H G
  inv-is-iso-hom-Semigroup f = pr1

  type-iso-Semigroup : UU (l1 ⊔ l2)
  type-iso-Semigroup = iso-Large-Precat Semigroup-Large-Precat G H
  
  hom-iso-Semigroup : type-iso-Semigroup → type-hom-Semigroup G H
  hom-iso-Semigroup = hom-iso-Large-Precat Semigroup-Large-Precat G H

  is-iso-hom-iso-Semigroup :
    (f : type-iso-Semigroup) → is-iso-hom-Semigroup (hom-iso-Semigroup f)
  is-iso-hom-iso-Semigroup =
    is-iso-hom-iso-Large-Precat Semigroup-Large-Precat G H

  hom-inv-iso-Semigroup : type-iso-Semigroup → type-hom-Semigroup H G
  hom-inv-iso-Semigroup = hom-inv-iso-Large-Precat Semigroup-Large-Precat G H

  issec-hom-inv-iso-Semigroup :
    (f : type-iso-Semigroup) →
    Id ( comp-hom-Semigroup H G H
         ( hom-iso-Semigroup f)
         ( hom-inv-iso-Semigroup f))
       ( id-hom-Semigroup H)
  issec-hom-inv-iso-Semigroup =
    is-sec-hom-inv-iso-Large-Precat Semigroup-Large-Precat G H

  isretr-hom-inv-iso-Semigroup :
    (f : type-iso-Semigroup) →
    Id ( comp-hom-Semigroup G H G
         ( hom-inv-iso-Semigroup f)
         ( hom-iso-Semigroup f))
       ( id-hom-Semigroup G)
  isretr-hom-inv-iso-Semigroup =
    is-retr-hom-inv-iso-Large-Precat Semigroup-Large-Precat G H
```

## Properties

### Being an isomorphism is a property

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  abstract
    is-prop-is-iso-hom-Semigroup :
      (f : type-hom-Semigroup G H) → is-prop (is-iso-hom-Semigroup G H f)
    is-prop-is-iso-hom-Semigroup =
      is-prop-is-iso-Large-Precat Semigroup-Large-Precat G H
```

### The inverse of an equivalence of semigroups preserves the binary operation

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  abstract
    preserves-mul-map-inv-is-equiv-Semigroup :
      ( f : type-hom-Semigroup G H)
      ( is-equiv-f : is-equiv (map-hom-Semigroup G H f)) →
      preserves-mul-Semigroup H G (map-inv-is-equiv is-equiv-f)
    preserves-mul-map-inv-is-equiv-Semigroup (pair f μ-f) is-equiv-f x y =
      map-inv-is-equiv
        ( is-emb-is-equiv is-equiv-f
          ( map-inv-is-equiv is-equiv-f (mul-Semigroup H x y))
          ( mul-Semigroup G
            ( map-inv-is-equiv is-equiv-f x)
            ( map-inv-is-equiv is-equiv-f y)))
        ( ( ( issec-map-inv-is-equiv is-equiv-f (mul-Semigroup H x y)) ∙
            ( ( ap ( λ t → mul-Semigroup H t y)
                   ( inv (issec-map-inv-is-equiv is-equiv-f x))) ∙
              ( ap
                ( mul-Semigroup H (f (map-inv-is-equiv is-equiv-f x)))
                ( inv (issec-map-inv-is-equiv is-equiv-f y))))) ∙
          ( inv
            ( μ-f
              ( map-inv-is-equiv is-equiv-f x)
              ( map-inv-is-equiv is-equiv-f y))))
```

### A homomorphism of semigroups is an equivalence of semigroups if and only if it is an isomorphism

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  abstract
    is-iso-is-equiv-hom-Semigroup :
      (f : type-hom-Semigroup G H) → is-equiv (pr1 f) →
      is-iso-hom-Semigroup G H f
    pr1 (pr1 (is-iso-is-equiv-hom-Semigroup (pair f μ-f) is-equiv-f)) =
      map-inv-is-equiv is-equiv-f
    pr2 (pr1 (is-iso-is-equiv-hom-Semigroup (pair f μ-f) is-equiv-f)) =
      preserves-mul-map-inv-is-equiv-Semigroup G H (pair f μ-f) is-equiv-f
    pr1 (pr2 (is-iso-is-equiv-hom-Semigroup (pair f μ-f) is-equiv-f)) =
      eq-htpy-hom-Semigroup H H (issec-map-inv-is-equiv is-equiv-f)
    pr2 (pr2 (is-iso-is-equiv-hom-Semigroup (pair f μ-f) is-equiv-f)) =
      eq-htpy-hom-Semigroup G G (isretr-map-inv-is-equiv is-equiv-f)         

  abstract
    is-equiv-is-iso-hom-Semigroup :
      (f : type-hom-Semigroup G H) → is-iso-hom-Semigroup G H f →
      is-equiv (pr1 f)
    is-equiv-is-iso-hom-Semigroup
      ( pair f μ-f)
      ( pair (pair g μ-g) (pair issec isretr)) =
      is-equiv-has-inverse g
        ( htpy-eq (ap pr1 issec))
        ( htpy-eq (ap pr1 isretr))

  equiv-iso-equiv-Semigroup : equiv-Semigroup G H ≃ type-iso-Semigroup G H
  equiv-iso-equiv-Semigroup =
    ( equiv-type-subtype
      ( λ f → is-property-is-equiv (map-hom-Semigroup G H f))
      ( is-prop-is-iso-hom-Semigroup G H)
      ( is-iso-is-equiv-hom-Semigroup)
      ( is-equiv-is-iso-hom-Semigroup)) ∘e
    ( equiv-right-swap-Σ)
```

### Two semigroups are equal if and only if they are isomorphic

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  is-contr-total-iso-Semigroup :
    is-contr (Σ (Semigroup l) (type-iso-Semigroup G))
  is-contr-total-iso-Semigroup =
    is-contr-equiv'
      ( Σ (Semigroup l) (equiv-Semigroup G))
      ( equiv-tot (equiv-iso-equiv-Semigroup G))
      ( is-contr-total-equiv-Semigroup G)

  id-iso-Semigroup : type-iso-Semigroup G G
  id-iso-Semigroup = id-iso-Large-Precat Semigroup-Large-Precat {X = G}

  iso-eq-Semigroup : (H : Semigroup l) → Id G H → type-iso-Semigroup G H
  iso-eq-Semigroup = iso-eq-Large-Precat Semigroup-Large-Precat G
```
