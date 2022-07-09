---
title: Equivalences between semigroups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.equivalences-semigroups where

open import foundation.contractible-types using (is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_≃_; map-equiv; id-equiv)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.functions using (id)
open import foundation.identity-types using (Id; refl)
open import foundation.propositions using (Π-Prop)
open import foundation.sets using (Id-Prop; is-prop-is-set)
open import foundation.structure-identity-principle using
  ( is-contr-total-Eq-structure)
open import foundation.subtype-identity-principle using
  ( is-contr-total-Eq-subtype)
open import foundation.subtypes using (eq-subtype)
open import foundation.univalence using (is-contr-total-equiv)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import group-theory.homomorphisms-semigroups using
  ( preserves-mul; preserves-mul-Semigroup; preserves-mul-semigroup-Prop)
open import group-theory.semigroups using
  ( Semigroup; type-Semigroup; mul-Semigroup; has-associative-mul;
    set-Semigroup; associative-mul-Semigroup; is-set-type-Semigroup)
```

## Idea

An equivalence between semigroups is an equivalence between their underlying types that preserves the binary operation.

## Definition

### Equivalences preserving binary operations

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  preserves-mul-equiv :
    (μA : A → A → A) (μB : B → B → B) → (A ≃ B) → UU (l1 ⊔ l2)
  preserves-mul-equiv μA μB e = preserves-mul μA μB (map-equiv e)
```

### Equivalences of semigroups

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  preserves-mul-equiv-Semigroup :
    (type-Semigroup G ≃ type-Semigroup H) → UU (l1 ⊔ l2)
  preserves-mul-equiv-Semigroup e =
    preserves-mul-equiv (mul-Semigroup G) (mul-Semigroup H) e

  equiv-Semigroup : UU (l1 ⊔ l2)
  equiv-Semigroup =
    Σ (type-Semigroup G ≃ type-Semigroup H) preserves-mul-equiv-Semigroup
```

## Properties

### The total space of all equivalences of semigroups with domain `G` is contractible

```agda
module _
  {l : Level} (G : Semigroup l)
  where
  
  center-total-preserves-mul-id-Semigroup :
    Σ ( has-associative-mul (type-Semigroup G))
      ( λ μ → preserves-mul-Semigroup G (pair (set-Semigroup G) μ) id)
  pr1 (pr1 (center-total-preserves-mul-id-Semigroup)) = mul-Semigroup G
  pr2 (pr1 (center-total-preserves-mul-id-Semigroup)) =
    associative-mul-Semigroup G
  pr2 (center-total-preserves-mul-id-Semigroup) x y = refl

  contraction-total-preserves-mul-id-Semigroup :
    ( t : Σ ( has-associative-mul (type-Semigroup G))
            ( λ μ →
              preserves-mul-Semigroup G (pair (set-Semigroup G) μ) id)) →
    Id center-total-preserves-mul-id-Semigroup t
  contraction-total-preserves-mul-id-Semigroup
    (pair (pair μ-G' assoc-G') μ-id) =
    eq-subtype
      ( λ μ →
        preserves-mul-semigroup-Prop G (pair (set-Semigroup G) μ) id)
      ( eq-subtype
        ( λ μ →
          Π-Prop
            ( type-Semigroup G)
            ( λ x →
              Π-Prop
                ( type-Semigroup G)
                ( λ y →
                  Π-Prop
                    ( type-Semigroup G)
                    ( λ z →
                      Id-Prop
                        ( set-Semigroup G)
                        ( μ (μ x y) z) (μ x (μ y z))))))
        ( eq-htpy (λ x → eq-htpy (λ y → μ-id x y))))

  is-contr-total-preserves-mul-id-Semigroup :
    is-contr
      ( Σ ( has-associative-mul (type-Semigroup G))
          ( λ μ → preserves-mul (mul-Semigroup G) (pr1 μ) id))
  pr1 is-contr-total-preserves-mul-id-Semigroup =
    center-total-preserves-mul-id-Semigroup
  pr2 is-contr-total-preserves-mul-id-Semigroup =
    contraction-total-preserves-mul-id-Semigroup

  is-contr-total-equiv-Semigroup :
    is-contr (Σ (Semigroup l) (equiv-Semigroup G))
  is-contr-total-equiv-Semigroup =
    is-contr-total-Eq-structure
      ( λ H μH → preserves-mul-equiv-Semigroup G (pair H μH))
      ( is-contr-total-Eq-subtype
        ( is-contr-total-equiv (type-Semigroup G))
        ( is-prop-is-set)
        ( type-Semigroup G)
        ( id-equiv)
        ( is-set-type-Semigroup G))
      ( pair (set-Semigroup G) id-equiv)
      ( is-contr-total-preserves-mul-id-Semigroup)
```
