---
title: Symmetric groups
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.symmetric-groups where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equality-dependent-pair-types using
  (eq-pair-Σ; pair-eq-Σ; comp-eq-pair-Σ; comp-pair-eq-Σ; issec-pair-eq-Σ; isretr-pair-eq-Σ)
open import foundation.equivalences using
  ( _≃_; _∘e_; associative-comp-equiv; id-equiv; left-unit-law-equiv; inv-equiv;
    right-unit-law-equiv; left-inverse-law-equiv; right-inverse-law-equiv;
    distributive-inv-comp-equiv; inv-inv-equiv; map-equiv; eq-htpy-equiv)
open import foundation.functions using (id)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.homotopies using (refl-htpy)
open import foundation.identity-types using
  (Id; refl; _∙_; ap; inv; ap-binary; tr)
open import foundation.propositional-truncations using
  ( type-trunc-Prop; is-prop-type-trunc-Prop; unit-trunc-Prop)
open import foundation.propositions using (eq-is-prop)
open import foundation.raising-universe-levels using (raise-Set; equiv-raise)
open import foundation.sets using
  ( UU-Set; type-Set; is-set; is-set-type-Set; aut-Set; is-prop-is-set;
    is-1-type-UU-Set)
open import foundation.truncated-types using (is-trunc-Id)
open import foundation.univalence using
  ( equiv-eq; eq-equiv; comp-eq-equiv; comp-equiv-eq; equiv-univalence)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import group-theory.automorphism-groups using (Automorphism-Group)
open import group-theory.concrete-groups using (abstract-group-Concrete-Group)
open import group-theory.groups using (is-group'; Group; semigroup-Group)
open import group-theory.homomorphisms-groups using (id-hom-Group; type-hom-Group; comp-hom-Group)
open import group-theory.homomorphisms-semigroups using (is-prop-preserves-mul-Semigroup)
open import group-theory.isomorphisms-groups using (type-iso-Group)
open import group-theory.monoids using (is-unital-Semigroup)
open import group-theory.semigroups using (has-associative-mul-Set; Semigroup)
```

## Definitions

```agda
set-symmetric-Group : {l : Level} (X : UU-Set l) → UU-Set l
set-symmetric-Group X = aut-Set X

type-symmetric-Group : {l : Level} (X : UU-Set l) → UU l
type-symmetric-Group X = type-Set (set-symmetric-Group X)

is-set-type-symmetric-Group :
  {l : Level} (X : UU-Set l) → is-set (type-symmetric-Group X)
is-set-type-symmetric-Group X = is-set-type-Set (set-symmetric-Group X)

has-associative-mul-aut-Set :
  {l : Level} (X : UU-Set l) → has-associative-mul-Set (aut-Set X)
pr1 (has-associative-mul-aut-Set X) f e = f ∘e e
pr2 (has-associative-mul-aut-Set X) e f g = associative-comp-equiv g f e

symmetric-Semigroup :
  {l : Level} (X : UU-Set l) → Semigroup l
pr1 (symmetric-Semigroup X) = set-symmetric-Group X
pr2 (symmetric-Semigroup X) = has-associative-mul-aut-Set X

is-unital-Semigroup-symmetric-Semigroup :
  {l : Level} (X : UU-Set l) → is-unital-Semigroup (symmetric-Semigroup X)
pr1 (is-unital-Semigroup-symmetric-Semigroup X) = id-equiv
pr1 (pr2 (is-unital-Semigroup-symmetric-Semigroup X)) = left-unit-law-equiv
pr2 (pr2 (is-unital-Semigroup-symmetric-Semigroup X)) = right-unit-law-equiv

is-group-symmetric-Semigroup' :
  {l : Level} (X : UU-Set l) →
  is-group' (symmetric-Semigroup X) (is-unital-Semigroup-symmetric-Semigroup X)
pr1 (is-group-symmetric-Semigroup' X) = inv-equiv
pr1 (pr2 (is-group-symmetric-Semigroup' X)) = left-inverse-law-equiv
pr2 (pr2 (is-group-symmetric-Semigroup' X)) = right-inverse-law-equiv

symmetric-Group :
  {l : Level} → UU-Set l → Group l
pr1 (symmetric-Group X) = symmetric-Semigroup X
pr1 (pr2 (symmetric-Group X)) = is-unital-Semigroup-symmetric-Semigroup X
pr2 (pr2 (symmetric-Group X)) = is-group-symmetric-Semigroup' X
```

## Properties

### If two sets are equivalent, then their symmetric groups are isomorphic

```agda
module _
  {l1 l2 : Level} (X : UU-Set l1) (Y : UU-Set l2) (e : type-Set X ≃ type-Set Y)
  where

  hom-symmetric-group-equiv-Set : 
    type-hom-Group (symmetric-Group X) (symmetric-Group Y)
  pr1 hom-symmetric-group-equiv-Set f = e ∘e (f ∘e inv-equiv e)
  pr2 hom-symmetric-group-equiv-Set f g =
    ( eq-htpy-equiv refl-htpy) ∙
      ( ( ap
        ( λ h → e ∘e (( f ∘e (h ∘e g)) ∘e inv-equiv e))
        ( inv (left-inverse-law-equiv e))) ∙
        ( eq-htpy-equiv refl-htpy))

  hom-inv-symmetric-group-equiv-Set : 
    type-hom-Group (symmetric-Group Y) (symmetric-Group X)
  pr1 hom-inv-symmetric-group-equiv-Set f = inv-equiv e ∘e (f ∘e e)
  pr2 hom-inv-symmetric-group-equiv-Set f g =
    ( eq-htpy-equiv refl-htpy) ∙
      ( ( ap
        ( λ h → inv-equiv e ∘e (( f ∘e (h ∘e g)) ∘e e))
        ( inv (right-inverse-law-equiv e))) ∙
        ( eq-htpy-equiv refl-htpy))

  is-sec-hom-inv-symmetric-group-equiv-Set :
    Id
      ( comp-hom-Group
        ( symmetric-Group Y)
        ( symmetric-Group X)
        ( symmetric-Group Y)
        ( hom-symmetric-group-equiv-Set)
        ( hom-inv-symmetric-group-equiv-Set))
      ( id-hom-Group (symmetric-Group Y))
  is-sec-hom-inv-symmetric-group-equiv-Set =
    eq-pair-Σ
      ( eq-htpy
        ( λ f →
          ( eq-htpy-equiv refl-htpy) ∙
            ( ( ap (λ h → h ∘e (f ∘e h)) (right-inverse-law-equiv e)) ∙
              ( eq-htpy-equiv refl-htpy))))
      ( eq-is-prop
        ( is-prop-preserves-mul-Semigroup
          ( semigroup-Group (symmetric-Group Y))
          ( semigroup-Group (symmetric-Group Y))
          ( id)))

  is-retr-hom-inv-symmetric-group-equiv-Set :
    Id
      ( comp-hom-Group
        ( symmetric-Group X)
        ( symmetric-Group Y)
        ( symmetric-Group X)
        ( hom-inv-symmetric-group-equiv-Set)
        ( hom-symmetric-group-equiv-Set))
      ( id-hom-Group (symmetric-Group X))
  is-retr-hom-inv-symmetric-group-equiv-Set =
    eq-pair-Σ
      ( eq-htpy
        ( λ f →
          ( eq-htpy-equiv refl-htpy) ∙
            ( ( ap (λ h → h ∘e (f ∘e h)) (left-inverse-law-equiv e)) ∙
              ( eq-htpy-equiv refl-htpy))))
      ( eq-is-prop
        ( is-prop-preserves-mul-Semigroup
          ( semigroup-Group (symmetric-Group X))
          ( semigroup-Group (symmetric-Group X))
          ( id)))

  iso-symmetric-group-equiv-Set :
    type-iso-Group (symmetric-Group X) (symmetric-Group Y)
  pr1 iso-symmetric-group-equiv-Set = hom-symmetric-group-equiv-Set
  pr1 (pr2 iso-symmetric-group-equiv-Set) = hom-inv-symmetric-group-equiv-Set
  pr1 (pr2 (pr2 iso-symmetric-group-equiv-Set)) = is-sec-hom-inv-symmetric-group-equiv-Set
  pr2 (pr2 (pr2 iso-symmetric-group-equiv-Set)) = is-retr-hom-inv-symmetric-group-equiv-Set

```

### The symmetric group and the abstract automorphism group of a set are isomorphic

```agda
module _
  {l1 l2 : Level} (X : UU-Set l1)
  where
  
  hom-symmetric-group-abstract-automorphism-group-Set :
    type-hom-Group
      ( symmetric-Group X)
      ( abstract-group-Concrete-Group
        ( Automorphism-Group (UU-Set (l1 ⊔ l2)) (raise-Set l2 X) is-1-type-UU-Set))
  pr1 hom-symmetric-group-abstract-automorphism-group-Set x =
    eq-pair-Σ
      ( eq-pair-Σ
        ( eq-equiv
          ( type-Set (raise-Set l2 X))
          ( type-Set (raise-Set l2 X))
          ( equiv-raise l2 (type-Set X) ∘e
            ( (inv-equiv x) ∘e inv-equiv (equiv-raise l2 (type-Set X)))))
        ( eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X)))))
      ( eq-is-prop is-prop-type-trunc-Prop)
  pr2 hom-symmetric-group-abstract-automorphism-group-Set x y =
    ( ap
      ( λ P → eq-pair-Σ P (eq-is-prop is-prop-type-trunc-Prop))
      ( ap
        ( λ Q → eq-pair-Σ Q (eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X)))))
        ( ( ap
          ( eq-equiv (type-Set (raise-Set l2 X)) (type-Set (raise-Set l2 X)))
          ( ( ap
            ( λ e → equiv-raise l2 (type-Set X) ∘e (e ∘e inv-equiv (equiv-raise l2 (type-Set X))))
            ( distributive-inv-comp-equiv y x ∙
              (eq-htpy-equiv refl-htpy ∙
                ( ap
                  ( λ e → inv-equiv y ∘e (e ∘e inv-equiv x))
                  ( inv (left-inverse-law-equiv (equiv-raise l2 (type-Set X)))))))) ∙
            ( eq-htpy-equiv refl-htpy))) ∙
          ( inv
            ( comp-eq-equiv
              ( type-Set (raise-Set l2 X))
              ( type-Set (raise-Set l2 X))
              ( type-Set (raise-Set l2 X))
              ( equiv-raise l2 (type-Set X) ∘e (inv-equiv x ∘e inv-equiv (equiv-raise l2 (type-Set X))))
              ( equiv-raise l2 (type-Set X) ∘e (inv-equiv y ∘e inv-equiv (equiv-raise l2 (type-Set X))))))) ∙
        ( ( ap
          ( λ w →
            eq-pair-Σ
              ( ( eq-equiv
                ( type-Set (raise-Set l2 X))
                ( type-Set (raise-Set l2 X))
                ( equiv-raise l2 (type-Set X) ∘e (inv-equiv x ∘e inv-equiv (equiv-raise l2 (type-Set X))))) ∙
                ( eq-equiv
                  ( type-Set (raise-Set l2 X))
                  ( type-Set (raise-Set l2 X))
                  ( equiv-raise l2 (type-Set X) ∘e
                    ( inv-equiv y ∘e inv-equiv (equiv-raise l2 (type-Set X))))))
              ( w))
          ( eq-is-prop (is-trunc-Id (is-prop-is-set (type-Set (raise-Set l2 X)) _ _)))) ∙
          ( inv
            ( comp-eq-pair-Σ
              ( pr2 (raise-Set l2 X))
              ( pr2 (raise-Set l2 X))
              ( pr2 (raise-Set l2 X))
              ( eq-equiv
                ( type-Set (raise-Set l2 X))
                ( type-Set (raise-Set l2 X))
                ( equiv-raise l2 (type-Set X) ∘e
                  ( inv-equiv x ∘e inv-equiv (equiv-raise l2 (type-Set X)))))
              ( eq-equiv
                ( type-Set (raise-Set l2 X))
                ( type-Set (raise-Set l2 X))
                ( equiv-raise l2 (type-Set X) ∘e
                  ( inv-equiv y ∘e inv-equiv (equiv-raise l2 (type-Set X)))))
              ( eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X))))
              ( eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X))))))))) ∙
      ( ap
        ( λ w →
          eq-pair-Σ
            ( ( eq-pair-Σ
              ( eq-equiv
                ( type-Set (raise-Set l2 X))
                ( type-Set (raise-Set l2 X))
                ( equiv-raise l2 (type-Set X) ∘e
                  ( inv-equiv x ∘e inv-equiv (equiv-raise l2 (type-Set X)))))
              ( eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X))))) ∙
               eq-pair-Σ
                ( eq-equiv
                  (type-Set (raise-Set l2 X))
                  (type-Set (raise-Set l2 X))
                  ( equiv-raise l2 (type-Set X) ∘e
                    (inv-equiv y ∘e inv-equiv (equiv-raise l2 (type-Set X)))))
                ( eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X)))))
            ( w))
        ( eq-is-prop (is-trunc-Id (is-prop-type-trunc-Prop _ (unit-trunc-Prop refl)))) ∙
         inv
          ( comp-eq-pair-Σ
            ( unit-trunc-Prop refl)
            ( unit-trunc-Prop refl)
            ( unit-trunc-Prop refl)
            ( eq-pair-Σ
              ( eq-equiv
                ( type-Set (raise-Set l2 X))
                ( type-Set (raise-Set l2 X))
                ( equiv-raise l2 (type-Set X) ∘e
                  (inv-equiv x ∘e inv-equiv (equiv-raise l2 (type-Set X)))))
              ( eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X)))))
            ( eq-pair-Σ
              ( eq-equiv
                ( type-Set (raise-Set l2 X))
                ( type-Set (raise-Set l2 X))
                ( equiv-raise l2 (type-Set X) ∘e
                  (inv-equiv y ∘e inv-equiv (equiv-raise l2 (type-Set X)))))
              ( eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X)))))
            ( eq-is-prop is-prop-type-trunc-Prop)
            ( eq-is-prop is-prop-type-trunc-Prop))) 

  hom-inv-symmetric-group-abstract-automorphism-group-Set :
    type-hom-Group
      ( abstract-group-Concrete-Group
        ( Automorphism-Group (UU-Set (l1 ⊔ l2)) (raise-Set l2 X) is-1-type-UU-Set))
      ( symmetric-Group X)
  pr1 hom-inv-symmetric-group-abstract-automorphism-group-Set x =
    inv-equiv
      ( inv-equiv (equiv-raise l2 (type-Set X)) ∘e
        ( equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x)))) ∘e equiv-raise l2 (type-Set X)))
  pr2 hom-inv-symmetric-group-abstract-automorphism-group-Set x y = 
    ( ap
      ( inv-equiv)
      { y =
        ( inv-equiv (equiv-raise l2 (type-Set X)) ∘e
          ( equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ y)))) ∘e equiv-raise l2 (type-Set X))) ∘e
          ( inv-equiv (equiv-raise l2 (type-Set X)) ∘e
            ( equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x)))) ∘e equiv-raise l2 (type-Set X)))}
      ( ( ap
        ( λ e → inv-equiv (equiv-raise l2 (type-Set X)) ∘e (e ∘e equiv-raise l2 (type-Set X)))
        ( ( ap
          ( equiv-eq)
          ( ( ap (λ p → pr1 (pair-eq-Σ p)) (inv (comp-pair-eq-Σ x y))) ∙
            ( inv (comp-pair-eq-Σ (pr1 (pair-eq-Σ x)) (pr1 (pair-eq-Σ y)))))) ∙
          ( ( inv
            ( comp-equiv-eq
              ( pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x))))
              ( pr1 (pair-eq-Σ (pr1 (pair-eq-Σ y)))))) ∙
            ( ( eq-htpy-equiv refl-htpy) ∙
              ( ap
                ( λ e →
                  equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ y)))) ∘e
                    (e ∘e equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x))))))
                ( inv (right-inverse-law-equiv (equiv-raise l2 (type-Set X))))))))) ∙
        ( eq-htpy-equiv refl-htpy))) ∙
      ( distributive-inv-comp-equiv
        ( inv-equiv (equiv-raise l2 (type-Set X)) ∘e
          ( equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x)))) ∘e equiv-raise l2 (type-Set X)))
        ( inv-equiv (equiv-raise l2 (type-Set X)) ∘e
          ( equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ y)))) ∘e equiv-raise l2 (type-Set X))))

  is-sec-hom-inv-symmetric-group-abstract-automorphism-group-Set :
    Id
      ( comp-hom-Group
        ( abstract-group-Concrete-Group
          ( Automorphism-Group (UU-Set (l1 ⊔ l2)) (raise-Set l2 X) is-1-type-UU-Set))
        ( symmetric-Group X)
        ( abstract-group-Concrete-Group
          ( Automorphism-Group (UU-Set (l1 ⊔ l2)) (raise-Set l2 X) is-1-type-UU-Set))
        ( hom-symmetric-group-abstract-automorphism-group-Set)
        ( hom-inv-symmetric-group-abstract-automorphism-group-Set))
      ( id-hom-Group
        ( abstract-group-Concrete-Group
          ( Automorphism-Group (UU-Set (l1 ⊔ l2)) (raise-Set l2 X) is-1-type-UU-Set)))
  is-sec-hom-inv-symmetric-group-abstract-automorphism-group-Set = 
    eq-pair-Σ
      ( eq-htpy
        ( λ x →
          ( ap
            ( λ w →
              eq-pair-Σ
                ( w)
                ( eq-is-prop is-prop-type-trunc-Prop))
            ( ( ap
              (λ w →
                eq-pair-Σ w (eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X)))))
              ( ( ap
                ( eq-equiv (type-Set (raise-Set l2 X)) (type-Set (raise-Set l2 X)))
                ( ( ap
                  ( λ e → equiv-raise l2 (type-Set X) ∘e (e ∘e inv-equiv (equiv-raise l2 (type-Set X))))
                  ( inv-inv-equiv
                    ( inv-equiv (equiv-raise l2 (type-Set X)) ∘e
                      (equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x)))) ∘e equiv-raise l2 (type-Set X))))) ∙
                  ( ( eq-htpy-equiv refl-htpy) ∙
                    ( ( ap
                      ( λ e →
                        e ∘e
                          ( equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x)))) ∘e
                            ( equiv-raise l2 (type-Set X) ∘e
                              inv-equiv (equiv-raise l2 (type-Set X)))))
                      ( right-inverse-law-equiv (equiv-raise l2 (type-Set X)))) ∙
                      ( ( ap
                        ( λ e → id-equiv ∘e (equiv-eq (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x)))) ∘e e))
                        ( right-inverse-law-equiv (equiv-raise l2 (type-Set X)))) ∙
                        ( eq-htpy-equiv refl-htpy)))))) ∙
                ( ap
                  ( λ e → map-equiv e (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x)))))
                  ( left-inverse-law-equiv equiv-univalence)))) ∙
              ( ( ap
                ( eq-pair-Σ (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ x)))))
                { y = pr2 (pair-eq-Σ (pr1 (pair-eq-Σ x)))}
                ( eq-is-prop (is-trunc-Id (is-prop-is-set (type-Set (raise-Set l2 X)) _ _)))) ∙
                ( issec-pair-eq-Σ (raise-Set l2 X) (raise-Set l2 X) (pr1 (pair-eq-Σ x))))) ∙
            ( ( ap
              ( eq-pair-Σ (pr1 (pair-eq-Σ x)))
              { y = pr2 (pair-eq-Σ x)}
              ( eq-is-prop (is-trunc-Id (is-prop-type-trunc-Prop _ _)))) ∙
              ( issec-pair-eq-Σ
                ( pair (raise-Set l2 X) (unit-trunc-Prop refl))
                ( pair (raise-Set l2 X) (unit-trunc-Prop refl))
                ( x))))))
      ( eq-is-prop
        ( is-prop-preserves-mul-Semigroup
          ( semigroup-Group
            ( abstract-group-Concrete-Group
              ( Automorphism-Group (UU-Set (l1 ⊔ l2)) (raise-Set l2 X) is-1-type-UU-Set)))
          ( semigroup-Group
            ( abstract-group-Concrete-Group
              ( Automorphism-Group (UU-Set (l1 ⊔ l2)) (raise-Set l2 X) is-1-type-UU-Set)))
          ( id)))

  is-retr-hom-inv-symmetric-group-abstract-automorphism-group-Set :
    Id
      ( comp-hom-Group
        ( symmetric-Group X)
        ( abstract-group-Concrete-Group
          ( Automorphism-Group (UU-Set (l1 ⊔ l2)) (raise-Set l2 X) is-1-type-UU-Set))
        ( symmetric-Group X)
        ( hom-inv-symmetric-group-abstract-automorphism-group-Set)
        ( hom-symmetric-group-abstract-automorphism-group-Set))
      ( id-hom-Group (symmetric-Group X))
  is-retr-hom-inv-symmetric-group-abstract-automorphism-group-Set = 
    eq-pair-Σ
      ( eq-htpy
        ( λ x →
          ( ap
            ( inv-equiv)
            { y = inv-equiv x}
            ( ( ap
              ( λ e →
                ( inv-equiv (equiv-raise l2 (type-Set X))) ∘e
                  ( e ∘e equiv-raise l2 (type-Set X)))
              ( ( ap
                ( equiv-eq)
                ( ap
                  ( λ w → pr1 (pair-eq-Σ w))
                  ( ap pr1
                    ( isretr-pair-eq-Σ
                      ( pair (raise-Set l2 X) (unit-trunc-Prop refl))
                      ( pair (raise-Set l2 X) (unit-trunc-Prop refl))
                      ( pair
                        ( eq-pair-Σ
                          ( eq-equiv
                            ( type-Set (raise-Set l2 X))
                            ( type-Set (raise-Set l2 X))
                            ( equiv-raise l2 (type-Set X) ∘e
                              ( inv-equiv x ∘e inv-equiv (equiv-raise l2 (type-Set X)))))
                          ( eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X)))))
                        ( eq-is-prop is-prop-type-trunc-Prop)))) ∙
                    ( ap pr1
                      ( isretr-pair-eq-Σ (raise-Set l2 X) (raise-Set l2 X)
                        ( pair
                          ( eq-equiv
                            ( type-Set (raise-Set l2 X))
                            ( type-Set (raise-Set l2 X))
                            ( equiv-raise l2 (type-Set X) ∘e
                              ( inv-equiv x ∘e inv-equiv (equiv-raise l2 (type-Set X)))))
                          ( eq-is-prop (is-prop-is-set (type-Set (raise-Set l2 X))))))))) ∙
                ( ap
                  ( λ e →
                    map-equiv
                      ( e)
                      ( equiv-raise l2 (type-Set X) ∘e
                        ( inv-equiv x ∘e inv-equiv (equiv-raise l2 (type-Set X)))))
                  ( right-inverse-law-equiv equiv-univalence)))) ∙
              ( eq-htpy-equiv refl-htpy ∙
                ( ( ap
                  ( λ e →
                    e ∘e
                      (inv-equiv x ∘e
                        (inv-equiv (equiv-raise l2 (type-Set X)) ∘e
                          equiv-raise l2 (type-Set X))))
                   ( left-inverse-law-equiv (equiv-raise l2 (type-Set X)))) ∙
                   ( ( ap
                     ( λ e → id-equiv ∘e (inv-equiv x ∘e e))
                     ( left-inverse-law-equiv (equiv-raise l2 (type-Set X)))) ∙
                     ( eq-htpy-equiv refl-htpy)))))) ∙
            ( inv-inv-equiv x)))
      ( eq-is-prop
        ( is-prop-preserves-mul-Semigroup
          ( semigroup-Group (symmetric-Group X))
          ( semigroup-Group (symmetric-Group X))
          ( id)))

  iso-symmetric-group-abstract-automorphism-group-Set :
    type-iso-Group
      ( symmetric-Group X)
      ( abstract-group-Concrete-Group
        ( Automorphism-Group (UU-Set (l1 ⊔ l2)) (raise-Set l2 X) is-1-type-UU-Set))
  pr1 iso-symmetric-group-abstract-automorphism-group-Set =
    hom-symmetric-group-abstract-automorphism-group-Set
  pr1 (pr2 iso-symmetric-group-abstract-automorphism-group-Set) =
    hom-inv-symmetric-group-abstract-automorphism-group-Set
  pr1 (pr2 (pr2 iso-symmetric-group-abstract-automorphism-group-Set)) =
    is-sec-hom-inv-symmetric-group-abstract-automorphism-group-Set
  pr2 (pr2 (pr2 iso-symmetric-group-abstract-automorphism-group-Set)) =
    is-retr-hom-inv-symmetric-group-abstract-automorphism-group-Set
```
