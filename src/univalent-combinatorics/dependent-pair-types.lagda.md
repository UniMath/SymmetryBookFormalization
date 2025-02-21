# Dependent pair types of finite types

```agda
module univalent-combinatorics.dependent-pair-types where

open import foundation.dependent-pair-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.complements
open import foundation.contractible-types
open import foundation.decidable-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import logic.propositionally-decidable-types

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-dependent-pair-types
open import univalent-combinatorics.decidable-propositions
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-choice
open import univalent-combinatorics.finite-types
```

</details>

## Idea

In this file we study finiteness in relation to dependent pair types.

## Properties

### A dependent sum of finite types indexed by a finite type is finite

```agda
abstract
  is-finite-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-finite A → ((a : A) → is-finite (B a)) → is-finite (Σ A B)
  is-finite-Σ {A = A} {B} H K =
    apply-universal-property-trunc-Prop H
      ( is-finite-Prop (Σ A B))
      ( λ (e : count A) →
        apply-universal-property-trunc-Prop
          ( finite-choice H K)
          ( is-finite-Prop (Σ A B))
          ( is-finite-count ∘ (count-Σ e)))

Σ-Finite-Type :
  {l1 l2 : Level}
  (A : Finite-Type l1) (B : type-Finite-Type A → Finite-Type l2) →
  Finite-Type (l1 ⊔ l2)
pr1 (Σ-Finite-Type A B) = Σ (type-Finite-Type A) (λ a → type-Finite-Type (B a))
pr2 (Σ-Finite-Type A B) =
  is-finite-Σ
    ( is-finite-type-Finite-Type A)
    ( λ a → is-finite-type-Finite-Type (B a))
```

### If `A` and `Σ A B` are finite, then eacy `B a` is finite

```agda
abstract
  is-finite-fiber-is-finite-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-finite A → is-finite (Σ A B) → (a : A) → is-finite (B a)
  is-finite-fiber-is-finite-Σ {l1} {l2} {A} {B} f g a =
    apply-universal-property-trunc-Prop f
      ( is-finite-Prop (B a))
      ( λ e → map-trunc-Prop (λ h → count-fiber-count-Σ-count-base e h a) g)
```

### If `B` is a family of finite types over `A` equipped with a (mere) section and `Σ A B` is finite, then `A` is finite

```agda
abstract
  is-finite-base-is-finite-Σ-section :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (a : A) → B a) →
    is-finite (Σ A B) → ((a : A) → is-finite (B a)) → is-finite A
  is-finite-base-is-finite-Σ-section {l1} {l2} {A} {B} b f g =
    apply-universal-property-trunc-Prop f
      ( is-finite-Prop A)
      ( λ e →
        is-finite-count
          ( count-equiv
            ( ( equiv-total-fiber (map-section-family b)) ∘e
              ( equiv-tot
                ( λ t →
                  ( equiv-tot
                    ( λ x → equiv-eq-pair-Σ (map-section-family b x) t)) ∘e
                  ( ( associative-Σ A
                      ( λ (x : A) → Id x (pr1 t))
                      ( λ s → Id (tr B (pr2 s) (b (pr1 s))) (pr2 t))) ∘e
                    ( inv-left-unit-law-Σ-is-contr
                      ( is-torsorial-Id' (pr1 t))
                      ( pair (pr1 t) refl))))))
            ( count-Σ e
              ( λ t →
                count-eq
                  ( has-decidable-equality-is-finite (g (pr1 t)))
                  ( b (pr1 t))
                  ( pr2 t)))))

abstract
  is-finite-base-is-finite-Σ-mere-section :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    type-trunc-Prop ((a : A) → B a) →
    is-finite (Σ A B) → ((a : A) → is-finite (B a)) → is-finite A
  is-finite-base-is-finite-Σ-mere-section {l1} {l2} {A} {B} H f g =
    apply-universal-property-trunc-Prop H
      ( is-finite-Prop A)
      ( λ b → is-finite-base-is-finite-Σ-section b f g)
```

### If `B` is a family of finite inhabited types over a set `A` and `Σ A B` is finite, then `A` is finite

```agda
abstract
  is-finite-base-is-finite-Σ-merely-inhabited :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → (b : (a : A) → type-trunc-Prop (B a)) →
    is-finite (Σ A B) → ((a : A) → is-finite (B a)) → is-finite A
  is-finite-base-is-finite-Σ-merely-inhabited {l1} {l2} {A} {B} K b f g =
    is-finite-base-is-finite-Σ-mere-section
      ( choice-is-finite-Σ-is-finite-fiber K f g b)
      ( f)
      ( g)
```

### If `B` is a family of finite types over `A` with finite complement, and if `Σ A B` is finite, then `A` is finite

```agda
abstract
  is-finite-base-is-finite-complement :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-set A →
    is-finite (Σ A B) → (g : (a : A) → is-finite (B a)) →
    is-finite (complement B) → is-finite A
  is-finite-base-is-finite-complement {l1} {l2} {A} {B} K f g h =
    is-finite-equiv
      ( ( right-unit-law-Σ-is-contr
          ( λ x →
            is-proof-irrelevant-is-prop
              ( is-property-is-inhabited-or-empty (B x))
              ( is-inhabited-or-empty-is-finite (g x)))) ∘e
        ( inv-equiv
          ( left-distributive-Σ-coproduct A
            ( λ x → type-trunc-Prop (B x))
            ( λ x → is-empty (B x)))))
      ( is-finite-coproduct
        ( is-finite-base-is-finite-Σ-merely-inhabited
          ( is-set-type-subtype (λ x → trunc-Prop _) K)
          ( λ t → pr2 t)
          ( is-finite-equiv
            ( equiv-right-swap-Σ)
            ( is-finite-Σ
              ( f)
              ( λ x → is-finite-type-trunc-Prop (g (pr1 x)))))
          ( λ x → g (pr1 x)))
        ( h))
```
