# Composition of species of types

```agda
module species.large-composition-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.discrete-relaxed-sigma-decompositions
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.relaxed-sigma-decompositions
open import foundation.trivial-relaxed-sigma-decompositions
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-function-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-unit-type
open import foundation.type-theoretic-principle-of-choice
open import foundation.unit-type
open import foundation.univalence
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import species.species-of-types
```

</details>

## Idea

A specie of types `S : UU l1 → UU l2` can be thought of as the analytic
endofunctor

```md
  X ↦ Σ (A : UU l1) (S A) × (A → X)
```

Using the formula for composition of analytic endofunctors, we obtain a way to
compose species.

## Definition

### Analytic composition of species

```agda
analytic-comp-species-types :
  {l1 l2 l3 : Level} → species-types l1 l2 → species-types l1 l3 →
  species-types l1 (lsuc l1 ⊔ l2 ⊔ l3)
analytic-comp-species-types {l1} {l2} {l3} S T X =
  Σ ( Relaxed-Σ-Decomposition l1 l1 X)
    ( λ D →
      ( S (indexing-type-Relaxed-Σ-Decomposition D) ×
      ( (y : indexing-type-Relaxed-Σ-Decomposition D) →
      T (cotype-Relaxed-Σ-Decomposition D y ))))
```

### The analytic unit for composition of species

```agda
analytic-unit-species-types : {l1 : Level} → species-types l1 l1
analytic-unit-species-types X = is-contr X
```

## Properties

### Unit laws for analytic composition of species

```agda
left-unit-law-comp-species-types :
  {l1 l2 : Level}
  (F : species-types l1 l2) → (A : UU l1) →
  analytic-comp-species-types analytic-unit-species-types F A ≃ F A
left-unit-law-comp-species-types {l1} F A =
  ( ( left-unit-law-Σ-is-contr
      ( is-contr-type-trivial-Relaxed-Σ-Decomposition)
      ( trivial-Relaxed-Σ-Decomposition l1 A ,
        is-trivial-trivial-inhabited-Relaxed-Σ-Decomposition {l1} {l1} {A})) ∘e
    ( ( inv-assoc-Σ
        ( Relaxed-Σ-Decomposition l1 l1 A)
        ( λ D → is-contr (indexing-type-Relaxed-Σ-Decomposition D))
        ( λ C → F (cotype-Relaxed-Σ-Decomposition (pr1 C) (center (pr2 C))))) ∘e
      ( ( equiv-Σ
          ( _)
          ( id-equiv)
          ( λ D →
            equiv-Σ
              ( λ z → F (cotype-Relaxed-Σ-Decomposition D (center z)))
              ( id-equiv)
              ( λ C →
                ( left-unit-law-Π-is-contr C (center C))))))))

right-unit-law-comp-species-types :
  {l1 l2 : Level}
  (F : species-types l1 l2) → (A : UU l1)  →
  analytic-comp-species-types F analytic-unit-species-types A ≃ F A
right-unit-law-comp-species-types {l1} F A =
  ( ( left-unit-law-Σ-is-contr
      ( is-contr-type-discrete-Relaxed-Σ-Decomposition)
      ( ( discrete-Relaxed-Σ-Decomposition l1 A) ,
        is-discrete-discrete-Relaxed-Σ-Decomposition) ) ∘e
    ( ( inv-assoc-Σ
        ( Relaxed-Σ-Decomposition l1 l1 A)
        ( λ D →
            ( y : indexing-type-Relaxed-Σ-Decomposition D) →
              is-contr (cotype-Relaxed-Σ-Decomposition D y))
        ( λ D → F (indexing-type-Relaxed-Σ-Decomposition (pr1 D)))) ∘e
      ( ( equiv-Σ
          ( λ D →
            ( ( y : indexing-type-Relaxed-Σ-Decomposition D) →
              analytic-unit-species-types
                ( cotype-Relaxed-Σ-Decomposition D y)) ×
              F ( indexing-type-Relaxed-Σ-Decomposition D))
         ( id-equiv)
         ( λ _ → commutative-prod)))))
```

### Associativity of composition of species

```agda
module _
  {l1 l2 l3 l4 : Level}
  (S : species-types l1 l2) (T : species-types l1 l3)
  (U : species-types l1 l4)
  where

  equiv-assoc-comp-species-types :
    (A : UU l1) →
    ( analytic-comp-species-types S (analytic-comp-species-types T  U) A) ≃
    ( analytic-comp-species-types (analytic-comp-species-types S T) U A)
  equiv-assoc-comp-species-types A =
    ( ( equiv-Σ
        ( _)
        ( id-equiv)
        ( λ D1 →
          ( ( inv-equiv right-distributive-prod-Σ)  ∘e
          ( ( equiv-Σ
              ( _)
              ( id-equiv)
              ( λ D2 →
                ( inv-assoc-Σ
                  ( S (indexing-type-Relaxed-Σ-Decomposition D2))
                  ( λ _ →
                    ( x : indexing-type-Relaxed-Σ-Decomposition D2) →
                    T ( cotype-Relaxed-Σ-Decomposition D2 x))
                  _))) ∘e
          ( ( equiv-Σ
            ( _)
            ( id-equiv)
            ( λ D2 →
              ( equiv-prod
                ( id-equiv)
                ( ( equiv-prod
                    ( id-equiv)
                    ( ( inv-equiv
                        ( equiv-precomp-Π
                          ( inv-equiv
                            ( matching-correspondence-Relaxed-Σ-Decomposition D2) )
                        ( λ x → U ( cotype-Relaxed-Σ-Decomposition D1 x) ))) ∘e
                      ( inv-equiv equiv-ev-pair))) ∘e
                  ( distributive-Π-Σ)))))))))) ∘e
      ( ( assoc-Σ
          ( Relaxed-Σ-Decomposition l1 l1 A)
          ( λ D → Relaxed-Σ-Decomposition l1 l1
            ( indexing-type-Relaxed-Σ-Decomposition D))
          ( _)) ∘e
        ( ( inv-equiv
            ( equiv-Σ-equiv-base
              ( _ )
              ( equiv-displayed-fibered-Relaxed-Σ-Decomposition))) ∘e
          ( ( inv-assoc-Σ
              ( Relaxed-Σ-Decomposition l1 l1 A)
              ( λ D →
                ( x : indexing-type-Relaxed-Σ-Decomposition D) →
                  Relaxed-Σ-Decomposition l1 l1
                    ( cotype-Relaxed-Σ-Decomposition D x))
              ( _)) ∘e
            ( ( equiv-Σ
                ( _)
                ( id-equiv)
                ( λ D → left-distributive-prod-Σ)) ∘e
              ( ( equiv-Σ
                  ( _)
                  ( id-equiv)
                  ( λ D → equiv-prod id-equiv distributive-Π-Σ))))))))

  htpy-assoc-comp-species-types :
    ( analytic-comp-species-types S (analytic-comp-species-types T  U)) ~
    ( analytic-comp-species-types (analytic-comp-species-types S T) U)
  htpy-assoc-comp-species-types A =
    eq-equiv
      ( analytic-comp-species-types S (analytic-comp-species-types T U)
        A)
      ( analytic-comp-species-types (analytic-comp-species-types S T) U
        A)
      ( equiv-assoc-comp-species-types A)

  assoc-comp-species-types :
    ( analytic-comp-species-types S (analytic-comp-species-types T  U)) ＝
    ( analytic-comp-species-types (analytic-comp-species-types S T) U)
  assoc-comp-species-types = eq-htpy htpy-assoc-comp-species-types
```
