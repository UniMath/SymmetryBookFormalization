# Dirichlet products of species of subuniverse

```agda
module species.dirichlet-product-species-of-subuniverse where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.product-decompositions
open import foundation.subuniverses
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universe-levels

open import species.species-of-types-in-subuniverse
```

</details>

## Idea

The Dirichlet product of two species of subuniverse `S` and `T` from `P` to `Q`
on `X` is defined as

```md
  Σ (k : P) (Σ (k' : P) (Σ (e : k × k' ≃ X) S(k) × T(k')))
```

If `Q` is stable by product and dependent pair type over `P` type, then the
dirichlet product is also a species of subuniverse from `P` to `Q`

## Definition

```agda
module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l1) (Q : global-subuniverse id )
  where

  private
    Ql2 = subuniverse-global-subuniverse Q l2
    Ql3 = subuniverse-global-subuniverse Q l3
    Ql1+⊔l2⊔l3 = subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3)

  dirichlet-product-species-subuniverse' :
    (S : species-subuniverse P Ql2) (T : species-subuniverse P Ql3)
    (X : type-subuniverse P) → UU (lsuc l1 ⊔ l2 ⊔ l3)
  dirichlet-product-species-subuniverse' S T X =
    Σ ( binary-product-Decomposition P X)
      ( λ d →
        inclusion-subuniverse Ql2
          ( S (left-summand-binary-product-Decomposition P X d)) ×
        inclusion-subuniverse Ql3
          ( T (right-summand-binary-product-Decomposition P X d)))

module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l1) (Q : global-subuniverse id )
  ( C1 :
    ( (l4 l5 : Level)
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l4))
    (T : species-subuniverse P (subuniverse-global-subuniverse Q l5))
    (X : type-subuniverse P) →
      is-in-subuniverse
        ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l4 ⊔ l5))
        ( dirichlet-product-species-subuniverse' P Q S T X)))
  where

  private
    Ql2 = subuniverse-global-subuniverse Q l2
    Ql3 = subuniverse-global-subuniverse Q l3
    Ql1+⊔l2⊔l3 = subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3)

  dirichlet-product-species-subuniverse :
    species-subuniverse P Ql2 → species-subuniverse P Ql3 →
    species-subuniverse P Ql1+⊔l2⊔l3
  pr1 (dirichlet-product-species-subuniverse S T X) =
    dirichlet-product-species-subuniverse' P Q S T X
  pr2 (dirichlet-product-species-subuniverse S T X) = C1 l2 l3 S T X

module _
  {l1 l2 l3 l4 : Level} (P : subuniverse l1 l1) (Q : global-subuniverse id)
  ( C1 :
      ( (l5 l6 : Level)
        (S : species-subuniverse P (subuniverse-global-subuniverse Q l5))
        (T : species-subuniverse P (subuniverse-global-subuniverse Q l6))
        (X : type-subuniverse P) →
        is-in-subuniverse
          ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l5 ⊔ l6) )
          ( dirichlet-product-species-subuniverse' P Q S T X)))
  ( C2 :
    (A B : type-subuniverse P) →
    is-in-subuniverse P (inclusion-subuniverse P A × inclusion-subuniverse P B))
  where

  private
    Ql2 = subuniverse-global-subuniverse Q l2
    Ql3 = subuniverse-global-subuniverse Q l3
    Ql4 = subuniverse-global-subuniverse Q l4

  module _
    (S : species-subuniverse P Ql2)
    (T : species-subuniverse P Ql3)
    (U : species-subuniverse P Ql4)
    (X : type-subuniverse P)
    where

    equiv-left-iterated-dirichlet-product-species-subuniverse :
      dirichlet-product-species-subuniverse' P Q
        ( dirichlet-product-species-subuniverse P Q C1 S T)
        ( U)
        ( X) ≃
      Σ ( ternary-product-Decomposition P X)
        ( λ d →
          inclusion-subuniverse Ql2
            ( S (first-summand-ternary-product-Decomposition P X d)) ×
            ( inclusion-subuniverse Ql3
              ( T (second-summand-ternary-product-Decomposition P X d)) ×
              inclusion-subuniverse Ql4
              ( U (third-summand-ternary-product-Decomposition P X d))))
    equiv-left-iterated-dirichlet-product-species-subuniverse =
      ( ( equiv-Σ
          ( λ d →
            inclusion-subuniverse Ql2
            ( S (first-summand-ternary-product-Decomposition P X d)) ×
            ( inclusion-subuniverse Ql3
              ( T (second-summand-ternary-product-Decomposition P X d)) ×
              inclusion-subuniverse Ql4
              ( U (third-summand-ternary-product-Decomposition P X d)))))
          ( ( equiv-Σ
              ( _)
              ( assoc-prod _ _ _ ∘e commutative-prod)
              ( λ x →
                equiv-postcomp-equiv
                  ( ( assoc-prod _ _ _ ∘e
                    ( commutative-prod)) )
                  ( inclusion-subuniverse P X)) ∘e
              equiv-ternary-left-iterated-product-Decomposition P X C2))
          ( λ d → assoc-prod _ _ _) ∘e
        ( ( inv-assoc-Σ
            ( binary-product-Decomposition P X)
            ( λ z → binary-product-Decomposition P (pr1 z))
            ( _)) ∘e
          ( ( equiv-tot  λ d → right-distributive-prod-Σ))))

    equiv-right-iterated-dirichlet-product-species-subuniverse :
      dirichlet-product-species-subuniverse' P Q
        ( S)
        ( dirichlet-product-species-subuniverse P Q C1 T U)
        ( X) ≃
      Σ ( ternary-product-Decomposition P X)
        ( λ d →
          inclusion-subuniverse Ql2
            ( S (first-summand-ternary-product-Decomposition P X d)) ×
            ( inclusion-subuniverse Ql3
              ( T (second-summand-ternary-product-Decomposition P X d)) ×
                inclusion-subuniverse Ql4
              ( U (third-summand-ternary-product-Decomposition P X d))))
    equiv-right-iterated-dirichlet-product-species-subuniverse =
      ( ( equiv-Σ-equiv-base
          ( _)
          ( equiv-ternary-right-iterated-product-Decomposition P X C2)) ∘e
        ( ( inv-assoc-Σ
            ( binary-product-Decomposition P X)
            ( λ z → binary-product-Decomposition P (pr1 (pr2 z)))
            ( _)) ∘e
          ( ( equiv-tot (λ d → left-distributive-prod-Σ)))))

    equiv-associative-dirichlet-product-species-subuniverse :
      dirichlet-product-species-subuniverse' P Q
        ( dirichlet-product-species-subuniverse P Q C1 S T)
        ( U)
        ( X) ≃
      dirichlet-product-species-subuniverse' P Q
        ( S)
        ( dirichlet-product-species-subuniverse P Q C1 T U)
        ( X)
    equiv-associative-dirichlet-product-species-subuniverse =
      inv-equiv (equiv-right-iterated-dirichlet-product-species-subuniverse) ∘e
      equiv-left-iterated-dirichlet-product-species-subuniverse

  module _
    (S : species-subuniverse P Ql2)
    (T : species-subuniverse P Ql3)
    (U : species-subuniverse P Ql4)
    where

    associative-dirichlet-product-species-subuniverse :
      dirichlet-product-species-subuniverse P Q C1
        ( dirichlet-product-species-subuniverse P Q C1 S T)
        ( U) ＝
      dirichlet-product-species-subuniverse P Q C1
        ( S)
        ( dirichlet-product-species-subuniverse P Q C1 T U)
    associative-dirichlet-product-species-subuniverse =
      eq-equiv-fam-subuniverse
        ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
        ( dirichlet-product-species-subuniverse P Q C1
          ( dirichlet-product-species-subuniverse P Q C1 S T)
          ( U))
        ( dirichlet-product-species-subuniverse P Q C1
          ( S)
          ( dirichlet-product-species-subuniverse P Q C1 T U))
        ( equiv-associative-dirichlet-product-species-subuniverse S T U)
```
