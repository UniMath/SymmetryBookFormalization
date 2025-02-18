# Equivalences of fiber inclusions of maps

```agda
module synthetic-homotopy-theory.equivalences-fiber-inclusions-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-homotopies
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.fiber-inclusions-of-maps
```

</details>

## Idea

An
{{#concept "equivalence" Disambiguation="of fiber inclusions of maps" Agda=equiv-fiber-inclusion-of-map}}
of two [fiber inclusions](synthetic-homotopy-theory.fiber-inclusions-of-maps.md)
of `g` at `z`,

```text
       f         f'
  A ------> B <------ A'
  | ⌟       |       ⌞ |
  |    H    | g  H'   |
  ∨         ∨         ∨
  * ------> C <------ *
       z         z
```

consists of an [equivalence](foundation-core.equivalences.md) of types
`e : A ≃ A'` together with a [homotopy](foundation-core.homotopies.md)
`K : f ~ f' ∘ e` such that `H ~ H' ·r e ∙h g ·l K`.

## Definitions

```agda
module _
  {l1 l2 l3 : Level} {B : UU l1} {C : UU l2} {g : B → C} {z : C}
  where

  equiv-fiber-inclusion-of-map :
    {l4 : Level} →
    fiber-inclusion-of-map l3 g z → fiber-inclusion-of-map l4 g z →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-fiber-inclusion-of-map (A , f , H , _) (A' , f' , H' , _) =
    Σ ( A ≃ A')
      ( λ e →
        Σ ( coherence-triangle-maps f f' (map-equiv e))
          ( λ K → coherence-triangle-homotopies H (H' ·r map-equiv e) (g ·l K)))

  id-equiv-fiber-inclusion-of-map :
    (F : fiber-inclusion-of-map l3 g z) → equiv-fiber-inclusion-of-map F F
  id-equiv-fiber-inclusion-of-map F = (id-equiv , refl-htpy , refl-htpy)

  equiv-eq-fiber-inclusion-of-map :
    (F F' : fiber-inclusion-of-map l3 g z) →
    F ＝ F' → equiv-fiber-inclusion-of-map F F'
  equiv-eq-fiber-inclusion-of-map F .F refl = id-equiv-fiber-inclusion-of-map F
```

## Properties

### Equivalences characterize equality of fiber inclusions

```agda
module _
  {l1 l2 l3 : Level} {B : UU l1} {C : UU l2} {g : B → C} {z : C}
  where

  is-torsorial-equiv-fiber-inclusion-of-map :
    (F : fiber-inclusion-of-map l3 g z) →
    is-torsorial (equiv-fiber-inclusion-of-map F)
  is-torsorial-equiv-fiber-inclusion-of-map F =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv (type-fiber-inclusion-of-map F))
      ( type-fiber-inclusion-of-map F , id-equiv)
      ( is-torsorial-Eq-structure
        ( is-torsorial-htpy (inclusion-fiber-inclusion-of-map F))
        ( inclusion-fiber-inclusion-of-map F , refl-htpy)
        ( is-torsorial-Eq-subtype
          ( is-torsorial-htpy (compute-point-fiber-inclusion-of-map F))
          ( is-property-is-equiv ∘
            ( map-fiber-fiber-inclusion-of-map g z
              ( inclusion-fiber-inclusion-of-map F)))
          ( compute-point-fiber-inclusion-of-map F)
          ( refl-htpy)
          ( is-fiber-inclusion-fiber-inclusion-of-map F)))

  is-equiv-equiv-eq-fiber-inclusion-of-map :
    (F F' : fiber-inclusion-of-map l3 g z) →
    is-equiv (equiv-eq-fiber-inclusion-of-map F F')
  is-equiv-equiv-eq-fiber-inclusion-of-map F =
    fundamental-theorem-id
      ( is-torsorial-equiv-fiber-inclusion-of-map F)
      ( equiv-eq-fiber-inclusion-of-map F)

  extensionality-fiber-inclusion-of-map :
    (F F' : fiber-inclusion-of-map l3 g z) →
    (F ＝ F') ≃ equiv-fiber-inclusion-of-map F F'
  extensionality-fiber-inclusion-of-map F F' =
    ( equiv-eq-fiber-inclusion-of-map F F' ,
      is-equiv-equiv-eq-fiber-inclusion-of-map F F')

  eq-equiv-fiber-inclusion-of-map :
    (F F' : fiber-inclusion-of-map l3 g z) →
    equiv-fiber-inclusion-of-map F F' → F ＝ F'
  eq-equiv-fiber-inclusion-of-map F F' =
    map-inv-equiv (extensionality-fiber-inclusion-of-map F F')
```
