# Diaconescu's theorem

```agda
module foundation.diaconescus-theorem where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.axiom-of-choice
open import foundation.booleans
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types

open import synthetic-homotopy-theory.suspensions-of-propositions
open import synthetic-homotopy-theory.suspensions-of-types
```

</details>

## Idea

The [axiom of choice](foundation.axiom-of-choice.md) implies the
[law of excluded middle](foundation.law-of-excluded-middle.md). This is often
referred to as
{{#concept "Diaconescu's theorem" WD="Diaconescu's theorem" WDID=Q3527059 Agda=theorem-Diaconescu}}.

## Theorem

We follow the proof given under Theorem 10.1.14 in {{#cite UF13}}.

**Proof.** Given a [proposition](foundation-core.propositions.md) `P`, then its
[suspension](synthetic-homotopy-theory.suspensions-of-propositions.md) `ΣP` is a
[set](foundation-core.sets.md) with the property that `(N ＝ S) ≃ ΣP`, where `N`
and `S` are the _poles_ of `ΣP`. There is a surjection from the
[booleans](foundation.booleans.md) onto the suspension `f : bool ↠ ΣP` such that
`f true ≐ N` and `f false ≐ S`. Its
[fiber family](foundation-core.fibers-of-maps.md) is in other words an
[inhabited](foundation.inhabited-types.md) family over `ΣP`. Applying the axiom
of choice to this family, we obtain a
[mere](foundation.propositional-truncations.md)
[section](foundation-core.sections.md) `s` of `f` which thus exhibits `P` as a
[logical equivalent](foundation.logical-equivalences.md) to `f⁻¹ N ＝ f⁻¹ S`.
The latter is an [equation](foundation-core.identity-types.md) of booleans, and
the booleans have [decidable equality](foundation.decidable-equality.md) so `P`
must also be [decidable](foundation.decidable-propositions.md).

```agda
instance-theorem-Diaconescu :
  {l : Level} (P : Prop l) →
  instance-choice₀
    ( suspension-set-Prop P)
    ( fiber map-surjection-bool-suspension) →
  is-decidable-type-Prop P
instance-theorem-Diaconescu P ac-P =
  rec-trunc-Prop
    ( is-decidable-Prop P)
    ( λ s →
      is-decidable-iff'
        ( ( iff-equiv (compute-eq-north-south-suspension-Prop P)) ∘iff
          ( ( λ p →
              ( inv (pr2 (s north-suspension))) ∙
              ( ap map-surjection-bool-suspension p) ∙
              ( pr2 (s south-suspension))) ,
            ( ap (pr1 ∘ s))))
        ( has-decidable-equality-bool
          ( pr1 (s north-suspension))
          ( pr1 (s south-suspension))))
    ( ac-P is-surjective-map-surjection-bool-suspension)

theorem-Diaconescu :
  {l : Level} → level-axiom-of-choice l l → level-LEM l
theorem-Diaconescu ac P =
  instance-theorem-Diaconescu P
    ( ac (suspension-set-Prop P) (fiber map-surjection-bool-suspension))
```

## References

{{#bibliography}}
