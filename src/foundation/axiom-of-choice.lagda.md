# The axiom of choice

```agda
module foundation.axiom-of-choice where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.functoriality-propositional-truncation
open import foundation.inhabited-types
open import foundation.postcomposition-functions
open import foundation.projective-types
open import foundation.propositional-truncations
open import foundation.sections
open import foundation.split-surjective-maps
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.precomposition-functions
open import foundation-core.sets
```

</details>

## Idea

The {{#concept "axiom of choice" WD="axiom of choice" WDID=Q179692 Agda=AC0}}
asserts that for every family of [inhabited](foundation.inhabited-types.md)
types `B` indexed by a [set](foundation-core.sets.md) `A`, the type of sections
of that family `(x : A) → B x` is inhabited.

## Definition

### Instances of choice

```agda
instance-choice : {l1 l2 : Level} (A : UU l1) → (A → UU l2) → UU (l1 ⊔ l2)
instance-choice A B =
  ((x : A) → is-inhabited (B x)) → is-inhabited ((x : A) → B x)
```

Note that the above statement, were it true for all indexing types `A`, is
inconsistent with [univalence](foundation.univalence.md). For a concrete
counterexample see Lemma 3.8.5 in {{#cite UF13}}.

### The axiom of choice restricted to sets

```agda
instance-choice-Set :
  {l1 l2 : Level} (A : Set l1) → (type-Set A → Set l2) → UU (l1 ⊔ l2)
instance-choice-Set A B = instance-choice (type-Set A) (type-Set ∘ B)

level-axiom-of-choice-Set : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
level-axiom-of-choice-Set l1 l2 =
  (A : Set l1) (B : type-Set A → Set l2) → instance-choice-Set A B

axiom-of-choice-Set : UUω
axiom-of-choice-Set = {l1 l2 : Level} → level-axiom-of-choice-Set l1 l2
```

### The axiom of choice

```agda
instance-choice₀ :
  {l1 l2 : Level} (A : Set l1) → (type-Set A → UU l2) → UU (l1 ⊔ l2)
instance-choice₀ A = instance-choice (type-Set A)

level-axiom-of-choice : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
level-axiom-of-choice l1 l2 =
  (A : Set l1) (B : type-Set A → UU l2) → instance-choice₀ A B

axiom-of-choice : UUω
axiom-of-choice = {l1 l2 : Level} → level-axiom-of-choice l1 l2
```

## Properties

### Every type is set-projective if and only if the axiom of choice holds

```agda
is-set-projective-axiom-of-choice :
  {l1 l2 l3 : Level} → level-axiom-of-choice l2 (l1 ⊔ l2) →
  (X : UU l3) → is-set-projective l1 l2 X
is-set-projective-axiom-of-choice ac X A B f h =
  map-trunc-Prop
    ( ( map-Σ
        ( λ g → ((map-surjection f) ∘ g) ＝ h)
        ( precomp h A)
        ( λ s H → htpy-postcomp X H h)) ∘
      ( section-is-split-surjective (map-surjection f)))
    ( ac B (fiber (map-surjection f)) (is-surjective-map-surjection f))

axiom-of-choice-is-set-projective :
  {l1 l2 : Level} →
  ({l : Level} (X : UU l) → is-set-projective (l1 ⊔ l2) l1 X) →
  level-axiom-of-choice l1 l2
axiom-of-choice-is-set-projective H A B K =
  map-trunc-Prop
    ( map-equiv (equiv-Π-section-pr1 {B = B}) ∘ tot (λ g → htpy-eq))
    ( H ( type-Set A)
        ( Σ (type-Set A) B)
        ( A)
        ( pr1 , (λ a → map-trunc-Prop (map-inv-fiber-pr1 B a) (K a)))
        ( id))
```

## See also

- [Diaconescu's theorem](foundation.diaconescus-theorem.md), which states that
  the axiom of choice implies the law of excluded middle.

## Table of choice principles

{{#include tables/choice-principles.md}}

## References

{{#bibliography}}
