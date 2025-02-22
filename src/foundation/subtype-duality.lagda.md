# Subtype duality

```agda
module foundation.subtype-duality where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.propositional-maps
open import foundation.structured-type-duality
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.propositions
```

</details>

## Idea

The {{#concept "subtype duality" Agda=equiv-Fiber-Prop}} principle establishes an equivalence

$$
  \left(\sum_{A:\mathcal{U}} X\hookrightarrow A\right) \simeq (A \to \mathrm{Prop}),
$$

In other words, it establishes a unique correspondence between [embeddings](foundation-core.embeddings.md) into a type $A$, and [subtypes](foundation-core.subtypes.md) of $A$.

## Theorem

### Subtype duality

```agda
Slice-emb : (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
Slice-emb l A = Σ (UU l) (λ X → X ↪ A)

equiv-Fiber-Prop :
  (l : Level) {l1 : Level} (A : UU l1) →
  Slice-emb (l1 ⊔ l) A ≃ (A → Prop (l1 ⊔ l))
equiv-Fiber-Prop l A =
  ( equiv-Fiber-structure l is-prop A) ∘e
  ( equiv-tot (λ X → equiv-tot equiv-is-prop-map-is-emb))
```

### Inhabited type duality

```agda
Slice-surjection : (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
Slice-surjection l A = Σ (UU l) (λ X → X ↠ A)

equiv-Fiber-trunc-Prop :
  (l : Level) {l1 : Level} (A : UU l1) →
  Slice-surjection (l1 ⊔ l) A ≃ (A → Inhabited-Type (l1 ⊔ l))
equiv-Fiber-trunc-Prop l A =
  ( equiv-Fiber-structure l is-inhabited A)
```
