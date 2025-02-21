# Decidable families

```agda
module foundation.decidable-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.coproduct-types
open import foundation.decidable-maps
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.equivalences
open import foundation.hilberts-epsilon-operators
open import foundation.injective-maps
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.retracts-of-types
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

A type family `B : A → 𝒰` is said to be
{{#concept "decidable" Disambiguation="type family" Agda=is-decidable-family}}
if we, for every `x : A`, can either construct an element of `B x`, or we can
prove that it is [empty](foundation-core.empty-types.md). In other words, we
interpret decidability via the
[Curry–Howard interpretation](https://en.wikipedia.org/wiki/Curry–Howard_correspondence)
of logic into type theory. A related concept is that a type family is either
[inhabited](foundation.inhabited-types.md) or empty, where inhabitedness of a
type is expressed using the
[propositional truncation](foundation.propositional-truncations.md).

## Definitions

### The Curry–Howard interpretation of decidability

```agda
is-decidable-family : {l1 l2 : Level} {A : UU l1} (P : A → UU l2) → UU (l1 ⊔ l2)
is-decidable-family {A = A} P = (x : A) → is-decidable (P x)

decidable-family : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
decidable-family l2 A = Σ (A → UU l2) is-decidable-family

module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-family l2 A)
  where

  family-decidable-family : A → UU l2
  family-decidable-family = pr1 P

  is-decidable-decidable-family : is-decidable-family family-decidable-family
  is-decidable-decidable-family = pr2 P
```

### The underlying decidable type family of a decidable subtype

```agda
decidable-family-decidable-subtype :
  {l1 l2 : Level} {A : UU l1} → decidable-subtype l2 A → decidable-family l2 A
decidable-family-decidable-subtype P =
  ( is-in-decidable-subtype P , is-decidable-decidable-subtype P)
```

## Properties

### Reindexing decidable type families

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (P : decidable-family l3 B)
  where

  reindex-decidable-family : (f : A → B) → decidable-family l3 A
  reindex-decidable-family f =
    ( family-decidable-family P ∘ f , is-decidable-decidable-family P ∘ f)
```

### The negation of a decidable family is decidable

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : decidable-family l2 A)
  where

  is-decidable-neg-decidable-family :
    is-decidable-family (¬_ ∘ family-decidable-family P)
  is-decidable-neg-decidable-family =
    is-decidable-neg ∘ is-decidable-decidable-family P

  neg-decidable-family : decidable-family l2 A
  neg-decidable-family =
    ( ¬_ ∘ family-decidable-family P , is-decidable-neg-decidable-family)
```

### Composition of decidable families

Given a decidable type family of propositions `P : A → 𝒰` and a decidable type
family `Q : (x : A) → P x → 𝒰` then we may _compose_ `Q` after `P` and obtain a
decidabe type family `Q ∘ P : A → 𝒰`.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1}
  where

  is-decidable-comp-decidable-family-decidable-subtype' :
    (P : decidable-family l2 A)
    (Q : (x : A) → decidable-family l3 (family-decidable-family P x)) →
    ((x : A) → is-prop (family-decidable-family P x)) →
    is-decidable-family
      ( λ x → Σ (family-decidable-family P x) (family-decidable-family (Q x)))
  is-decidable-comp-decidable-family-decidable-subtype' P Q H x =
    rec-coproduct
      ( λ p →
        rec-coproduct
          ( λ q → inl (p , q))
          (λ nq →
            inr
              ( map-neg
                ( λ pq →
                  tr
                    ( family-decidable-family (Q x))
                    ( eq-is-prop (H x))
                    ( pr2 pq))
                ( nq)))
          ( is-decidable-decidable-family (Q x) p))
      (λ np → inr (map-neg pr1 np))
      ( is-decidable-decidable-family P x)

  comp-decidable-family-decidable-subtype' :
    (P : decidable-family l2 A) →
    ((x : A) → decidable-family l3 (family-decidable-family P x)) →
    ((x : A) → is-prop (family-decidable-family P x)) →
    decidable-family (l2 ⊔ l3) A
  comp-decidable-family-decidable-subtype' P Q H =
    ( λ x → Σ (family-decidable-family P x) (family-decidable-family (Q x))) ,
    ( is-decidable-comp-decidable-family-decidable-subtype' P Q H)

  comp-decidable-family-decidable-subtype :
    (P : decidable-subtype l2 A) →
    ((x : A) → decidable-family l3 (is-in-decidable-subtype P x)) →
    decidable-family (l2 ⊔ l3) A
  comp-decidable-family-decidable-subtype P Q =
    comp-decidable-family-decidable-subtype'
      ( decidable-family-decidable-subtype P)
      ( Q)
      ( is-prop-is-in-decidable-subtype P)
```

**Comment.** It should be possible to relax the condition on `P` of being a
family of propositions to asking that the first projection map `Σ A P → A` is
injective.

### Decidable families on the subuniverse of propositions

```text
blabla :
  {l1 l2 : Level} (P : decidable-family l2 (Prop l1)) →
  family-decidable-family P (raise-empty-Prop l1) ＝
  family-decidable-family P (raise-unit-Prop l1) →
  (Q : Prop l1) →
  family-decidable-family P (raise-empty-Prop l1) ＝ family-decidable-family P Q
blabla = {!   !}
```

## See also

- [Uniformly decidable type families](foundation.uniformly-decidable-type-families.md)
