# Existential quantification

```agda
module foundation.existential-quantification where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.logical-equivalences
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

Given a family of [propositions](foundation-core.propositions.md) `P` over `A`,
the
{{#concept "existential quantification" Disambiguation="on a subtype" WDID=Q773483 WD="existential quantification" Agda=exists}}
of `P` over `A` is the proposition `∃ A P` asserting that there is an element
`a : A` such that `P a` holds. We use the
[propositional truncation](foundation.propositional-truncations.md) to define
the existential quantification,

```text
  ∃ (x : A), (P x) := ║ Σ (x : A), (P x) ║₋₁
```

because the
[Curry–Howard interpretation](https://en.wikipedia.org/wiki/Curry–Howard_correspondence)
of the existential quantification as `Σ A P` does not guarantee that existential
quantifications are interpreted as propositions.

The
{{#concept "universal property" Disambiguation="of existential quantification" Agda=universal-property-exists}}
of existential quantification states that it is the
[least upper bound](order-theory.least-upper-bounds-large-posets.md) on the
family of propositions `P` in the
[locale of propositions](foundation.large-locale-of-propositions.md), by which
we mean that for every proposition `Q` we have the
[logical equivalence](foundation.logical-equivalences.md)

```text
  (∀ (x : A), (P x ⇒ Q)) ⇔ ((∃ (x : A), (P x)) ⇒ Q).
```

## Definitions

### Existence of structure

Given a [structure](foundation.structure.md) `B : A → 𝒰` on a type `A`, the
propositional truncation

```text
  ║ Σ (x : A), (B x) ║₋₁
```

satisfies the universal property of the existential quantification

```text
  ∃ (x : A), ║ B x ║₋₁
```

and is thus equivalent to it. Therefore, we may reasonably call this
construction the
{{#concept "existential quantification" Disambiguation="structure" Agda=exists-structure-Prop}}
of structure. It is important to keep in mind that this is not a generalization
of the concept but rather a conflation, and should be read as the statement _the
type of elements `x : A` equipped with `y : B x` is
[inhabited](foundation.inhabited-types.md)_.

Existence of structure is a widely occurring notion in univalent mathematics.
For instance, the condition that an element `y : B` is in the
[image](foundation.images.md) of a map `f : A → B` is formulated using existence
of structure: The element `y` is in the image of `f` if the type of `x : A`
equipped with an identification `f x = y` is inhabited.

Because subtypes are a special case of structure, and Agda can generally infer
structures for us, we will continue to conflate the two in our formalizations
for the benefit that we have to specify the subtype in our code less often. For
instance, even though the introduction rule for existential quantification
`intro-exists` is phrased in terms of existential quantification on structures,
it equally applies to existential quantification on subtypes.

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2)
  where

  exists-structure-Prop : Prop (l1 ⊔ l2)
  exists-structure-Prop = trunc-Prop (Σ A B)

  exists-structure : UU (l1 ⊔ l2)
  exists-structure = type-Prop exists-structure-Prop

  is-prop-exists-structure : is-prop exists-structure
  is-prop-exists-structure = is-prop-type-Prop exists-structure-Prop
```

### Existential quantification

```agda
module _
  {l1 l2 : Level} (A : UU l1) (P : A → Prop l2)
  where

  exists-Prop : Prop (l1 ⊔ l2)
  exists-Prop = exists-structure-Prop A (type-Prop ∘ P)

  exists : UU (l1 ⊔ l2)
  exists = type-Prop exists-Prop

  abstract
    is-prop-exists : is-prop exists
    is-prop-exists = is-prop-type-Prop exists-Prop

  ∃ : Prop (l1 ⊔ l2)
  ∃ = exists-Prop
```

### The introduction rule for existential quantification

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  intro-exists : (a : A) (b : B a) → exists-structure A B
  intro-exists a b = unit-trunc-Prop (a , b)
```

**Note.** Even though the introduction rule is formalized in terms of
existential quantification on structures, it equally applies to existential
quantification on subtypes. This is because subtypes are a special case of
structure. The benefit of this approach is that Agda can infer structures for
us, but not generally subtypes.

### The universal property of existential quantification

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (S : Prop l3)
  where

  universal-property-exists-structure : UUω
  universal-property-exists-structure =
    {l : Level} (Q : Prop l) →
    (type-Prop S → type-Prop Q) ↔ ((x : A) → B x → type-Prop Q)

module _
  {l1 l2 l3 : Level} (A : UU l1) (P : A → Prop l2) (S : Prop l3)
  where

  universal-property-exists : UUω
  universal-property-exists =
    universal-property-exists-structure A (type-Prop ∘ P) S
```

## Properties

### The elimination rule of existential quantification

The
{{#concept "universal property" Disambiguation="of existential quantification"}}
of existential quantification states `∃ A P` is the least upper bound on the
predicate `P` in the locale of propositions.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  where

  ev-intro-exists :
    {C : UU l3} → (exists-structure A B → C) → (x : A) → B x → C
  ev-intro-exists H x p = H (intro-exists x p)

  elim-exists :
    (Q : Prop l3) →
    ((x : A) → B x → type-Prop Q) → (exists-structure A B → type-Prop Q)
  elim-exists Q f = map-universal-property-trunc-Prop Q (ind-Σ f)

  abstract
    is-equiv-ev-intro-exists :
      (Q : Prop l3) → is-equiv (ev-intro-exists {type-Prop Q})
    is-equiv-ev-intro-exists Q =
      is-equiv-has-converse
        ( function-Prop (exists-structure A B) Q)
        ( Π-Prop A (λ x → function-Prop (B x) Q))
        ( elim-exists Q)
```

Note that since existential quantification is implemented using propositional
truncation, the associated
[`do` syntax](foundation.propositional-truncations.md#do-syntax) can be used to
simplify deeply nested chains of `elim-exists`.

### The existential quantification satisfies the universal property of existential quantification

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  up-exists :
    universal-property-exists-structure A B (exists-structure-Prop A B)
  up-exists Q = (ev-intro-exists , elim-exists Q)
```

### Propositions that satisfy the universal property of a existential quantification are equivalent to the existential quantification

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (Q : Prop l3)
  (up-Q : universal-property-exists-structure A B Q)
  where

  forward-implication-iff-universal-property-exists :
    exists-structure A B → type-Prop Q
  forward-implication-iff-universal-property-exists =
    elim-exists Q (forward-implication (up-Q Q) id)

  backward-implication-iff-universal-property-exists :
    type-Prop Q → exists-structure A B
  backward-implication-iff-universal-property-exists =
    backward-implication (up-Q (exists-structure-Prop A B)) intro-exists

  iff-universal-property-exists :
    exists-structure A B ↔ type-Prop Q
  iff-universal-property-exists =
    ( forward-implication-iff-universal-property-exists ,
      backward-implication-iff-universal-property-exists)
```

### Existential quantification of structure is the same as existential quantification over its propositional reflection

We proceed by showing that the latter satisfies the universal property of the
former.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  universal-property-exists-structure-exists-trunc-Prop :
    universal-property-exists-structure A B (exists-Prop A (trunc-Prop ∘ B))
  universal-property-exists-structure-exists-trunc-Prop Q =
    ( λ f a b → f (unit-trunc-Prop (a , unit-trunc-Prop b))) ,
    ( λ f → rec-trunc-Prop Q (λ (a , |b|) → rec-trunc-Prop Q (f a) |b|))

  compute-exists-trunc-Prop : exists-structure A B ↔ exists A (trunc-Prop ∘ B)
  compute-exists-trunc-Prop =
    iff-universal-property-exists
      ( exists-Prop A (trunc-Prop ∘ B))
      ( universal-property-exists-structure-exists-trunc-Prop)
```

### Taking the cartesian product with a proposition distributes over existential quantification of structures

```agda
module _
  {l1 l2 l3 : Level} (P : Prop l1) {A : UU l2} {B : A → UU l3}
  where

  map-distributive-product-exists-structure :
    type-Prop P × exists-structure A B →
    exists-structure A (λ x → type-Prop P × B x)
  map-distributive-product-exists-structure (p , e) =
    elim-exists
      ( exists-structure-Prop A (λ x → type-Prop P × B x))
      ( λ x q → intro-exists x (p , q))
      ( e)

  map-inv-distributive-product-exists-structure :
    exists-structure A (λ x → type-Prop P × B x) →
    type-Prop P × exists-structure A B
  map-inv-distributive-product-exists-structure =
    elim-exists
      ( P ∧ exists-structure-Prop A B)
      ( λ x (p , q) → (p , intro-exists x q))

  iff-distributive-product-exists-structure :
    ( type-Prop P × exists-structure A B) ↔
    ( exists-structure A (λ x → type-Prop P × B x))
  iff-distributive-product-exists-structure =
    ( map-distributive-product-exists-structure ,
      map-inv-distributive-product-exists-structure)

  eq-distributive-product-exists-structure :
    P ∧ exists-structure-Prop A B ＝
    exists-structure-Prop A (λ x → type-Prop P × B x)
  eq-distributive-product-exists-structure =
    eq-iff'
      ( P ∧ exists-structure-Prop A B)
      ( exists-structure-Prop A (λ x → type-Prop P × B x))
      ( iff-distributive-product-exists-structure)
```

### Conjunction distributes over existential quantification

```agda
module _
  {l1 l2 l3 : Level} (P : Prop l1) {A : UU l2} (Q : A → Prop l3)
  where

  map-distributive-conjunction-exists :
    type-Prop (P ∧ (∃ A Q) ⇒ ∃ A (λ x → P ∧ Q x))
  map-distributive-conjunction-exists =
    map-distributive-product-exists-structure P

  map-inv-distributive-conjunction-exists :
    type-Prop (∃ A (λ x → P ∧ Q x) ⇒ P ∧ (∃ A Q))
  map-inv-distributive-conjunction-exists =
    map-inv-distributive-product-exists-structure P

  iff-distributive-conjunction-exists :
    type-Prop (P ∧ ∃ A Q ⇔ ∃ A (λ x → P ∧ Q x))
  iff-distributive-conjunction-exists =
    iff-distributive-product-exists-structure P

  eq-distributive-conjunction-exists :
    P ∧ (∃ A Q) ＝ ∃ A (λ x → P ∧ Q x)
  eq-distributive-conjunction-exists =
    eq-distributive-product-exists-structure P
```

## See also

- Existential quantification is the indexed counterpart to
  [disjunction](foundation.disjunction.md)

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}

## External links

- [existential quantifier](https://ncatlab.org/nlab/show/existential+quantifier)
  at $n$Lab
