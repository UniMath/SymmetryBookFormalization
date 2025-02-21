# Decidability of dependent function types

```agda
module foundation.decidable-dependent-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-function-types
open import foundation.irrefutable-equality
open import foundation.maybe
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.uniformly-decidable-type-families
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-maybe
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.negation

open import logic.propositionally-decidable-types
```

</details>

## Idea

We describe conditions under which
[dependent function types](foundation.dependent-function-types.md) are
[decidable](foundation.decidable-types.md).

## Properties

### Decidability of dependent products of uniformly decidable families

```agda
is-decidable-Π-uniformly-decidable-family :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-decidable A →
  is-uniformly-decidable-family B →
  is-decidable ((a : A) → (B a))
is-decidable-Π-uniformly-decidable-family (inl a) (inl b) =
  inl b
is-decidable-Π-uniformly-decidable-family (inl a) (inr b) =
  inr (λ f → b a (f a))
is-decidable-Π-uniformly-decidable-family (inr na) _ =
  inl (ex-falso ∘ na)

is-decidable-prop-Π-uniformly-decidable-family :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-decidable A →
  is-uniformly-decidable-family B →
  ((x : A) → is-prop (B x)) →
  is-decidable-prop ((a : A) → (B a))
is-decidable-prop-Π-uniformly-decidable-family dA dB H =
  ( is-prop-Π H , is-decidable-Π-uniformly-decidable-family dA dB)

abstract
  is-decidable-prop-Π-uniformly-decidable-family' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-inhabited-or-empty A →
    is-uniformly-decidable-family B →
    ((x : A) → is-prop (B x)) →
    is-decidable-prop ((a : A) → (B a))
  is-decidable-prop-Π-uniformly-decidable-family' {A = A} {B} dA dB H =
    elim-is-inhabited-or-empty-Prop'
      ( is-decidable-prop-Prop ((a : A) → (B a)))
      ( λ d → is-decidable-prop-Π-uniformly-decidable-family d dB H)
      ( dA)
```

### Decidablitilty of dependent products over coproducts

```agda
is-decidable-Π-coproduct :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A + B → UU l3} →
  is-decidable ((a : A) → C (inl a)) →
  is-decidable ((b : B) → C (inr b)) →
  is-decidable ((x : A + B) → C x)
is-decidable-Π-coproduct {C = C} dA dB =
  is-decidable-equiv
    ( equiv-dependent-universal-property-coproduct C)
    ( is-decidable-product dA dB)
```

### Decidability of dependent products over `Maybe`

```agda
is-decidable-Π-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  is-decidable ((x : A) → B (unit-Maybe x)) →
  is-decidable (B exception-Maybe) →
  is-decidable ((x : Maybe A) → B x)
is-decidable-Π-Maybe {B = B} du de =
  is-decidable-equiv
    ( equiv-dependent-universal-property-Maybe B)
    ( is-decidable-product du de)
```

### Dependent products of decidable propositions over an irrefutably π₀-trivial base are decidable propositions

Assuming the base `A` is empty or 0-connected, a dependent product of decidable
propositions over `A` is again a decidable proposition.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → Decidable-Prop l2)
  where

  is-decidable-Π-all-elements-irrefutably-equal-base :
    all-elements-irrefutably-equal A →
    is-decidable A →
    is-decidable ((x : A) → type-Decidable-Prop (B x))
  is-decidable-Π-all-elements-irrefutably-equal-base H dA =
    is-decidable-Π-uniformly-decidable-family dA
      ( is-uniformly-decidable-family-all-elements-irrefutably-equal-base
        ( H)
        ( is-decidable-Decidable-Prop ∘ B)
        ( dA))

  is-decidable-prop-Π-all-elements-irrefutably-equal-base :
    all-elements-irrefutably-equal A →
    is-decidable A →
    is-decidable-prop ((x : A) → type-Decidable-Prop (B x))
  is-decidable-prop-Π-all-elements-irrefutably-equal-base H dA =
    is-decidable-prop-Π-uniformly-decidable-family dA
      ( is-uniformly-decidable-family-all-elements-irrefutably-equal-base
        ( H)
        ( is-decidable-Decidable-Prop ∘ B)
        ( dA))
      ( is-prop-type-Decidable-Prop ∘ B)

  is-decidable-prop-Π-all-elements-irrefutably-equal-base' :
    all-elements-irrefutably-equal A →
    is-inhabited-or-empty A →
    is-decidable-prop ((x : A) → type-Decidable-Prop (B x))
  is-decidable-prop-Π-all-elements-irrefutably-equal-base' H dA =
    is-decidable-prop-Π-uniformly-decidable-family' dA
      ( is-uniformly-decidable-family-all-elements-irrefutably-equal-base'
        ( H)
        ( is-decidable-Decidable-Prop ∘ B)
        ( dA)
        ( is-prop-type-Decidable-Prop ∘ B))
      ( is-prop-type-Decidable-Prop ∘ B)
```

### Dependent products of decidable propositions over an π₀-trivial base are decidable propositions

Assuming the base `A` is empty or 0-connected, a dependent product of decidable
propositions over `A` is again a decidable proposition.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → Decidable-Prop l2)
  where

  is-decidable-Π-all-elements-merely-equal-base :
    all-elements-merely-equal A →
    is-decidable A →
    is-decidable ((x : A) → type-Decidable-Prop (B x))
  is-decidable-Π-all-elements-merely-equal-base H dA =
    is-decidable-Π-uniformly-decidable-family dA
      ( is-uniformly-decidable-family-all-elements-merely-equal-base
        ( H)
        ( is-decidable-Decidable-Prop ∘ B)
        ( dA))

  is-decidable-prop-Π-all-elements-merely-equal-base :
    all-elements-merely-equal A →
    is-decidable A →
    is-decidable-prop ((x : A) → type-Decidable-Prop (B x))
  is-decidable-prop-Π-all-elements-merely-equal-base H dA =
    is-decidable-prop-Π-uniformly-decidable-family dA
      ( is-uniformly-decidable-family-all-elements-merely-equal-base
        ( H)
        ( is-decidable-Decidable-Prop ∘ B)
        ( dA))
      ( is-prop-type-Decidable-Prop ∘ B)

  is-decidable-prop-Π-all-elements-merely-equal-base' :
    all-elements-merely-equal A →
    is-inhabited-or-empty A →
    is-decidable-prop ((x : A) → type-Decidable-Prop (B x))
  is-decidable-prop-Π-all-elements-merely-equal-base' H dA =
    is-decidable-prop-Π-uniformly-decidable-family' dA
      ( is-uniformly-decidable-family-all-elements-merely-equal-base'
        ( H)
        ( is-decidable-Decidable-Prop ∘ B)
        ( dA)
        ( is-prop-type-Decidable-Prop ∘ B))
      ( is-prop-type-Decidable-Prop ∘ B)
```

### Decidability of dependent products over an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x))
  where

  is-decidable-Π-equiv :
    is-decidable ((x : A) → C x) → is-decidable ((y : B) → D y)
  is-decidable-Π-equiv = is-decidable-equiv' (equiv-Π D e f)

  is-decidable-Π-equiv' :
    is-decidable ((y : B) → D y) → is-decidable ((x : A) → C x)
  is-decidable-Π-equiv' = is-decidable-equiv (equiv-Π D e f)
```
