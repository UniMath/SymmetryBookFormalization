# Uniformly decidable type families

```agda
module foundation.uniformly-decidable-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-type-families
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.equality-coproduct-types
open import foundation.functoriality-coproduct-types
open import foundation.inhabited-types
open import foundation.irrefutable-equality
open import foundation.mere-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-empty-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-maps
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types

open import logic.propositionally-decidable-types
```

</details>

## Idea

A type family `B : A → 𝒰` is
{{#concept "uniformly decidable" Agda=is-uniformly-decidable-family}} if there
either is an element of every fiber `B x`, or every fiber is
[empty](foundation-core.empty-types.md).

## Definitions

### The predicate of being uniformly decidable

```agda
is-uniformly-decidable-family :
  {l1 l2 : Level} {A : UU l1} → (A → UU l2) → UU (l1 ⊔ l2)
is-uniformly-decidable-family {A = A} B =
  ((x : A) → B x) + ((x : A) → ¬ (B x))
```

## Properties

### The fibers of a uniformly decidable type family are decidable

```agda
is-decidable-is-uniformly-decidable-family :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-uniformly-decidable-family B →
  (x : A) → is-decidable (B x)
is-decidable-is-uniformly-decidable-family (inl f) x = inl (f x)
is-decidable-is-uniformly-decidable-family (inr g) x = inr (g x)
```

### The uniform decidability predicate on a family of contractible types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-contr-is-uniformly-decidable-family-is-inhabited-base'' :
    is-contr ((x : A) → (B x)) →
    A →
    is-contr (is-uniformly-decidable-family B)
  is-contr-is-uniformly-decidable-family-is-inhabited-base'' H a =
    is-contr-equiv
      ( (x : A) → B x)
      ( right-unit-law-coproduct-is-empty
        ( (x : A) → B x)
        ( (x : A) → ¬ B x)
        ( λ f → f a (center H a)))
      ( H)

  is-contr-is-uniformly-decidable-family-is-inhabited-base' :
    ((x : A) → is-contr (B x)) →
    A →
    is-contr (is-uniformly-decidable-family B)
  is-contr-is-uniformly-decidable-family-is-inhabited-base' H =
    is-contr-is-uniformly-decidable-family-is-inhabited-base'' (is-contr-Π H)

  is-contr-is-uniformly-decidable-family-is-inhabited-base :
    ((x : A) → is-contr (B x)) →
    is-inhabited A →
    is-contr (is-uniformly-decidable-family B)
  is-contr-is-uniformly-decidable-family-is-inhabited-base H =
    rec-trunc-Prop
      ( is-contr-Prop (is-uniformly-decidable-family B))
      ( is-contr-is-uniformly-decidable-family-is-inhabited-base' H)
```

### The uniform decidability predicate on a family of propositions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-prop-is-uniformly-decidable-family-is-inhabited-base'' :
    is-prop ((x : A) → (B x)) →
    A →
    is-prop (is-uniformly-decidable-family B)
  is-prop-is-uniformly-decidable-family-is-inhabited-base'' H a =
    is-prop-coproduct
      ( λ f nf → nf a (f a))
      ( H)
      ( is-prop-Π (λ x → is-prop-neg))

  is-prop-is-uniformly-decidable-family-is-inhabited-base' :
    ((x : A) → is-prop (B x)) →
    A →
    is-prop (is-uniformly-decidable-family B)
  is-prop-is-uniformly-decidable-family-is-inhabited-base' H =
    is-prop-is-uniformly-decidable-family-is-inhabited-base'' (is-prop-Π H)

  is-prop-is-uniformly-decidable-family-is-inhabited-base :
    ((x : A) → is-prop (B x)) →
    is-inhabited A →
    is-prop (is-uniformly-decidable-family B)
  is-prop-is-uniformly-decidable-family-is-inhabited-base H =
    rec-trunc-Prop
      ( is-prop-Prop (is-uniformly-decidable-family B))
      ( is-prop-is-uniformly-decidable-family-is-inhabited-base' H)

is-uniformly-decidable-family-Prop :
  {l1 l2 : Level}
  (A : Inhabited-Type l1) (B : subtype l2 (type-Inhabited-Type A)) →
  Prop (l1 ⊔ l2)
is-uniformly-decidable-family-Prop (A , |a|) B =
  ( is-uniformly-decidable-family (is-in-subtype B)) ,
  ( is-prop-is-uniformly-decidable-family-is-inhabited-base
    ( is-prop-is-in-subtype B)
    ( |a|))
```

### The uniform decidability predicate on a family of truncated types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-trunc-succ-succ-is-uniformly-decidable-family' :
    (k : 𝕋) →
    is-trunc (succ-𝕋 (succ-𝕋 k)) ((x : A) → (B x)) →
    is-trunc (succ-𝕋 (succ-𝕋 k)) (is-uniformly-decidable-family B)
  is-trunc-succ-succ-is-uniformly-decidable-family' k H =
    is-trunc-coproduct k
      ( H)
      ( is-trunc-is-prop (succ-𝕋 k) (is-prop-Π (λ x → is-prop-neg)))

  is-trunc-succ-succ-is-uniformly-decidable-family :
    (k : 𝕋) →
    ((x : A) → is-trunc (succ-𝕋 (succ-𝕋 k)) (B x)) →
    is-trunc (succ-𝕋 (succ-𝕋 k)) (is-uniformly-decidable-family B)
  is-trunc-succ-succ-is-uniformly-decidable-family k H =
    is-trunc-succ-succ-is-uniformly-decidable-family' k
      ( is-trunc-Π (succ-𝕋 (succ-𝕋 k)) H)

  is-trunc-is-uniformly-decidable-family-is-inhabited-base :
    (k : 𝕋) →
    ((x : A) → is-trunc k (B x)) →
    is-inhabited A →
    is-trunc k (is-uniformly-decidable-family B)
  is-trunc-is-uniformly-decidable-family-is-inhabited-base
    neg-two-𝕋 =
    is-contr-is-uniformly-decidable-family-is-inhabited-base
  is-trunc-is-uniformly-decidable-family-is-inhabited-base
    ( succ-𝕋 neg-two-𝕋) =
    is-prop-is-uniformly-decidable-family-is-inhabited-base
  is-trunc-is-uniformly-decidable-family-is-inhabited-base
    ( succ-𝕋 (succ-𝕋 k)) H _ =
    is-trunc-succ-succ-is-uniformly-decidable-family k H
```

### A family of decidable propositions over a irrefutably π₀-trivial decidable base are uniformly decidable

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (H : all-elements-irrefutably-equal A)
  (dB : is-decidable-family B)
  where

  abstract
    is-uniformly-decidable-family-all-elements-irrefutably-equal-base :
      is-decidable A →
      is-uniformly-decidable-family B
    is-uniformly-decidable-family-all-elements-irrefutably-equal-base (inl a) =
      map-coproduct
        ( λ b x →
          double-negation-elim-is-decidable
            ( dB x)
            ( λ nb → H a x (λ p → nb (tr B p b))))
        ( λ nb x b → H x a (λ p → nb (tr B p b)))
        ( dB a)
    is-uniformly-decidable-family-all-elements-irrefutably-equal-base (inr na) =
      inr (ex-falso ∘ na)

  abstract
    is-uniformly-decidable-family-all-elements-irrefutably-equal-base' :
      is-inhabited-or-empty A →
      ((x : A) → is-prop (B x)) →
      is-uniformly-decidable-family B
    is-uniformly-decidable-family-all-elements-irrefutably-equal-base'
      ( inl |a|) K =
      rec-trunc-Prop
        ( is-uniformly-decidable-family-Prop (A , |a|) (λ x → (B x , K x)))
        ( is-uniformly-decidable-family-all-elements-irrefutably-equal-base ∘
          inl)
        ( |a|)
    is-uniformly-decidable-family-all-elements-irrefutably-equal-base'
      ( inr na) K =
      is-uniformly-decidable-family-all-elements-irrefutably-equal-base (inr na)
```

### A family of decidable propositions over a π₀-trivial decidable base are uniformly decidable

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (H : all-elements-merely-equal A)
  (dB : is-decidable-family B)
  where

  abstract
    is-uniformly-decidable-family-all-elements-merely-equal-base :
      is-decidable A →
      is-uniformly-decidable-family B
    is-uniformly-decidable-family-all-elements-merely-equal-base =
      is-uniformly-decidable-family-all-elements-irrefutably-equal-base
        ( all-elements-irrefutably-equal-all-elements-merely-equal H)
        ( dB)

  abstract
    is-uniformly-decidable-family-all-elements-merely-equal-base' :
      is-inhabited-or-empty A →
      ((x : A) → is-prop (B x)) →
      is-uniformly-decidable-family B
    is-uniformly-decidable-family-all-elements-merely-equal-base' =
      is-uniformly-decidable-family-all-elements-irrefutably-equal-base'
        ( all-elements-irrefutably-equal-all-elements-merely-equal H)
        ( dB)
```
