# Double negation sheaves

```agda
module orthogonal-factorization-systems.double-negation-sheaves where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.double-negation-stable-propositions
open import foundation.empty-types
open import foundation.irrefutable-propositions
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.universal-property-coproduct-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions

open import orthogonal-factorization-systems.null-types
```

</details>

## Idea

{{#concept "Double negation sheaves" Agda=is-double-negation-sheaf}} are types
that are [null](orthogonal-factorization-systems.null-types.md) at
[irrefutable propositions](foundation.irrefutable-propositions.md), i.e.,
[propositions](foundation-core.propositions.md) `P` for which the
[double negation](foundation.double-negation.md) `¬¬P` is true.

Double negation sheaves were first introduced in the context of Homotopy Type
Theory in Example 3.41 of {{#cite RSS20}}, and are considered in the restricted
context of [sets](foundation-core.sets.md) in {{#cite Swan24}}.

## Definitions

### The property of being a double negation sheaf

```agda
is-double-negation-sheaf :
  (l1 : Level) {l2 : Level} (A : UU l2) → UU (lsuc l1 ⊔ l2)
is-double-negation-sheaf l1 A =
  (P : Irrefutable-Prop l1) → is-null (type-Irrefutable-Prop P) A

is-prop-is-double-negation-sheaf :
  {l1 l2 : Level} {A : UU l2} → is-prop (is-double-negation-sheaf l1 A)
is-prop-is-double-negation-sheaf {A = A} =
  is-prop-Π (λ P → is-prop-is-null (type-Irrefutable-Prop P) A)
```

## Properties

### The empty type is a double negation sheaf

```agda
is-double-negation-sheaf-empty :
  {l : Level} → is-double-negation-sheaf l empty
is-double-negation-sheaf-empty P =
  is-equiv-has-converse empty-Prop
    ( hom-Prop (prop-Irrefutable-Prop P) empty-Prop)
    ( is-irrefutable-Irrefutable-Prop P)
```

### Contractible types are double negation sheaves

```agda
is-double-negation-sheaf-is-contr :
  {l1 l2 : Level} {A : UU l1} → is-contr A → is-double-negation-sheaf l2 A
is-double-negation-sheaf-is-contr is-contr-A P =
  is-null-is-contr (type-Irrefutable-Prop P) is-contr-A
```

### Propositions that are double negation sheaves are double negation stable

```agda
module _
  {l : Level} {A : UU l}
  (is-prop-A : is-prop A)
  (is-¬¬-sheaf-A : is-double-negation-sheaf l A)
  where

  compute-is-double-negation-sheaf-is-prop : A ≃ (¬ A → A)
  compute-is-double-negation-sheaf-is-prop =
    ( left-unit-law-product-is-contr
      ( is-proof-irrelevant-is-prop (is-prop-function-type is-prop-A) id)) ∘e
    ( equiv-universal-property-coproduct A) ∘e
    ( _ , is-¬¬-sheaf-A (is-decidable-prop-Irrefutable-Prop (A , is-prop-A)))

  is-double-negation-stable-is-double-negation-sheaf-is-prop :
    is-double-negation-stable (A , is-prop-A)
  is-double-negation-stable-is-double-negation-sheaf-is-prop ¬¬a =
    map-inv-is-equiv (is-¬¬-sheaf-A (A , is-prop-A , ¬¬a)) id
```

### Double negation stable propositions are double negation sheaves

This follows from the fact that a proposition `P` is double negation stable if
and only if it is local at all double negations

```text
  (¬¬A → P) → (A → P),
```

and nullification at irrefutable propositions is a restriction of this.

> This remains to be formalized.

### The negation of a type is a double negation sheaf

This is a corollary of the previous result.

> This remains to be formalized.

## References

{{#bibliography}}
