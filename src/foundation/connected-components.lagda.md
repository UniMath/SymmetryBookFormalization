# Connected components of types

```agda
module foundation.connected-components where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.equality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.subtypes
open import foundation-core.truncated-types
open import foundation-core.truncation-levels

open import higher-group-theory.higher-groups

open import structured-types.pointed-types
```

</details>

## Idea

The
{{#concept "connected component" Disambiguation="of a type" WD="connected component" WDID=Q91050456 Agda=connected-component}}
of a type `A` at an element `a : A` is the type of all `x : A` that are
[merely equal](foundation.mere-equality.md) to `a`.

The [subtype](foundation-core.subtypes.md) of elements merely equal to `a` is
also the least subtype of `A` containing `a`. In other words, if a subtype
satisfies the universal property of being the least subtype of `A` containing
`a`, then its underlying type is the connected component of `A` at `a`.

## Definitions

### The predicate of being the least subtype containing a given element

```agda
module _
  {l1 l2 : Level} {X : UU l1} (x : X) (P : subtype l2 X)
  where

  is-least-subtype-containing-element : UUω
  is-least-subtype-containing-element =
    {l : Level} (Q : subtype l X) → (P ⊆ Q) ↔ is-in-subtype Q x
```

### Connected components of types

```agda
module _
  {l : Level} (A : UU l) (a : A)
  where

  connected-component : UU l
  connected-component = Σ A (λ x → mere-eq x a)

  point-connected-component : connected-component
  pr1 point-connected-component = a
  pr2 point-connected-component = unit-trunc-Prop refl

  connected-component-pointed-type : Pointed-Type l
  pr1 connected-component-pointed-type = connected-component
  pr2 connected-component-pointed-type = point-connected-component

  value-connected-component : connected-component → A
  value-connected-component X = pr1 X

  abstract
    mere-equality-connected-component :
      (X : connected-component) → mere-eq (value-connected-component X) a
    mere-equality-connected-component X = pr2 X
```

## Properties

### Connected components are 0-connected

```agda
abstract
  is-0-connected-connected-component :
    {l : Level} (A : UU l) (a : A) →
    is-0-connected (connected-component A a)
  is-0-connected-connected-component A a =
    is-0-connected-mere-eq
      ( a , refl-mere-eq a)
      ( λ (x , p) →
        apply-universal-property-trunc-Prop
          ( p)
          ( mere-eq-Prop (a , refl-mere-eq a) (x , p))
          ( λ p' →
            mere-eq-eq
              ( eq-pair-Σ
                ( inv p')
                ( all-elements-equal-type-trunc-Prop _ p))))

connected-component-∞-Group :
  {l : Level} (A : UU l) (a : A) → ∞-Group l
pr1 (connected-component-∞-Group A a) = connected-component-pointed-type A a
pr2 (connected-component-∞-Group A a) = is-0-connected-connected-component A a
```

### If `A` is `k+1`-truncated, then the connected component of `a` in `A` is `k+1`-truncated

```agda
is-trunc-connected-component :
  {l : Level} {k : 𝕋} (A : UU l) (a : A) →
  is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) (connected-component A a)
is-trunc-connected-component {l} {k} A a H =
  is-trunc-Σ H (λ x → is-trunc-is-prop k (is-prop-mere-eq x a))
```
