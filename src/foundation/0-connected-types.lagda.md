# `0`-Connected types

```agda
module foundation.0-connected-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.fiber-inclusions
open import foundation.functoriality-set-truncation
open import foundation.images
open import foundation.inhabited-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.set-truncations
open import foundation.sets
open import foundation.surjective-maps
open import foundation.unit-type
open import foundation.universal-property-contractible-types
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.precomposition-functions
open import foundation-core.propositions
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

A type is said to be
{{#concept "0-connected" Disambiguation="type" Agda=is-0-connected}} if its type
of [connected components](foundation.connected-components.md), i.e., its
[set truncation](foundation.set-truncations.md), is
[contractible](foundation-core.contractible-types.md).

```agda
is-0-connected-Prop : {l : Level} → UU l → Prop l
is-0-connected-Prop A = is-contr-Prop (type-trunc-Set A)

is-0-connected : {l : Level} → UU l → UU l
is-0-connected A = type-Prop (is-0-connected-Prop A)

is-prop-is-0-connected : {l : Level} (A : UU l) → is-prop (is-0-connected A)
is-prop-is-0-connected A = is-prop-type-Prop (is-0-connected-Prop A)

abstract
  is-inhabited-is-0-connected :
    {l : Level} {A : UU l} → is-0-connected A → is-inhabited A
  is-inhabited-is-0-connected {l} {A} C =
    apply-universal-property-trunc-Set'
      ( center C)
      ( set-Prop (trunc-Prop A))
      ( unit-trunc-Prop)

abstract
  mere-eq-is-0-connected :
    {l : Level} {A : UU l} → is-0-connected A → all-elements-merely-equal A
  mere-eq-is-0-connected {A = A} H x y =
    apply-effectiveness-unit-trunc-Set (eq-is-contr H)

abstract
  is-0-connected-mere-eq :
    {l : Level} {A : UU l} (a : A) →
    ((x : A) → mere-eq a x) → is-0-connected A
  is-0-connected-mere-eq {l} {A} a e =
    pair
      ( unit-trunc-Set a)
      ( apply-dependent-universal-property-trunc-Set'
        ( λ x → set-Prop (Id-Prop (trunc-Set A) (unit-trunc-Set a) x))
        ( λ x → apply-effectiveness-unit-trunc-Set' (e x)))

abstract
  is-0-connected-mere-eq-is-inhabited :
    {l : Level} {A : UU l} →
    is-inhabited A → all-elements-merely-equal A → is-0-connected A
  is-0-connected-mere-eq-is-inhabited H K =
    apply-universal-property-trunc-Prop H
      ( is-0-connected-Prop _)
      ( λ a → is-0-connected-mere-eq a (K a))

is-0-connected-is-surjective-point :
  {l1 : Level} {A : UU l1} (a : A) →
  is-surjective (point a) → is-0-connected A
is-0-connected-is-surjective-point a H =
  is-0-connected-mere-eq a
    ( λ x →
      apply-universal-property-trunc-Prop
        ( H x)
        ( mere-eq-Prop a x)
        ( λ u → unit-trunc-Prop (pr2 u)))

abstract
  is-surjective-point-is-0-connected :
    {l1 : Level} {A : UU l1} (a : A) →
    is-0-connected A → is-surjective (point a)
  is-surjective-point-is-0-connected a H x =
    apply-universal-property-trunc-Prop
      ( mere-eq-is-0-connected H a x)
      ( trunc-Prop (fiber (point a) x))
      ( λ where refl → unit-trunc-Prop (star , refl))

is-trunc-map-ev-point-is-connected :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (a : A) →
  is-0-connected A → is-trunc (succ-𝕋 k) B →
  is-trunc-map k (ev-point' a {B})
is-trunc-map-ev-point-is-connected k {A} {B} a H K =
  is-trunc-map-comp k
    ( ev-point' star {B})
    ( precomp (point a) B)
    ( is-trunc-map-is-equiv k
      ( universal-property-contr-is-contr star is-contr-unit B))
    ( is-trunc-map-precomp-Π-is-surjective k
      ( is-surjective-point-is-0-connected a H)
      ( λ _ → (B , K)))

equiv-dependent-universal-property-is-0-connected :
  {l1 : Level} {A : UU l1} (a : A) → is-0-connected A →
  ( {l : Level} (P : A → Prop l) →
    ((x : A) → type-Prop (P x)) ≃ type-Prop (P a))
equiv-dependent-universal-property-is-0-connected a H P =
  ( equiv-universal-property-unit (type-Prop (P a))) ∘e
  ( equiv-dependent-universal-property-surjection-is-surjective
    ( point a)
    ( is-surjective-point-is-0-connected a H)
    ( P))

apply-dependent-universal-property-is-0-connected :
  {l1 : Level} {A : UU l1} (a : A) → is-0-connected A →
  {l : Level} (P : A → Prop l) → type-Prop (P a) → (x : A) → type-Prop (P x)
apply-dependent-universal-property-is-0-connected a H P =
  map-inv-equiv (equiv-dependent-universal-property-is-0-connected a H P)

abstract
  is-surjective-fiber-inclusion :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-0-connected A → (a : A) → is-surjective (fiber-inclusion B a)
  is-surjective-fiber-inclusion {B = B} C a (x , b) =
    apply-universal-property-trunc-Prop
      ( mere-eq-is-0-connected C a x)
      ( trunc-Prop (fiber (fiber-inclusion B a) (x , b)))
      ( λ where refl → unit-trunc-Prop (b , refl))

abstract
  mere-eq-is-surjective-fiber-inclusion :
    {l1 : Level} {A : UU l1} (a : A) →
    ({l : Level} (B : A → UU l) → is-surjective (fiber-inclusion B a)) →
    (x : A) → mere-eq a x
  mere-eq-is-surjective-fiber-inclusion a H x =
    apply-universal-property-trunc-Prop
      ( H (λ x → unit) (x , star))
      ( mere-eq-Prop a x)
      ( λ u → unit-trunc-Prop (ap pr1 (pr2 u)))

abstract
  is-0-connected-is-surjective-fiber-inclusion :
    {l1 : Level} {A : UU l1} (a : A) →
    ({l : Level} (B : A → UU l) → is-surjective (fiber-inclusion B a)) →
    is-0-connected A
  is-0-connected-is-surjective-fiber-inclusion a H =
    is-0-connected-mere-eq a (mere-eq-is-surjective-fiber-inclusion a H)

is-0-connected-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → is-0-connected B → is-0-connected A
is-0-connected-equiv e = is-contr-equiv _ (equiv-trunc-Set e)

is-0-connected-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A ≃ B) → is-0-connected A → is-0-connected B
is-0-connected-equiv' e = is-0-connected-equiv (inv-equiv e)
```

### `0`-connected types are closed under cartesian products

```agda
module _
  {l1 l2 : Level} (X : UU l1) (Y : UU l2)
  (p1 : is-0-connected X) (p2 : is-0-connected Y)
  where

  is-0-connected-product : is-0-connected (X × Y)
  is-0-connected-product =
    is-contr-equiv
      ( type-trunc-Set X × type-trunc-Set Y)
      ( equiv-distributive-trunc-product-Set X Y)
      ( is-contr-product p1 p2)
```

### The unit type is `0`-connected

```agda
abstract
  is-0-connected-unit : is-0-connected unit
  is-0-connected-unit =
    is-contr-equiv' unit equiv-unit-trunc-unit-Set is-contr-unit
```

### A contractible type is `0`-connected

```agda
is-0-connected-is-contr :
  {l : Level} (X : UU l) →
  is-contr X → is-0-connected X
is-0-connected-is-contr X p =
  is-contr-equiv X (inv-equiv (equiv-unit-trunc-Set (X , is-set-is-contr p))) p
```

### The image of a function with a `0`-connected domain is `0`-connected

```agda
abstract
  is-0-connected-im-is-0-connected-domain :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-0-connected A → is-0-connected (im f)
  is-0-connected-im-is-0-connected-domain {A = A} {B} f C =
    apply-universal-property-trunc-Prop
      ( is-inhabited-is-0-connected C)
      ( is-contr-Prop _)
      ( λ a →
        is-contr-equiv'
          ( im (map-trunc-Set f))
          ( equiv-trunc-im-Set f)
          ( is-contr-im
            ( trunc-Set B)
            ( unit-trunc-Set a)
            ( apply-dependent-universal-property-trunc-Set'
              ( λ x →
                set-Prop
                  ( Id-Prop
                    ( trunc-Set B)
                    ( map-trunc-Set f x)
                    ( map-trunc-Set f (unit-trunc-Set a))))
              ( λ a' →
                apply-universal-property-trunc-Prop
                  ( mere-eq-is-0-connected C a' a)
                  ( Id-Prop
                    ( trunc-Set B)
                    ( map-trunc-Set f (unit-trunc-Set a'))
                    ( map-trunc-Set f (unit-trunc-Set a)))
                  ( λ where refl → refl)))))

abstract
  is-0-connected-im-point' :
    {l1 : Level} {A : UU l1} (f : unit → A) → is-0-connected (im f)
  is-0-connected-im-point' f =
    is-0-connected-im-is-0-connected-domain f is-0-connected-unit
```
