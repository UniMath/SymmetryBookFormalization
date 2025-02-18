# Coproduct types

```agda
module foundation.coproduct-types where

open import foundation-core.coproduct-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.negated-equality
open import foundation.noncontractible-types
open import foundation.subuniverses
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.contractible-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.negation
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.retracts-of-types
```

</details>

### The predicates of being in the left and in the right summand

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  is-left-Prop : X + Y → Prop lzero
  is-left-Prop (inl x) = unit-Prop
  is-left-Prop (inr x) = empty-Prop

  is-left : X + Y → UU lzero
  is-left x = type-Prop (is-left-Prop x)

  is-prop-is-left : (x : X + Y) → is-prop (is-left x)
  is-prop-is-left x = is-prop-type-Prop (is-left-Prop x)

  is-right-Prop : X + Y → Prop lzero
  is-right-Prop (inl x) = empty-Prop
  is-right-Prop (inr x) = unit-Prop

  is-right : X + Y → UU lzero
  is-right x = type-Prop (is-right-Prop x)

  is-prop-is-right : (x : X + Y) → is-prop (is-right x)
  is-prop-is-right x = is-prop-type-Prop (is-right-Prop x)

  is-left-or-is-right : (x : X + Y) → is-left x + is-right x
  is-left-or-is-right (inl x) = inl star
  is-left-or-is-right (inr x) = inr star
```

### The predicate that a subuniverse is closed under coproducts

We formulate a variant with three subuniverses and the more traditional variant
using a single subuniverse

```agda
is-closed-under-coproducts-subuniverses :
  {l1 l2 l3 l4 l5 : Level} (P : subuniverse l1 l2) (Q : subuniverse l3 l4) →
  subuniverse (l1 ⊔ l3) l5 → UU (lsuc l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4 ⊔ l5)
is-closed-under-coproducts-subuniverses {l1} {l2} {l3} P Q R =
  {X : UU l1} {Y : UU l3} →
  is-in-subuniverse P X → is-in-subuniverse Q Y → is-in-subuniverse R (X + Y)

is-closed-under-coproducts-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU (lsuc l1 ⊔ l2)
is-closed-under-coproducts-subuniverse P =
  is-closed-under-coproducts-subuniverses P P P
```

## Properties

### The left and right inclusions are injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-injective-inl : is-injective {B = A + B} inl
  is-injective-inl refl = refl

  is-injective-inr : is-injective {B = A + B} inr
  is-injective-inr refl = refl

  neq-inl-inr : {x : A} {y : B} → inl x ≠ inr y
  neq-inl-inr ()

  neq-inr-inl : {x : B} {y : A} → inr x ≠ inl y
  neq-inr-inl ()
```

### The type of left elements is equivalent to the left summand

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  map-equiv-left-summand : Σ (X + Y) is-left → X
  map-equiv-left-summand (inl x , star) = x
  map-equiv-left-summand (inr x , ())

  map-inv-equiv-left-summand : X → Σ (X + Y) is-left
  pr1 (map-inv-equiv-left-summand x) = inl x
  pr2 (map-inv-equiv-left-summand x) = star

  is-section-map-inv-equiv-left-summand :
    (map-equiv-left-summand ∘ map-inv-equiv-left-summand) ~ id
  is-section-map-inv-equiv-left-summand x = refl

  is-retraction-map-inv-equiv-left-summand :
    (map-inv-equiv-left-summand ∘ map-equiv-left-summand) ~ id
  is-retraction-map-inv-equiv-left-summand (inl x , star) = refl
  is-retraction-map-inv-equiv-left-summand (inr x , ())

  equiv-left-summand : (Σ (X + Y) is-left) ≃ X
  pr1 equiv-left-summand = map-equiv-left-summand
  pr2 equiv-left-summand =
    is-equiv-is-invertible
      map-inv-equiv-left-summand
      is-section-map-inv-equiv-left-summand
      is-retraction-map-inv-equiv-left-summand
```

### The type of right elements is equivalent to the right summand

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  map-equiv-right-summand : Σ (X + Y) is-right → Y
  map-equiv-right-summand (inl x , ())
  map-equiv-right-summand (inr x , star) = x

  map-inv-equiv-right-summand : Y → Σ (X + Y) is-right
  pr1 (map-inv-equiv-right-summand y) = inr y
  pr2 (map-inv-equiv-right-summand y) = star

  is-section-map-inv-equiv-right-summand :
    map-equiv-right-summand ∘ map-inv-equiv-right-summand ~ id
  is-section-map-inv-equiv-right-summand y = refl

  is-retraction-map-inv-equiv-right-summand :
    map-inv-equiv-right-summand ∘ map-equiv-right-summand ~ id
  is-retraction-map-inv-equiv-right-summand (inl x , ())
  is-retraction-map-inv-equiv-right-summand (inr x , star) = refl

  equiv-right-summand : Σ (X + Y) is-right ≃ Y
  pr1 equiv-right-summand = map-equiv-right-summand
  pr2 equiv-right-summand =
    is-equiv-is-invertible
      map-inv-equiv-right-summand
      is-section-map-inv-equiv-right-summand
      is-retraction-map-inv-equiv-right-summand
```

### Coproducts of contractible types are not contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  noncontractibility-coproduct-is-contr' :
    is-contr A → is-contr B → noncontractibility' (A + B) 1
  noncontractibility-coproduct-is-contr' HA HB =
    inl (center HA) , inr (center HB) , neq-inl-inr

  abstract
    is-not-contractible-coproduct-is-contr :
      is-contr A → is-contr B → is-not-contractible (A + B)
    is-not-contractible-coproduct-is-contr HA HB =
      is-not-contractible-noncontractibility
        ( 1 , noncontractibility-coproduct-is-contr' HA HB)
```

### Coproducts of mutually exclusive propositions are propositions

```agda
module _
  {l1 l2 : Level} {P : UU l1} {Q : UU l2}
  where

  abstract
    all-elements-equal-coproduct :
      (P → ¬ Q) → all-elements-equal P → all-elements-equal Q →
      all-elements-equal (P + Q)
    all-elements-equal-coproduct f is-prop-P is-prop-Q (inl p) (inl p') =
      ap inl (is-prop-P p p')
    all-elements-equal-coproduct f is-prop-P is-prop-Q (inl p) (inr q') =
      ex-falso (f p q')
    all-elements-equal-coproduct f is-prop-P is-prop-Q (inr q) (inl p') =
      ex-falso (f p' q)
    all-elements-equal-coproduct f is-prop-P is-prop-Q (inr q) (inr q') =
      ap inr (is-prop-Q q q')

  abstract
    is-prop-coproduct : (P → ¬ Q) → is-prop P → is-prop Q → is-prop (P + Q)
    is-prop-coproduct f is-prop-P is-prop-Q =
      is-prop-all-elements-equal
        ( all-elements-equal-coproduct f
          ( eq-is-prop' is-prop-P)
          ( eq-is-prop' is-prop-Q))

coproduct-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2) →
  (type-Prop P → ¬ (type-Prop Q)) → Prop (l1 ⊔ l2)
pr1 (coproduct-Prop P Q H) =
  type-Prop P + type-Prop Q
pr2 (coproduct-Prop P Q H) =
  is-prop-coproduct H (is-prop-type-Prop P) (is-prop-type-Prop Q)
```

### If a summand has an element, then that summand is a retract of the coproduct

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  retraction-inl : A → retraction (inl {A = A} {B})
  retraction-inl a = (rec-coproduct id (const B a) , refl-htpy)

  retract-left-summand-coproduct : A → A retract-of (A + B)
  retract-left-summand-coproduct a = (inl , retraction-inl a)

  retraction-inr : B → retraction (inr {A = A} {B})
  retraction-inr b = (rec-coproduct (const A b) id , refl-htpy)

  retract-right-summand-coproduct : B → B retract-of (A + B)
  retract-right-summand-coproduct b = (inr , retraction-inr b)
```
