# Propositionally decidable types

```agda
module logic.propositionally-decidable-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coinhabited-pairs-of-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.equivalences
open import foundation.functoriality-coproduct-types
open import foundation.hilberts-epsilon-operators
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.retracts-of-types
open import foundation.type-arithmetic-empty-type
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.decidable-propositions
open import foundation-core.function-types
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

A type is said to be
{{#concept "propositionally decidable" Disambiguation="type" Agda=is-inhabited-or-empty}}
if we can either deduce that it is [inhabited](foundation.inhabited-types.md),
or we can deduce that it is [empty](foundation-core.empty-types.md), where
inhabitedness of a type is expressed using the
[propositional truncation](foundation.propositional-truncations.md).

## Definitions

### The predicate that a type is inhabited or empty

```agda
is-inhabited-or-empty : {l1 : Level} → UU l1 → UU l1
is-inhabited-or-empty A = type-trunc-Prop A + is-empty A
```

### Merely decidable types

A type `A` is said to be
{{#concept "merely decidable" Agda=is-merely-decidable}} if it comes equipped
with an element of `║ is-decidable A ║₋₁`, or equivalently, the
[disjunction](foundation.disjunction.md) `A ∨ ¬ A` holds.

```agda
is-merely-decidable-Prop :
  {l : Level} → UU l → Prop l
is-merely-decidable-Prop A = trunc-Prop (is-decidable A)

is-merely-decidable : {l : Level} → UU l → UU l
is-merely-decidable A = type-trunc-Prop (is-decidable A)
```

## Properties

### Decidable types are inhabited or empty

```agda
is-inhabited-or-empty-is-decidable :
  {l : Level} {A : UU l} → is-decidable A → is-inhabited-or-empty A
is-inhabited-or-empty-is-decidable (inl x) = inl (unit-trunc-Prop x)
is-inhabited-or-empty-is-decidable (inr y) = inr y
```

### Decidable types are merely decidable

```agda
is-merely-decidable-is-decidable :
  {l : Level} {A : UU l} → is-decidable A → is-merely-decidable A
is-merely-decidable-is-decidable = unit-trunc-Prop
```

### Being inhabited or empty is a proposition

```agda
abstract
  is-property-is-inhabited-or-empty :
    {l1 : Level} (A : UU l1) → is-prop (is-inhabited-or-empty A)
  is-property-is-inhabited-or-empty A =
    is-prop-coproduct
      ( λ t → apply-universal-property-trunc-Prop t empty-Prop)
      ( is-prop-type-trunc-Prop)
      ( is-prop-neg)

is-inhabited-or-empty-Prop : {l1 : Level} → UU l1 → Prop l1
pr1 (is-inhabited-or-empty-Prop A) = is-inhabited-or-empty A
pr2 (is-inhabited-or-empty-Prop A) = is-property-is-inhabited-or-empty A
```

### Types are inhabited or empty if and only if they are merely decidable

```agda
module _
  {l : Level} {A : UU l}
  where

  is-inhabited-or-empty-is-merely-decidable :
    is-merely-decidable A → is-inhabited-or-empty A
  is-inhabited-or-empty-is-merely-decidable =
    rec-trunc-Prop
      ( is-inhabited-or-empty-Prop A)
      ( is-inhabited-or-empty-is-decidable)

  is-merely-decidable-is-inhabited-or-empty :
    is-inhabited-or-empty A → is-merely-decidable A
  is-merely-decidable-is-inhabited-or-empty (inl |x|) =
    rec-trunc-Prop (is-merely-decidable-Prop A) (unit-trunc-Prop ∘ inl) |x|
  is-merely-decidable-is-inhabited-or-empty (inr y) =
    unit-trunc-Prop (inr y)

  iff-is-inhabited-or-empty-is-merely-decidable :
    is-merely-decidable A ↔ is-inhabited-or-empty A
  iff-is-inhabited-or-empty-is-merely-decidable =
    ( is-inhabited-or-empty-is-merely-decidable ,
      is-merely-decidable-is-inhabited-or-empty)
```

### Propositionally decidable types are closed under coinhabited types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-inhabited-or-empty-is-coinhabited :
    is-coinhabited A B → is-inhabited-or-empty A → is-inhabited-or-empty B
  is-inhabited-or-empty-is-coinhabited (f , b) =
    map-coproduct
      ( f)
      ( is-empty-type-trunc-Prop' ∘ map-neg b ∘ is-empty-type-trunc-Prop)
```

### Propositionally decidable types are closed under logical equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-inhabited-or-empty-iff :
    (A → B) → (B → A) → is-inhabited-or-empty A → is-inhabited-or-empty B
  is-inhabited-or-empty-iff f g (inl |a|) =
    inl (rec-trunc-Prop (trunc-Prop B) (unit-trunc-Prop ∘ f) |a|)
  is-inhabited-or-empty-iff f g (inr na) = inr (na ∘ g)

  is-inhabited-or-empty-iff' :
    A ↔ B → is-inhabited-or-empty A → is-inhabited-or-empty B
  is-inhabited-or-empty-iff' (f , g) = is-inhabited-or-empty-iff f g

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  iff-is-inhabited-or-empty :
    A ↔ B → is-inhabited-or-empty A ↔ is-inhabited-or-empty B
  iff-is-inhabited-or-empty e =
    is-inhabited-or-empty-iff' e , is-inhabited-or-empty-iff' (inv-iff e)
```

### Propositionally decidable types are closed under retracts

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-inhabited-or-empty-retract-of :
    A retract-of B → is-inhabited-or-empty B → is-inhabited-or-empty A
  is-inhabited-or-empty-retract-of R =
    is-inhabited-or-empty-iff' (iff-retract' R)

  is-inhabited-or-empty-retract-of' :
    A retract-of B → is-inhabited-or-empty A → is-inhabited-or-empty B
  is-inhabited-or-empty-retract-of' R =
    is-inhabited-or-empty-iff' (inv-iff (iff-retract' R))
```

### Propositionally decidable types are closed under equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-inhabited-or-empty-is-equiv :
    {f : A → B} → is-equiv f → is-inhabited-or-empty B → is-inhabited-or-empty A
  is-inhabited-or-empty-is-equiv {f} H =
    is-inhabited-or-empty-retract-of (retract-equiv (f , H))

  is-inhabited-or-empty-equiv :
    A ≃ B → is-inhabited-or-empty B → is-inhabited-or-empty A
  is-inhabited-or-empty-equiv e =
    is-inhabited-or-empty-iff (map-inv-equiv e) (map-equiv e)

  is-inhabited-or-empty-equiv' :
    A ≃ B → is-inhabited-or-empty A → is-inhabited-or-empty B
  is-inhabited-or-empty-equiv' e =
    is-inhabited-or-empty-iff (map-equiv e) (map-inv-equiv e)
```

### Elimination for propositional decidability

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Prop l2)
  where

  elim-is-inhabited-or-empty-Prop :
    (A → type-Prop B) → (¬ A → type-Prop B) →
    is-inhabited-or-empty A → type-Prop B
  elim-is-inhabited-or-empty-Prop b nb (inl |a|) = rec-trunc-Prop B b |a|
  elim-is-inhabited-or-empty-Prop b nb (inr na) = nb na

  elim-is-inhabited-or-empty-Prop' :
    (is-decidable A → type-Prop B) → is-inhabited-or-empty A → type-Prop B
  elim-is-inhabited-or-empty-Prop' f =
    elim-is-inhabited-or-empty-Prop (f ∘ inl) (f ∘ inr)
```

### Coproducts of propositionally decidable types are propositionally decidable

```agda
is-inhabited-or-empty-coproduct :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-inhabited-or-empty A →
  is-inhabited-or-empty B →
  is-inhabited-or-empty (A + B)
is-inhabited-or-empty-coproduct (inl a) dB =
  rec-trunc-Prop (is-inhabited-or-empty-Prop _) (inl ∘ unit-trunc-Prop ∘ inl) a
is-inhabited-or-empty-coproduct (inr na) (inl b) =
  rec-trunc-Prop (is-inhabited-or-empty-Prop _) (inl ∘ unit-trunc-Prop ∘ inr) b
is-inhabited-or-empty-coproduct (inr na) (inr nb) = inr (rec-coproduct na nb)
```

### Cartesian products of propositionally decidable types are propositionally decidable

```agda
is-inhabited-or-empty-product :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-inhabited-or-empty A →
  is-inhabited-or-empty B →
  is-inhabited-or-empty (A × B)
is-inhabited-or-empty-product (inl a) (inl b) =
  inl (map-inv-distributive-trunc-product-Prop (a , b))
is-inhabited-or-empty-product (inl a) (inr nb) = inr (nb ∘ pr2)
is-inhabited-or-empty-product (inr na) dB = inr (na ∘ pr1)

is-inhabited-or-empty-product' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-inhabited-or-empty A → (A → is-inhabited-or-empty B) →
  is-inhabited-or-empty (A × B)
is-inhabited-or-empty-product' (inl a) dB =
  rec-trunc-Prop
    ( is-inhabited-or-empty-Prop _)
    ( rec-coproduct
      ( λ b → inl (map-inv-distributive-trunc-product-Prop (a , b)))
      ( λ nb → inr (nb ∘ pr2)) ∘
      dB)
    ( a)
is-inhabited-or-empty-product' (inr na) dB = inr (na ∘ pr1)

is-inhabited-or-empty-left-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-inhabited-or-empty (A × B) → B → is-inhabited-or-empty A
is-inhabited-or-empty-left-factor (inl x) b =
  inl (pr1 (map-distributive-trunc-product-Prop x))
is-inhabited-or-empty-left-factor (inr nx) b = inr (λ a → nx (a , b))

is-inhabited-or-empty-right-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-inhabited-or-empty (A × B) → A → is-inhabited-or-empty B
is-inhabited-or-empty-right-factor (inl x) a =
  inl (pr2 (map-distributive-trunc-product-Prop x))
is-inhabited-or-empty-right-factor (inr nx) a = inr (λ b → nx (a , b))
```

### Function types of propositionally decidable types are propositionally decidable

```agda
is-inhabited-or-empty-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-inhabited-or-empty A →
  is-inhabited-or-empty B →
  is-inhabited-or-empty (A → B)
is-inhabited-or-empty-function-type (inl a) (inl b) =
  inl (rec-trunc-Prop (trunc-Prop _) (λ y → unit-trunc-Prop (λ _ → y)) b)
is-inhabited-or-empty-function-type (inl a) (inr nb) =
  inr (λ f → rec-trunc-Prop empty-Prop (λ x → nb (f x)) a)
is-inhabited-or-empty-function-type (inr na) dB =
  inl (unit-trunc-Prop (ex-falso ∘ na))

is-inhabited-or-empty-function-type' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-inhabited-or-empty A → (A → is-inhabited-or-empty B) →
  is-inhabited-or-empty (A → B)
is-inhabited-or-empty-function-type' (inl a) dB =
  rec-trunc-Prop (is-inhabited-or-empty-Prop _)
    ( λ x →
      rec-coproduct
        ( inl ∘ rec-trunc-Prop (trunc-Prop _) (λ y → unit-trunc-Prop (λ _ → y)))
        ( λ nb → inr (λ f → nb (f x)))
        ( dB x))
    ( a)
is-inhabited-or-empty-function-type' (inr na) dB =
  inl (unit-trunc-Prop (ex-falso ∘ na))
```

### Decidability of a propositional truncation

```agda
abstract
  is-prop-is-decidable-trunc-Prop :
    {l : Level} (A : UU l) → is-prop (is-decidable (type-trunc-Prop A))
  is-prop-is-decidable-trunc-Prop A =
    is-prop-is-decidable is-prop-type-trunc-Prop

is-decidable-trunc-Prop : {l : Level} → UU l → Prop l
pr1 (is-decidable-trunc-Prop A) = is-decidable (type-trunc-Prop A)
pr2 (is-decidable-trunc-Prop A) = is-prop-is-decidable-trunc-Prop A

is-decidable-trunc-Prop-is-decidable :
  {l : Level} {A : UU l} →
  is-decidable A → type-Prop (is-decidable-trunc-Prop A)
is-decidable-trunc-Prop-is-decidable (inl a) =
  inl (unit-trunc-Prop a)
is-decidable-trunc-Prop-is-decidable (inr f) =
  inr (map-universal-property-trunc-Prop empty-Prop f)

is-decidable-trunc-Prop-is-merely-decidable :
  {l : Level} {A : UU l} →
  is-merely-decidable A → is-decidable (type-trunc-Prop A)
is-decidable-trunc-Prop-is-merely-decidable {A = A} =
  map-universal-property-trunc-Prop
    ( is-decidable-trunc-Prop A)
    ( is-decidable-trunc-Prop-is-decidable)

is-merely-decidable-is-decidable-trunc-Prop :
  {l : Level} (A : UU l) →
  is-decidable (type-trunc-Prop A) → is-merely-decidable A
is-merely-decidable-is-decidable-trunc-Prop A (inl x) =
  apply-universal-property-trunc-Prop x
    ( is-merely-decidable-Prop A)
    ( unit-trunc-Prop ∘ inl)
is-merely-decidable-is-decidable-trunc-Prop A (inr f) =
  unit-trunc-Prop (inr (f ∘ unit-trunc-Prop))
```

## See also

- That decidablity is irrefutable is shown in
  [`foundation.irrefutable-propositions`](foundation.irrefutable-propositions.md).
