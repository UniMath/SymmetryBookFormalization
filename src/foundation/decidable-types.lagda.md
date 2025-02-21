# Decidable types

```agda
module foundation.decidable-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.equivalences
open import foundation.evaluation-functions
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
open import foundation-core.function-types
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

A type is said to be
{{#concept "decidable" Disambiguation="type" Agda=is-decidable}} if we can
either construct an element, or we can prove that it is
[empty](foundation-core.empty-types.md). In other words, we interpret
decidability via the
[Curry–Howard interpretation](https://en.wikipedia.org/wiki/Curry–Howard_correspondence)
of logic into type theory. A related concept is that a type is either
[inhabited](foundation.inhabited-types.md) or empty, where inhabitedness of a
type is expressed using the
[propositional truncation](foundation.propositional-truncations.md).

## Definitions

### The Curry–Howard interpretation of decidability

```agda
is-decidable : {l : Level} (A : UU l) → UU l
is-decidable A = A + (¬ A)
```

## Examples

### The unit type and the empty type are decidable

```agda
is-decidable-unit : is-decidable unit
is-decidable-unit = inl star

is-decidable-empty : is-decidable empty
is-decidable-empty = inr id
```

## Properties

### Coproducts of decidable types are decidable

```agda
is-decidable-coproduct :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (A + B)
is-decidable-coproduct (inl a) y = inl (inl a)
is-decidable-coproduct (inr na) (inl b) = inl (inr b)
is-decidable-coproduct (inr na) (inr nb) = inr (rec-coproduct na nb)
```

### Cartesian products of decidable types are decidable

```agda
is-decidable-product :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (A × B)
is-decidable-product (inl a) (inl b) = inl (a , b)
is-decidable-product (inl a) (inr g) = inr (g ∘ pr2)
is-decidable-product (inr f) (inl b) = inr (f ∘ pr1)
is-decidable-product (inr f) (inr g) = inr (f ∘ pr1)

is-decidable-product' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → (A → is-decidable B) → is-decidable (A × B)
is-decidable-product' (inl a) d =
  rec-coproduct (λ b → inl (a , b)) (λ nb → inr (nb ∘ pr2)) (d a)
is-decidable-product' (inr na) d = inr (na ∘ pr1)

is-decidable-left-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable (A × B) → B → is-decidable A
is-decidable-left-factor (inl (x , y)) b = inl x
is-decidable-left-factor (inr f) b = inr (λ a → f (a , b))

is-decidable-right-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable (A × B) → A → is-decidable B
is-decidable-right-factor (inl (x , y)) a = inl y
is-decidable-right-factor (inr f) a = inr (λ b → f (a , b))
```

### Function types of decidable types are decidable

```agda
is-decidable-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → is-decidable B → is-decidable (A → B)
is-decidable-function-type (inl a) (inl b) = inl (λ _ → b)
is-decidable-function-type (inl a) (inr nb) = inr (map-neg (ev a) nb)
is-decidable-function-type (inr f) _ = inl (ex-falso ∘ f)

is-decidable-function-type' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-decidable A → (A → is-decidable B) → is-decidable (A → B)
is-decidable-function-type' (inl a) d =
  rec-coproduct (λ b → inl (λ _ → b)) (λ nb → inr (map-neg (ev a) nb)) (d a)
is-decidable-function-type' (inr na) d = inl (ex-falso ∘ na)
```

### The negation of a decidable type is decidable

```agda
is-decidable-neg :
  {l : Level} {A : UU l} → is-decidable A → is-decidable (¬ A)
is-decidable-neg d = is-decidable-function-type d is-decidable-empty
```

### The double negation of a decidable type is decidable

```agda
is-decidable-double-negation :
  {l : Level} {A : UU l} → is-decidable A → is-decidable (¬¬ A)
is-decidable-double-negation d = is-decidable-neg (is-decidable-neg d)
```

### Decidable types are closed under coinhabited types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-iff :
    (A → B) → (B → A) → is-decidable A → is-decidable B
  is-decidable-iff f g (inl a) = inl (f a)
  is-decidable-iff f g (inr na) = inr (na ∘ g)

  is-decidable-iff' :
    A ↔ B → is-decidable A → is-decidable B
  is-decidable-iff' (f , g) = is-decidable-iff f g

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  iff-is-decidable : A ↔ B → is-decidable A ↔ is-decidable B
  iff-is-decidable e = is-decidable-iff' e , is-decidable-iff' (inv-iff e)
```

### Decidable types are closed under retracts

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-retract-of :
    A retract-of B → is-decidable B → is-decidable A
  is-decidable-retract-of R = is-decidable-iff' (iff-retract' R)

  is-decidable-retract-of' :
    A retract-of B → is-decidable A → is-decidable B
  is-decidable-retract-of' R = is-decidable-iff' (inv-iff (iff-retract' R))
```

### Decidable types are closed under equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-is-equiv :
    {f : A → B} → is-equiv f → is-decidable B → is-decidable A
  is-decidable-is-equiv {f} H =
    is-decidable-retract-of (retract-equiv (f , H))

  is-decidable-equiv :
    A ≃ B → is-decidable B → is-decidable A
  is-decidable-equiv e = is-decidable-iff (map-inv-equiv e) (map-equiv e)

  is-decidable-equiv' :
    A ≃ B → is-decidable A → is-decidable B
  is-decidable-equiv' e = is-decidable-iff (map-equiv e) (map-inv-equiv e)
```

### Equivalent types have equivalent decidability predicates

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  map-equiv-is-decidable : is-decidable A → is-decidable B
  map-equiv-is-decidable = is-decidable-equiv' e

  map-inv-equiv-is-decidable : is-decidable B → is-decidable A
  map-inv-equiv-is-decidable = is-decidable-equiv e

  is-section-map-inv-equiv-is-decidable :
    is-section map-equiv-is-decidable map-inv-equiv-is-decidable
  is-section-map-inv-equiv-is-decidable (inl x) =
    ap inl (is-section-map-inv-equiv e x)
  is-section-map-inv-equiv-is-decidable (inr x) =
    ap inr eq-neg

  is-retraction-map-inv-equiv-is-decidable :
    is-retraction map-equiv-is-decidable map-inv-equiv-is-decidable
  is-retraction-map-inv-equiv-is-decidable (inl x) =
    ap inl (is-retraction-map-inv-equiv e x)
  is-retraction-map-inv-equiv-is-decidable (inr x) =
    ap inr eq-neg

  is-equiv-map-equiv-is-decidable : is-equiv map-equiv-is-decidable
  is-equiv-map-equiv-is-decidable =
    is-equiv-is-invertible
      map-inv-equiv-is-decidable
      is-section-map-inv-equiv-is-decidable
      is-retraction-map-inv-equiv-is-decidable

  equiv-is-decidable : is-decidable A ≃ is-decidable B
  equiv-is-decidable = map-equiv-is-decidable , is-equiv-map-equiv-is-decidable
```

### Decidability implies double negation elimination

```agda
double-negation-elim-is-decidable :
  {l : Level} {P : UU l} → is-decidable P → (¬¬ P → P)
double-negation-elim-is-decidable (inl x) p = x
double-negation-elim-is-decidable (inr x) p = ex-falso (p x)
```

See also
[double negation stable propositions](foundation.double-negation-stable-propositions.md).

### Decidable types have ε-operators

```agda
elim-trunc-Prop-is-decidable :
  {l : Level} {A : UU l} → is-decidable A → ε-operator-Hilbert A
elim-trunc-Prop-is-decidable (inl a) x = a
elim-trunc-Prop-is-decidable (inr f) x =
  ex-falso (apply-universal-property-trunc-Prop x empty-Prop f)
```

### `is-decidable` is an idempotent operation

```agda
module _
  {l : Level} {P : UU l}
  where

  map-idempotent-is-decidable : is-decidable P → is-decidable (is-decidable P)
  map-idempotent-is-decidable = inl

  map-inv-idempotent-is-decidable :
    is-decidable (is-decidable P) → is-decidable P
  map-inv-idempotent-is-decidable (inl (inl p)) = inl p
  map-inv-idempotent-is-decidable (inl (inr np)) = inr np
  map-inv-idempotent-is-decidable (inr np) = inr (λ p → np (inl p))
```

### Any inhabited type is a fixed point for `is-decidable`

```agda
is-fixed-point-is-decidable-is-inhabited :
  {l : Level} {X : UU l} → type-trunc-Prop X → is-decidable X ≃ X
is-fixed-point-is-decidable-is-inhabited {l} {X} t =
  right-unit-law-coproduct-is-empty X (¬ X) (is-nonempty-is-inhabited t)
```

### Raising universe level conserves decidability

```agda
module _
  (l : Level) {l1 : Level} (A : UU l1)
  where

  is-decidable-raise : is-decidable A → is-decidable (raise l A)
  is-decidable-raise = is-decidable-equiv' (compute-raise l A)
```

## See also

- That decidablity is irrefutable is shown in
  [`foundation.irrefutable-propositions`](foundation.irrefutable-propositions.md).
