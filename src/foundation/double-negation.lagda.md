# Double negation

```agda
module foundation.double-negation where
```

<details><summary>Imports</summary>

```agda
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.propositions
```

</details>

## Definition

We define double negation and triple negation

```agda
infix 25 ¬¬_ ¬¬¬_

¬¬_ : {l : Level} → UU l → UU l
¬¬ P = ¬ (¬ P)

¬¬¬_ : {l : Level} → UU l → UU l
¬¬¬ P = ¬ (¬ (¬ P))
```

We also define the introduction rule for double negation, and the action on maps
of double negation.

```agda
intro-double-negation : {l : Level} {P : UU l} → P → ¬¬ P
intro-double-negation p f = f p

map-double-negation :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} → (P → Q) → ¬¬ P → ¬¬ Q
map-double-negation f = map-neg (map-neg f)

elim-triple-negation : {l : Level} {P : UU l} → ¬¬¬ P → ¬ P
elim-triple-negation = map-neg intro-double-negation
```

## Properties

### The double negation of a type is a proposition

```agda
double-negation-type-Prop :
  {l : Level} (A : UU l) → Prop l
double-negation-type-Prop A = neg-type-Prop (¬ A)

double-negation-Prop :
  {l : Level} (P : Prop l) → Prop l
double-negation-Prop P = double-negation-type-Prop (type-Prop P)

is-prop-double-negation :
  {l : Level} {A : UU l} → is-prop (¬¬ A)
is-prop-double-negation = is-prop-neg

infix 25 ¬¬'_

¬¬'_ : {l : Level} (P : Prop l) → Prop l
¬¬'_ = double-negation-Prop
```

### Double negations of classical laws

```agda
double-negation-double-negation-elim :
  {l : Level} {P : UU l} → ¬¬ (¬¬ P → P)
double-negation-double-negation-elim {P = P} f =
  ( λ (np : ¬ P) → f (λ (nnp : ¬¬ P) → ex-falso (nnp np)))
  ( λ (p : P) → f (λ (nnp : ¬¬ P) → p))

double-negation-Peirces-law :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} → ¬¬ (((P → Q) → P) → P)
double-negation-Peirces-law {P = P} f =
  ( λ (np : ¬ P) → f (λ h → h (λ p → ex-falso (np p))))
  ( λ (p : P) → f (λ _ → p))

double-negation-linearity-implication :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  ¬¬ ((P → Q) + (Q → P))
double-negation-linearity-implication {P = P} {Q = Q} f =
  ( λ (np : ¬ P) →
    map-neg (inl {A = P → Q} {B = Q → P}) f (λ p → ex-falso (np p)))
  ( λ (p : P) → map-neg (inr {A = P → Q} {B = Q → P}) f (λ _ → p))
```

### Maps into double negations extend along `intro-double-negation`

```agda
extend-double-negation :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → ¬¬ Q) → (¬¬ P → ¬¬ Q)
extend-double-negation {P = P} {Q = Q} f nnp nq = nnp (λ p → f p nq)
```

### The double negation of a type is logically equivalent to the double negation of its propositional truncation

```agda
abstract
  intro-double-negation-type-trunc-Prop :
    {l : Level} {A : UU l} → type-trunc-Prop A → ¬¬ A
  intro-double-negation-type-trunc-Prop {A = A} =
    map-universal-property-trunc-Prop
      ( double-negation-type-Prop A)
      ( intro-double-negation)

abstract
  double-negation-double-negation-type-trunc-Prop :
    {l : Level} {A : UU l} → ¬¬ (type-trunc-Prop A) → ¬¬ A
  double-negation-double-negation-type-trunc-Prop =
    extend-double-negation intro-double-negation-type-trunc-Prop

abstract
  double-negation-type-trunc-Prop-double-negation :
    {l : Level} {A : UU l} → ¬¬ A → ¬¬ (type-trunc-Prop A)
  double-negation-type-trunc-Prop-double-negation =
    map-double-negation unit-trunc-Prop
```

## See also

- [Double negation elimination](logic.double-negation-elimination.md)
- [Irrefutable propositions](foundation.irrefutable-propositions.md)

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}
