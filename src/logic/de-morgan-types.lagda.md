# De Morgan types

```agda
module logic.de-morgan-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.double-negation
open import foundation.empty-types
open import foundation.evaluation-functions
open import foundation.function-types
open import foundation.identity-types
open import foundation.irrefutable-propositions
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.precomposition-functions
open import foundation.propositional-truncations
open import foundation.retracts-of-types
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.decidable-propositions
open import foundation-core.equivalences
open import foundation-core.propositions

open import logic.de-morgans-law
open import logic.propositionally-decidable-types
```

</details>

## Idea

In classical logic, i.e., logic where we assume
[the law of excluded middle](foundation.law-of-excluded-middle.md), the _De
Morgan laws_ refers to the pair of logical equivalences

```text
  ¬ (P ∨ Q) ⇔ (¬ P) ∧ (¬ Q)
  ¬ (P ∧ Q) ⇔ (¬ P) ∨ (¬ Q).
```

Out of these in total four logical implications, all but one are validated in
constructive mathematics. The odd one out is

```text
  ¬ (P ∧ Q) ⇒ (¬ P) ∨ (¬ Q).
```

Indeed, this would state that we could constructively deduce from a proof that
not both of `P` and `Q` are true, which of `P` and `Q` that is false. This
logical law is what we refer to as [De Morgan's Law](logic.de-morgans-law.md).
If a type `P` is such that for every other type `Q`, _the De Morgan implication_

```text
  ¬ (P ∧ Q) ⇒ (¬ P) ∨ (¬ Q)
```

holds, we say `P` is
{{#concept "De Morgan" Disambiguation="type" Agda=is-de-morgan Agda=De-Morgan-Type Agda=satisfies-de-morgans-law-type}}.

Equivalently, a type is De Morgan [iff](foundation.logical-equivalences.md) its
[negation](foundation-core.negation.md) is
[decidable](foundation.decidable-types.md). Since this is a
[small](foundation.small-types.md) condition, it is frequently more convenient
to use and is what we take as the main definition.

## Definition

### The small condition of being a De Morgan type

I.e., types whose negation is decidable.

```agda
module _
  {l : Level} (A : UU l)
  where

  is-de-morgan : UU l
  is-de-morgan = is-decidable (¬ A)

  is-prop-is-de-morgan : is-prop is-de-morgan
  is-prop-is-de-morgan = is-prop-is-decidable is-prop-neg

  is-de-morgan-Prop : Prop l
  is-de-morgan-Prop = is-decidable-Prop (neg-type-Prop A)
```

### The subuniverse of De Morgan types

We use the decidability of the negation condition to define the subuniverse of
De Morgan types.

```agda
De-Morgan-Type : (l : Level) → UU (lsuc l)
De-Morgan-Type l = Σ (UU l) (is-de-morgan)

module _
  {l : Level} (A : De-Morgan-Type l)
  where

  type-De-Morgan-Type : UU l
  type-De-Morgan-Type = pr1 A

  is-de-morgan-type-De-Morgan-Type : is-de-morgan type-De-Morgan-Type
  is-de-morgan-type-De-Morgan-Type = pr2 A
```

### Types that satisfy De Morgan's law

```agda
satisfies-de-morgans-law-type-Level :
  {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
satisfies-de-morgans-law-type-Level l2 A =
  (B : UU l2) → ¬ (A × B) → disjunction-type (¬ A) (¬ B)

satisfies-de-morgans-law-type : {l1 : Level} (A : UU l1) → UUω
satisfies-de-morgans-law-type A =
  {l2 : Level} (B : UU l2) → ¬ (A × B) → disjunction-type (¬ A) (¬ B)

is-prop-satisfies-de-morgans-law-type-Level :
  {l1 l2 : Level} {A : UU l1} →
  is-prop (satisfies-de-morgans-law-type-Level l2 A)
is-prop-satisfies-de-morgans-law-type-Level {A = A} =
  is-prop-Π (λ B → is-prop-Π (λ p → is-prop-disjunction-type (¬ A) (¬ B)))

satisfies-de-morgans-law-type-Prop :
  {l1 : Level} (l2 : Level) (A : UU l1) → Prop (l1 ⊔ lsuc l2)
satisfies-de-morgans-law-type-Prop l2 A =
  ( satisfies-de-morgans-law-type-Level l2 A ,
    is-prop-satisfies-de-morgans-law-type-Level)
```

```agda
satisfies-de-morgans-law-type-Level' :
  {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
satisfies-de-morgans-law-type-Level' l2 A =
  (B : UU l2) → ¬ (B × A) → disjunction-type (¬ B) (¬ A)

satisfies-de-morgans-law-type' : {l1 : Level} (A : UU l1) → UUω
satisfies-de-morgans-law-type' A =
  {l2 : Level} (B : UU l2) → ¬ (B × A) → disjunction-type (¬ B) (¬ A)

is-prop-satisfies-de-morgans-law-type-Level' :
  {l1 l2 : Level} {A : UU l1} →
  is-prop (satisfies-de-morgans-law-type-Level' l2 A)
is-prop-satisfies-de-morgans-law-type-Level' {A = A} =
  is-prop-Π (λ B → is-prop-Π (λ p → is-prop-disjunction-type (¬ B) (¬ A)))

satisfies-de-morgans-law-type-Prop' :
  {l1 : Level} (l2 : Level) (A : UU l1) → Prop (l1 ⊔ lsuc l2)
satisfies-de-morgans-law-type-Prop' l2 A =
  ( satisfies-de-morgans-law-type-Level' l2 A ,
    is-prop-satisfies-de-morgans-law-type-Level')
```

## Properties

### If a type satisfies De Morgan's law then its negation is decidable

Indeed, one need only check that `A` and `¬ A` satisfy De Morgan's law, as then
the hypothesis of the implication

```text
   ¬ (A ∧ ¬ A) ⇒ ¬ A ∨ ¬¬ A
```

is true.

```agda
module _
  {l : Level} (A : UU l)
  where

  is-de-morgan-satisfies-de-morgans-law' :
    ({l' : Level} (B : UU l') → ¬ (A × B) → ¬ A + ¬ B) → is-de-morgan A
  is-de-morgan-satisfies-de-morgans-law' H = H (¬ A) (λ f → pr2 f (pr1 f))

  is-merely-decidable-neg-satisfies-de-morgans-law :
    satisfies-de-morgans-law-type A → is-merely-decidable (¬ A)
  is-merely-decidable-neg-satisfies-de-morgans-law H =
    H (¬ A) (λ f → pr2 f (pr1 f))

  is-de-morgan-satisfies-de-morgans-law :
    satisfies-de-morgans-law-type A → is-de-morgan A
  is-de-morgan-satisfies-de-morgans-law H =
    rec-trunc-Prop
      ( is-decidable-Prop (neg-type-Prop A))
      ( id)
      ( H (¬ A) (λ f → pr2 f (pr1 f)))
```

### If the negation of a type is decidable then it satisfies De Morgan's law

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  satisfies-de-morgans-law-is-de-morgan-left :
    is-de-morgan A → ¬ (A × B) → ¬ A + ¬ B
  satisfies-de-morgans-law-is-de-morgan-left (inl na) f =
    inl na
  satisfies-de-morgans-law-is-de-morgan-left (inr nna) f =
    inr (λ y → nna (λ x → f (x , y)))

  satisfies-de-morgans-law-is-de-morgan-right :
    is-de-morgan B → ¬ (A × B) → ¬ A + ¬ B
  satisfies-de-morgans-law-is-de-morgan-right (inl nb) f =
    inr nb
  satisfies-de-morgans-law-is-de-morgan-right (inr nnb) f =
    inl (λ x → nnb (λ y → f (x , y)))

satisfies-de-morgans-law-is-de-morgan :
  {l : Level} {A : UU l} → is-de-morgan A → satisfies-de-morgans-law-type A
satisfies-de-morgans-law-is-de-morgan x B q =
  unit-trunc-Prop (satisfies-de-morgans-law-is-de-morgan-left x q)

satisfies-de-morgans-law-is-de-morgan' :
  {l : Level} {A : UU l} → is-de-morgan A → satisfies-de-morgans-law-type' A
satisfies-de-morgans-law-is-de-morgan' x B q =
  unit-trunc-Prop (satisfies-de-morgans-law-is-de-morgan-right x q)

module _
  {l : Level} (A : De-Morgan-Type l)
  where

  satisfies-de-morgans-law-type-De-Morgan-Type :
    satisfies-de-morgans-law-type (type-De-Morgan-Type A)
  satisfies-de-morgans-law-type-De-Morgan-Type =
    satisfies-de-morgans-law-is-de-morgan (is-de-morgan-type-De-Morgan-Type A)

  satisfies-de-morgans-law-type-De-Morgan-Type' :
    satisfies-de-morgans-law-type' (type-De-Morgan-Type A)
  satisfies-de-morgans-law-type-De-Morgan-Type' =
    satisfies-de-morgans-law-is-de-morgan' (is-de-morgan-type-De-Morgan-Type A)
```

### It is irrefutable that a type is De Morgan

```agda
is-irrefutable-is-de-morgan : {l : Level} {A : UU l} → ¬¬ (is-de-morgan A)
is-irrefutable-is-de-morgan = is-irrefutable-is-decidable
```

### Decidable types are De Morgan

```agda
is-de-morgan-is-decidable :
  {l : Level} {A : UU l} → is-decidable A → is-de-morgan A
is-de-morgan-is-decidable (inl x) = inr (intro-double-negation x)
is-de-morgan-is-decidable (inr x) = inl x

satisfies-de-morgans-law-is-decidable :
  {l : Level} {A : UU l} → is-decidable A → satisfies-de-morgans-law-type A
satisfies-de-morgans-law-is-decidable H =
  satisfies-de-morgans-law-is-de-morgan (is-de-morgan-is-decidable H)

satisfies-de-morgans-law-is-decidable' :
  {l : Level} {A : UU l} → is-decidable A → satisfies-de-morgans-law-type' A
satisfies-de-morgans-law-is-decidable' H =
  satisfies-de-morgans-law-is-de-morgan' (is-de-morgan-is-decidable H)
```

### Irrefutable types are De Morgan

```agda
is-de-morgan-is-irrefutable :
  {l : Level} {A : UU l} → ¬¬ A → is-de-morgan A
is-de-morgan-is-irrefutable = inr
```

### Contractible types are De Morgan

```agda
is-de-morgan-is-contr :
  {l : Level} {A : UU l} → is-contr A → is-de-morgan A
is-de-morgan-is-contr H =
  is-de-morgan-is-irrefutable (intro-double-negation (center H))

is-de-morgan-unit : is-de-morgan unit
is-de-morgan-unit = is-de-morgan-is-contr is-contr-unit
```

### Empty types are De Morgan

```agda
is-de-morgan-is-empty : {l : Level} {A : UU l} → is-empty A → is-de-morgan A
is-de-morgan-is-empty = inl

is-de-morgan-empty : is-de-morgan empty
is-de-morgan-empty = is-de-morgan-is-empty id
```

### De Morgan types are closed under logical equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-de-morgan-iff :
    (A → B) → (B → A) → is-de-morgan A → is-de-morgan B
  is-de-morgan-iff f g = is-decidable-iff (map-neg g) (map-neg f)

  is-de-morgan-iff' :
    (A ↔ B) → is-de-morgan A → is-de-morgan B
  is-de-morgan-iff' (f , g) = is-de-morgan-iff f g

  satisfies-de-morgans-law-iff :
    (A → B) → (B → A) →
    satisfies-de-morgans-law-type A → satisfies-de-morgans-law-type B
  satisfies-de-morgans-law-iff f g a =
    satisfies-de-morgans-law-is-de-morgan
      ( is-de-morgan-iff f g (is-de-morgan-satisfies-de-morgans-law A a))

  satisfies-de-morgans-law-iff' :
    (A ↔ B) → satisfies-de-morgans-law-type A → satisfies-de-morgans-law-type B
  satisfies-de-morgans-law-iff' (f , g) = satisfies-de-morgans-law-iff f g
```

### De Morgan types are closed under retracts

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (R : B retract-of A)
  where

  is-de-morgan-retract-of : is-de-morgan A → is-de-morgan B
  is-de-morgan-retract-of = is-de-morgan-iff' (iff-retract' R)

  is-de-morgan-retract-of' : is-de-morgan B → is-de-morgan A
  is-de-morgan-retract-of' = is-de-morgan-iff' (iff-retract R)
```

### De Morgan types are closed under equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  is-de-morgan-equiv' : is-de-morgan A → is-de-morgan B
  is-de-morgan-equiv' = is-de-morgan-iff' (iff-equiv e)

  is-de-morgan-equiv : is-de-morgan B → is-de-morgan A
  is-de-morgan-equiv = is-de-morgan-iff' (iff-equiv' e)
```

### Equivalent types have equivalent De Morgan predicates

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  iff-is-de-morgan : A ↔ B → is-de-morgan A ↔ is-de-morgan B
  iff-is-de-morgan e = iff-is-decidable (iff-neg e)

  equiv-iff-is-de-morgan : A ↔ B → is-de-morgan A ≃ is-de-morgan B
  equiv-iff-is-de-morgan e = equiv-is-decidable (equiv-iff-neg e)

  equiv-is-de-morgan : A ≃ B → is-de-morgan A ≃ is-de-morgan B
  equiv-is-de-morgan e = equiv-iff-is-de-morgan (iff-equiv e)
```

### The truncation of a De Morgan type is De Morgan

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  is-de-morgan-trunc : {k : 𝕋} → is-de-morgan A → is-de-morgan (type-trunc k A)
  is-de-morgan-trunc {neg-two-𝕋} a =
    is-de-morgan-is-contr is-trunc-type-trunc
  is-de-morgan-trunc {succ-𝕋 k} (inl na) =
    inl (map-universal-property-trunc (empty-Truncated-Type k) na)
  is-de-morgan-trunc {succ-𝕋 k} (inr nna) =
    inr (λ nn|a| → nna (λ a → nn|a| (unit-trunc a)))
```

### If the truncation of a type is De Morgan then the type is De Morgan

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  equiv-is-de-morgan-trunc :
    {k : 𝕋} → is-de-morgan (type-trunc (succ-𝕋 k) A) ≃ is-de-morgan A
  equiv-is-de-morgan-trunc {k} =
    equiv-is-decidable
      ( map-neg unit-trunc , is-truncation-trunc (empty-Truncated-Type k))

  is-de-morgan-is-de-morgan-trunc :
    {k : 𝕋} → is-de-morgan (type-trunc (succ-𝕋 k) A) → is-de-morgan A
  is-de-morgan-is-de-morgan-trunc = map-equiv equiv-is-de-morgan-trunc
```

### Products of De Morgan types are De Morgan

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-de-morgan-product : is-de-morgan A → is-de-morgan B → is-de-morgan (A × B)
  is-de-morgan-product (inl na) b =
    inl (λ ab → na (pr1 ab))
  is-de-morgan-product (inr nna) (inl nb) =
    inl (λ ab → nb (pr2 ab))
  is-de-morgan-product (inr nna) (inr nnb) =
    inr (is-irrefutable-product nna nnb)
```

### Coproducts of De Morgan types are De Morgan

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-de-morgan-coproduct :
    is-de-morgan A → is-de-morgan B → is-de-morgan (A + B)
  is-de-morgan-coproduct (inl na) (inl nb) =
    inl (rec-coproduct na nb)
  is-de-morgan-coproduct (inl na) (inr nnb) =
    inr (λ nab → nnb (λ nb → nab (inr nb)))
  is-de-morgan-coproduct (inr nna) _ =
    inr (λ nab → nna (λ na → nab (inl na)))

  is-de-morgan-disjunction :
    is-de-morgan A → is-de-morgan B → is-de-morgan (disjunction-type A B)
  is-de-morgan-disjunction a b = is-de-morgan-trunc (is-de-morgan-coproduct a b)
```

### The negation of a De Morgan type is De Morgan

```agda
is-de-morgan-neg : {l : Level} {A : UU l} → is-de-morgan A → is-de-morgan (¬ A)
is-de-morgan-neg = is-decidable-neg
```

### The identity types of De Morgan types are not generally De Morgan

Consider any type `A`, then its suspension `ΣA` is De Morgan since it is
inhabited. However, its identity type `N ＝ S` is equivalent to `A`, so cannot
be De Morgan unless `A` is.

> This remains to be formalized.

## External links

- [De Morgan laws, in constructive mathematics](https://ncatlab.org/nlab/show/De+Morgan+laws#in_constructive_mathematics)
  at $n$Lab
