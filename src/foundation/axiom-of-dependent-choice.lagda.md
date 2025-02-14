# The axiom of dependent choice

```agda
module foundation.axiom-of-dependent-choice where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.existential-quantification
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Statement

The
{{#concept "axiom of dependent choice" WD="axiom of dependent choice" WDID=Q3303153}}
asserts that for every [inhabited](foundation.inhabited-types.md)
[set](foundation.sets.md) `A` and
[binary relation](foundation.binary-relations.md) `R` on `A`, such that for
every `a : A`, `∃ A (λ b → R a b)`, there is a sequence `f : ℕ → A` with
`R (f n) (f (succ-ℕ n))` for every `n`.

### Instances of dependent choice

```agda
module _
  {l1 l2 : Level}
  (A : Set l1) (H : is-inhabited (type-Set A))
  (R : Relation-Prop l2 (type-Set A))
  (total-R : (a : type-Set A) → exists (type-Set A) (R a))
  where

  instance-dependent-choice-Prop : Prop (l1 ⊔ l2)
  instance-dependent-choice-Prop =
    ∃ (ℕ → type-Set A) (λ f → Π-Prop ℕ (λ n → R (f n) (f (succ-ℕ n))))

  instance-dependent-choice : UU (l1 ⊔ l2)
  instance-dependent-choice = type-Prop instance-dependent-choice-Prop
```

### The axiom of dependent choice

```agda
level-ADC : (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
level-ADC l1 l2 =
  (A : Set l1) (H : is-inhabited (type-Set A)) →
  (R : Relation-Prop l2 (type-Set A))
  (total-R : (a : type-Set A) → exists (type-Set A) (R a)) →
  instance-dependent-choice A H R total-R

ADC : UUω
ADC = {l1 l2 : Level} → level-ADC l1 l2
```

## Table of choice principles

{{#include tables/choice-principles.md}}

## External links

- [Axiom of dependent choice](https://en.wikipedia.org/wiki/Axiom_of_dependent_choice)
