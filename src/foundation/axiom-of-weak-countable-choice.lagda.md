# The axiom of weak countable choice

```agda
module foundation.axiom-of-weak-countable-choice where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.axiom-of-countable-choice
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.law-of-excluded-middle
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

The {{#concept "axiom of weak countable choice" Agda=WCC}} asserts that for
every family of [inhabited](foundation.inhabited-types.md) types `F` indexed by
[`ℕ`](elementary-number-theory.natural-numbers.md), where for at most one `n`,
`F n` is not [contractible](foundation.contractible-types.md), the type of
sections of that family `(n : ℕ) → B n` is inhabited. This axiom was introduced
in {{#cite Bridges2000}}.

## Definitions

### Instances of weak countable choice

```agda
instance-weak-countable-choice : {l : Level} → (ℕ → UU l) → UU l
instance-weak-countable-choice F =
  ( (n : ℕ) → is-inhabited (F n)) →
  ( (m n : ℕ) →
    m ≠ n →
    type-Prop (is-contr-Prop (F m) ∨ is-contr-Prop (F n))) →
  is-inhabited ((n : ℕ) → F n)
```

### The axiom of weak countable choice

```agda
instance-weak-countable-choice-Set :
  {l : Level} → (ℕ → Set l) → UU l
instance-weak-countable-choice-Set F =
  instance-weak-countable-choice (type-Set ∘ F)

level-WCC : (l : Level) → UU (lsuc l)
level-WCC l = (F : ℕ → Set l) → instance-weak-countable-choice-Set F

WCC : UUω
WCC = {l : Level} → level-WCC l
```

## Properties

### The law of excluded middle implies weak countable choice

```agda
wcc-lem : {l : Level} → LEM l → level-WCC l
wcc-lem {l} lem F inhab-F contr-le
  with lem (∃ ℕ (λ n → ¬' (is-contr-Prop (type-Set (F n)))))
... | inr none-non-contractible =
  unit-trunc-Prop
    ( λ n →
      rec-coproduct
        ( center)
        ( ex-falso ∘ none-non-contractible ∘ intro-exists n)
        ( lem (is-contr-Prop (type-Set (F n)))))
... | inl one-not-contractible =
  elim-exists
    ( claim)
    ( λ n not-contractible-Fn →
      rec-trunc-Prop
        ( claim)
        ( λ elem-Fn →
          unit-trunc-Prop
            ( λ m →
              rec-coproduct
                ( λ m=n → tr (type-Set ∘ F) (inv m=n) elem-Fn)
                ( λ m≠n →
                  center
                    ( map-right-unit-law-disjunction-is-empty-Prop
                      ( is-contr-Prop (type-Set (F m)))
                      ( is-contr-Prop (type-Set (F n)))
                      ( not-contractible-Fn)
                      ( contr-le m n m≠n)))
                ( has-decidable-equality-ℕ m n)))
        ( inhab-F n))
    ( one-not-contractible)
    where
    claim : Prop l
    claim = is-inhabited-Prop ((n : ℕ) → type-Set (F n))
```

## Properties

### The axiom of countable choice implies the axiom of weak countable choice

```agda
instance-weak-countable-choice-instance-countable-choice :
  {l : Level} → (F : ℕ → UU l) →
  instance-countable-choice F → instance-weak-countable-choice F
instance-weak-countable-choice-instance-countable-choice F cc inhab-F _ =
  cc inhab-F

instance-weak-countable-choice-instance-countable-choice-Set :
  {l : Level} → (F : ℕ → Set l) →
  instance-countable-choice-Set F → instance-weak-countable-choice-Set F
instance-weak-countable-choice-instance-countable-choice-Set F =
  instance-weak-countable-choice-instance-countable-choice (type-Set ∘ F)

level-WCC-level-ACω : {l : Level} → level-countable-choice-Set l → level-WCC l
level-WCC-level-ACω acω-l F =
  instance-weak-countable-choice-instance-countable-choice-Set F (acω-l F)

WCC-ACω : ACω → WCC
WCC-ACω acω = level-WCC-level-ACω acω
```

## Table of choice principles

{{#include tables/choice-principles.md}}

## External links

- [Weak countable choice](https://ncatlab.org/nlab/show/countable+choice#WCC) at
  nLab

## References

{{#bibliography}}
