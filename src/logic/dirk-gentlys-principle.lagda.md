# Dirk Gently's principle

```agda
module logic.dirk-gentlys-principle where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.double-negation
open import foundation.empty-types
open import foundation.evaluation-functions
open import foundation.function-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.decidable-propositions
```

</details>

## Idea

{{#concept "Dirk Gently's principle"}} is the logical axiom that the type of
[propositions](foundation-core.propositions.md) is
[linearly ordered](order-theory.total-orders.md). In other words, for every pair
of propositions `P` and `Q`, either `P` implies `Q` or `Q` implies `P`:

$$
  (P ⇒ Q) ∨ (Q ⇒ P).
$$

The proof strength of this principle lies strictly between the
[law of excluded middle](foundation.law-of-excluded-middle.md) and
[De Morgan's law](logic.de-morgans-law.md), Section 8.5 {{#cite Diener18}}.

## Statement

```agda
instance-prop-Dirk-Gently's-Principle :
  {l1 l2 : Level} → Prop l1 → Prop l2 → Prop (l1 ⊔ l2)
instance-prop-Dirk-Gently's-Principle P Q = (P ⇒ Q) ∨ (Q ⇒ P)
```
