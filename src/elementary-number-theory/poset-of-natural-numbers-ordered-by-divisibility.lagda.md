# The poset of natural numbers ordered by divisibility

```agda
module
  elementary-number-theory.poset-of-natural-numbers-ordered-by-divisibility
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.bounded-divisibility-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

The **poset of natural numbers ordered by divisibility** consists of the
[natural numbers](elementary-number-theory.natural-numbers.md) and its ordering
is defined by
[bounded divisibility](elementary-number-theory.bounded-divisibility-natural-numbers.md),
i.e., the type `m ≤ n` is defined to be the type of natural numbers `q ≤ n` such
that `q * m ＝ n`.

Recall that bounded divisibility is
[logically equivalent](foundation.logical-equivalences.md) to the more standard
[divisibility relation](elementar-number-theory.divisibility-natural-numbers.md).
However, the divisibility relation `m | n` is only valued in the
[propositions](foundation.propositions.md) when both `m` and `n` are
[nonzero](elementary-number-theory.nonzero-natural-numbers.md). On the other
hand, bounded divisibility is always valued in propositions. By using bounded
divisibility we avoid the need for
[propoositional truncation](foundation.propositional-truncations.md).

## Definition

```agda
leq-prop-ℕ-Div : ℕ → ℕ → Prop lzero
leq-prop-ℕ-Div = bounded-div-ℕ-Prop

leq-ℕ-Div : ℕ → ℕ → UU lzero
leq-ℕ-Div m n = type-Prop (leq-prop-ℕ-Div m n)

refl-leq-ℕ-Div : (n : ℕ) → leq-ℕ-Div n n
refl-leq-ℕ-Div = refl-bounded-div-ℕ

antisymmetric-leq-ℕ-Div : (m n : ℕ) → leq-ℕ-Div m n → leq-ℕ-Div n m → m ＝ n
antisymmetric-leq-ℕ-Div = antisymmetric-bounded-div-ℕ

transitive-leq-ℕ-Div :
  (m n o : ℕ) → leq-ℕ-Div n o → leq-ℕ-Div m n → leq-ℕ-Div m o
transitive-leq-ℕ-Div = transitive-bounded-div-ℕ

ℕ-Div-Preorder : Preorder lzero lzero
pr1 ℕ-Div-Preorder = ℕ
pr1 (pr2 ℕ-Div-Preorder) = leq-prop-ℕ-Div
pr1 (pr2 (pr2 ℕ-Div-Preorder)) = refl-leq-ℕ-Div
pr2 (pr2 (pr2 ℕ-Div-Preorder)) = transitive-leq-ℕ-Div

ℕ-Div-Poset : Poset lzero lzero
pr1 ℕ-Div-Poset = ℕ-Div-Preorder
pr2 ℕ-Div-Poset = antisymmetric-leq-ℕ-Div
```
