# The weak limited principle of omniscience

```agda
module foundation.weak-limited-principle-of-omniscience where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.disjunction
open import foundation.negation
open import foundation.universal-quantification
open import foundation.universe-levels

open import foundation-core.decidable-propositions
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Statement

The {{#concept "weak limited principle of omniscience"}} (WLPO) asserts that for
any [sequence](foundation.sequences.md) `f : ℕ → bool` either `f n` is true for
all `n : ℕ` or it is [not](foundation-core.negation.md). In particular, it is a
restricted form of the
[law of excluded middle](foundation.law-of-excluded-middle.md).

```agda
prop-bool-WLPO : Prop lzero
prop-bool-WLPO =
  ∀' (ℕ → bool) (λ f → is-decidable-Prop (∀' ℕ (λ n → is-true-Prop (f n))))

bool-WLPO : UU lzero
bool-WLPO = type-Prop prop-bool-WLPO

is-prop-bool-WLPO : is-prop bool-WLPO
is-prop-bool-WLPO = is-prop-type-Prop prop-bool-WLPO
```

```agda
prop-level-WLPO : (l : Level) → Prop (lsuc l)
prop-level-WLPO l =
  ∀'
    ( ℕ → Decidable-Prop l)
    ( λ f → is-decidable-Prop (∀' ℕ (λ n → prop-Decidable-Prop (f n))))

level-WLPO : (l : Level) → UU (lsuc l)
level-WLPO l = type-Prop (prop-level-WLPO l)

is-prop-level-WLPO : {l : Level} → is-prop (level-WLPO l)
is-prop-level-WLPO {l} = is-prop-type-Prop (prop-level-WLPO l)
```

```agda
WLPO : UUω
WLPO = {l : Level} → level-WLPO l
```

## See also

- [The principle of omniscience](foundation.principle-of-omniscience.md)
- [The limited principle of omniscience](foundation.limited-principle-of-omniscience.md)
- [The lesser limited principle of omniscience](foundation.lesser-limited-principle-of-omniscience.md)
- [Markov's principle](logic.markovs-principle.md)

## External links

- [Taboos.WLPO](https://martinescardo.github.io/TypeTopology/Taboos.WLPO.html)
  at TypeTopology
- [weak limited principle of omniscience](https://ncatlab.org/nlab/show/weak+limited+principle+of+omniscience)
  at $n$Lab
