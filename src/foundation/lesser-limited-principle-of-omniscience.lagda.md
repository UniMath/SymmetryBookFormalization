# The lesser limited principle of omniscience

```agda
module foundation.lesser-limited-principle-of-omniscience where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers

open import foundation.booleans
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.negation
open import foundation.universal-quantification
open import foundation.universe-levels

open import foundation-core.decidable-propositions
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Idea

The {{#concept "lesser limited principle of omniscience" Agda=LLPO}} (LLPO)
asserts that for any [sequence](foundation.sequences.md) of
[booleans](foundation.booleans.md) `f : ℕ → bool` such that `f n` is true for
[at most one](foundation-core.propositions.md) `n`, then either `f n` is false
for all even `n` or `f n` is false for all odd `n`.

## Definitions

### The small lesser limited principle of omniscience

```agda
prop-bool-LLPO : Prop lzero
prop-bool-LLPO =
  ∀'
    ( ℕ → bool)
    ( λ f →
      function-Prop
        ( is-prop (Σ ℕ (λ n → is-true (f n))))
        ( disjunction-Prop
          ( ∀' ℕ (λ n → function-Prop (is-even-ℕ n) (is-false-Prop (f n))))
          ( ∀' ℕ (λ n → function-Prop (is-odd-ℕ n) (is-false-Prop (f n))))))

bool-LLPO : UU lzero
bool-LLPO = type-Prop prop-bool-LLPO

is-prop-bool-LLPO : is-prop bool-LLPO
is-prop-bool-LLPO = is-prop-type-Prop prop-bool-LLPO
```

### The lesser limited principle of omniscience with respect to a universe level

```agda
prop-level-LLPO : (l : Level) → Prop (lsuc l)
prop-level-LLPO l =
  ∀'
    ( ℕ → Decidable-Prop l)
    ( λ f →
      function-Prop
        ( is-prop (Σ ℕ (type-Decidable-Prop ∘ f)))
        ( disjunction-Prop
          ( ∀' ℕ
            ( λ n →
              function-Prop
                ( is-even-ℕ n)
                ( neg-Prop (prop-Decidable-Prop (f n)))))
          ( ∀' ℕ
            ( λ n →
              function-Prop
                ( is-odd-ℕ n)
                ( neg-Prop (prop-Decidable-Prop (f n)))))))

level-LLPO : (l : Level) → UU (lsuc l)
level-LLPO l = type-Prop (prop-level-LLPO l)

is-prop-level-LLPO : {l : Level} → is-prop (level-LLPO l)
is-prop-level-LLPO {l} = is-prop-type-Prop (prop-level-LLPO l)
```

### The lesser limited principle of omniscience

```agda
LLPO : UUω
LLPO = {l : Level} → level-LLPO l
```

## See also

- [The principle of omniscience](foundation.principle-of-omniscience.md)
- [The limited principle of omniscience](foundation.limited-principle-of-omniscience.md)
- [The weak limited principle of omniscience](foundation.weak-limited-principle-of-omniscience.md)
- [Markov's principle](logic.markovs-principle.md)

## External links

- [Taboos.LLPO](https://martinescardo.github.io/TypeTopology/Taboos.LLPO.html)
  at TypeTopology
- [lesser limited principle of omniscience](https://ncatlab.org/nlab/show/lesser+limited+principle+of+omniscience)
  at $n$Lab
