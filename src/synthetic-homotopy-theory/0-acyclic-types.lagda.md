# `0`-acyclic types

```agda
module synthetic-homotopy-theory.0-acyclic-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.0-acyclic-maps
open import synthetic-homotopy-theory.truncated-acyclic-maps
open import synthetic-homotopy-theory.truncated-acyclic-types
```

</details>

## Idea

We characterize the
[`0`-acyclic types](synthetic-homotopy-theory.truncated-acyclic-types.md) as the
[inhabited types](foundation.inhabited-types.md).

## Definition

### The predicate of being a `0`-acyclic type

```agda
module _
  {l : Level} (A : UU l)
  where

  is-0-acyclic-Prop : Prop l
  is-0-acyclic-Prop = is-truncated-acyclic-Prop zero-𝕋 A

  is-0-acyclic : UU l
  is-0-acyclic = type-Prop is-0-acyclic-Prop

  is-prop-is-0-acyclic : is-prop is-0-acyclic
  is-prop-is-0-acyclic = is-prop-type-Prop is-0-acyclic-Prop
```

## Properties

### A type is `0`-acyclic if and only if it is inhabited

```agda
module _
  {l : Level} {A : UU l}
  where

  is-inhabited-is-0-acyclic : is-0-acyclic A → is-inhabited A
  is-inhabited-is-0-acyclic ac =
    map-trunc-Prop
      ( pr1)
      ( is-surjective-is-0-acyclic-map
        ( terminal-map)
        ( is-truncated-acyclic-map-terminal-map-is-truncated-acyclic A ac)
        ( star))

  is-0-acyclic-is-inhabited : is-inhabited A → is-0-acyclic A
  is-0-acyclic-is-inhabited h =
    is-truncated-acyclic-is-truncated-acyclic-map-terminal-map A
      ( is-0-acyclic-map-is-surjective
        ( terminal-map)
        ( λ u →
          map-trunc-Prop
            (λ a → pair a (contraction is-contr-unit u))
            ( h)))
```

## See also

- [Acyclic maps](synthetic-homotopy-theory.acyclic-maps.md)
- [Acyclic types](synthetic-homotopy-theory.acyclic-types.md)
- [`0`-acyclic maps](synthetic-homotopy-theory.0-acyclic-maps.md)
- [`k`-acyclic types](synthetic-homotopy-theory.truncated-acyclic-types.md)
- [`k`-acyclic maps](synthetic-homotopy-theory.truncated-acyclic-maps.md)
- [Dependent epimorphisms](foundation.dependent-epimorphisms.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)
