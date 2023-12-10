# Local families of types

```agda
module orthogonal-factorization-systems.local-families-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.orthogonal-maps
```

</details>

## Idea

A family of types `B : A → UU l` is said to be
{{#concept "local" Disambiguation="family of types" Agda=is-local-family}} at
`f : Y → X`, or **`f`-local**, if every
[fiber](foundation-core.fibers-of-maps.md) is.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} {Y : UU l1} {X : UU l2}
  (f : Y → X) {A : UU l3} (B : A → UU l4)
  where

  is-local-family : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-local-family = (x : A) → is-local f (B x)

  is-property-is-local-family : is-prop is-local-family
  is-property-is-local-family =
    is-prop-Π (λ x → is-property-is-equiv (precomp f (B x)))

  is-local-family-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-local-family-Prop = is-local-family
  pr2 is-local-family-Prop = is-property-is-local-family
```

## Properties

### A family is `f`-local if and only if it is `f`-orthogonal

This remains to be formalized.

## See also

- [Local maps](orthogonal-factorization-systems.local-maps.md)
- [Localizations with respect to maps](orthogonal-factorization-systems.localizations-maps.md)
- [Localizations with respect to subuniverses](orthogonal-factorization-systems.localizations-subuniverses.md)
