# Local maps

```agda
module orthogonal-factorization-systems.local-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-morphisms-arrows
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-fibers-of-maps
open import foundation.homotopies
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.pullbacks
open import foundation.unit-type
open import foundation.universal-property-family-of-fibers-of-maps
open import foundation.universe-levels

open import orthogonal-factorization-systems.local-families-of-types
open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.orthogonal-maps
open import orthogonal-factorization-systems.pullback-hom
```

</details>

## Idea

A map `g : X → Y` is said to be
{{#concept "local" Disambiguation="maps of types" Agda=is-local-map}} at
`f : A → B`, or
{{#concept "`f`-local" Disambiguation="maps of types" Agda=is-local-map}}, if
all its [fibers](foundation-core.fibers-of-maps.md) are
[`f`-local types](orthogonal-factorization-systems.local-types.md).

Equivalently, the map `g` is `f`-local if and only if `f` is
[orthogonal](orthogonal-factorization-systems.orthogonal-maps.md) to `g`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-local-map : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-local-map = is-local-family f (fiber g)

  is-property-is-local-map : is-prop is-local-map
  is-property-is-local-map = is-property-is-local-family f (fiber g)

  is-local-map-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-local-map-Prop = is-local-family-Prop f (fiber g)
```

### A type `B` is `f`-local if and only if the terminal map `B → unit` is `f`-local

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {Y : UU l3}
  (f : A → B)
  where

  is-local-is-local-terminal-map :
    is-local-map f (terminal-map Y) → is-local f Y
  is-local-is-local-terminal-map H =
    is-local-equiv f (inv-equiv-fiber-terminal-map star) (H star)

  is-local-terminal-map-is-local :
    is-local f Y → is-local-map f (terminal-map Y)
  is-local-terminal-map-is-local H u =
    is-local-equiv f (equiv-fiber-terminal-map u) H
```

### A map is `f`-local if and only if it is `f`-orthogonal

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-local-map-is-orthogonal-pullback-condition :
    is-orthogonal-pullback-condition f g → is-local-map f g
  is-local-map-is-orthogonal-pullback-condition G y =
    is-local-is-orthogonal-pullback-condition-terminal-map f
      ( is-orthogonal-pullback-condition-right-base-change f g
        ( terminal-map (fiber g y))
        ( fiber-cartesian-hom-arrow g y)
        ( G))

  is-local-map-is-orthogonal : is-orthogonal f g → is-local-map f g
  is-local-map-is-orthogonal G y =
    is-local-is-orthogonal-terminal-map f
      ( is-orthogonal-right-base-change f g
        ( terminal-map (fiber g y))
        ( fiber-cartesian-hom-arrow g y)
        ( G))
```

The converse remains to be formalized.

## See also

- [Localizations with respect to maps](orthogonal-factorization-systems.localizations-maps.md)
- [Localizations with respect to subuniverses](orthogonal-factorization-systems.localizations-subuniverses.md)
