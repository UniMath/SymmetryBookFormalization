# Decidable maps

```agda
module foundation.decidable-maps where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-morphisms-arrows
open import foundation.coproduct-types
open import foundation.decidable-dependent-pair-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.pi-0-trivial-maps
open import foundation.propositional-truncations
open import foundation.retracts-of-maps
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.injective-maps
open import foundation-core.iterating-functions
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

A [map](foundation-core.function-types.md) is said to be
{{#concept "decidable" Disambiguation="map of types" Agda=is-decidable-map}} if
its [fibers](foundation-core.fibers-of-maps.md) are
[decidable types](foundation.decidable-types.md).

## Definitions

### The structure on a map of decidability

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-map : (A → B) → UU (l1 ⊔ l2)
  is-decidable-map f = (y : B) → is-decidable (fiber f y)
```

### The type of decidable maps

```agda
infix 5 _→ᵈ_

_→ᵈ_ : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
A →ᵈ B = Σ (A → B) (is-decidable-map)

decidable-map : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
decidable-map = _→ᵈ_

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A →ᵈ B)
  where

  map-decidable-map : A → B
  map-decidable-map = pr1 f

  is-decidable-decidable-map : is-decidable-map map-decidable-map
  is-decidable-decidable-map = pr2 f
```

## Properties

### Decidable maps are closed under homotopy

```agda
abstract
  is-decidable-map-htpy :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
    f ~ g → is-decidable-map g → is-decidable-map f
  is-decidable-map-htpy H K b =
    is-decidable-equiv
      ( equiv-tot (λ a → equiv-concat (inv (H a)) b))
      ( K b)
```

### Maps with sections are decidable

```agda
is-decidable-map-section :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (i : A → B) → section i → is-decidable-map i
is-decidable-map-section i (s , S) b = inl (s b , S b)
```

### Any map out of the empty type is decidable

```agda
abstract
  is-decidable-map-ex-falso :
    {l : Level} {X : UU l} → is-decidable-map (ex-falso {l} {X})
  is-decidable-map-ex-falso x = inr pr1
```

### The identity map is decidable

```agda
abstract
  is-decidable-map-id :
    {l : Level} {X : UU l} → is-decidable-map (id {l} {X})
  is-decidable-map-id y = inl (y , refl)
```

### Equivalences are decidable maps

```agda
abstract
  is-decidable-map-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-equiv f → is-decidable-map f
  is-decidable-map-is-equiv H x = inl (center (is-contr-map-is-equiv H x))
```

### Composition of decidable maps

The composite `g ∘ f` of two decidable maps is decidable if `g` is injective.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g : B → C} {f : A → B}
  where

  abstract
    is-decidable-map-comp :
      is-injective g →
      is-decidable-map g →
      is-decidable-map f →
      is-decidable-map (g ∘ f)
    is-decidable-map-comp H G F x =
      rec-coproduct
        ( λ u →
          is-decidable-iff
            ( λ v → (pr1 v) , ap g (pr2 v) ∙ pr2 u)
            ( λ w → pr1 w , H (pr2 w ∙ inv (pr2 u)))
            ( F (pr1 u)))
        ( λ α → inr (λ t → α (f (pr1 t) , pr2 t)))
        ( G x)
```

The composite `g ∘ f` of two decidable maps is decidable if `g` is π₀-trivial.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g : B → C} {f : A → B}
  where

  abstract
    is-decidable-map-comp-is-π₀-trivial-map' :
      is-π₀-trivial-map' g →
      is-decidable-map g →
      is-decidable-map f →
      is-decidable-map (g ∘ f)
    is-decidable-map-comp-is-π₀-trivial-map' H G F x =
      is-decidable-equiv
        ( compute-fiber-comp g f x)
        ( is-decidable-Σ-all-elements-merely-equal-base (H x) (G x) (F ∘ pr1))

module _
  {l1 : Level} {A : UU l1} {f : A → A}
  (is-decidable-f : is-decidable-map f)
  (is-π₀-trivial-f : is-π₀-trivial-map' f)
  where

  is-decidable-map-iterate-is-π₀-trivial-map' :
    (n : ℕ) → is-decidable-map (iterate n f)
  is-decidable-map-iterate-is-π₀-trivial-map' zero-ℕ = is-decidable-map-id
  is-decidable-map-iterate-is-π₀-trivial-map' (succ-ℕ n) =
    is-decidable-map-comp-is-π₀-trivial-map'
      ( is-π₀-trivial-f)
      ( is-decidable-f)
      ( is-decidable-map-iterate-is-π₀-trivial-map' n)
```

### Left cancellation for decidable maps

If a composite `g ∘ f` is decidable and `g` is injective then `f` is decidable.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : A → B} {g : B → C}
  where

  abstract
    is-decidable-map-right-factor' :
      is-decidable-map (g ∘ f) → is-injective g → is-decidable-map f
    is-decidable-map-right-factor' GF G y =
      rec-coproduct
        ( λ q → inl (pr1 q , G (pr2 q)))
        ( λ q → inr (λ x → q ((pr1 x) , ap g (pr2 x))))
        ( GF (g y))
```

### Retracts into types with decidable equality are decidable

```agda
is-decidable-map-retraction :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → has-decidable-equality B →
  (i : A → B) → retraction i → is-decidable-map i
is-decidable-map-retraction d i (r , R) b =
  is-decidable-iff
    ( λ (p : i (r b) ＝ b) → r b , p)
    ( λ t → ap (i ∘ r) (inv (pr2 t)) ∙ ap i (R (pr1 t)) ∙ pr2 t)
    ( d (i (r b)) b)
```

### The map on total spaces induced by a family of decidable maps is decidable

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  is-decidable-map-tot :
    {f : (x : A) → B x → C x} →
    ((x : A) → is-decidable-map (f x)) → is-decidable-map (tot f)
  is-decidable-map-tot {f} H x =
    is-decidable-equiv (compute-fiber-tot f x) (H (pr1 x) (pr2 x))
```

### The map on total spaces induced by a decidable map on the base is decidable

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  where

  is-decidable-map-Σ-map-base :
    {f : A → B} → is-decidable-map f → is-decidable-map (map-Σ-map-base f C)
  is-decidable-map-Σ-map-base {f} H x =
    is-decidable-equiv' (compute-fiber-map-Σ-map-base f C x) (H (pr1 x))
```

### Products of decidable maps are decidable

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  is-decidable-map-product :
    {f : A → B} {g : C → D} →
    is-decidable-map f → is-decidable-map g → is-decidable-map (map-product f g)
  is-decidable-map-product {f} {g} F G x =
    is-decidable-equiv
      ( compute-fiber-map-product f g x)
      ( is-decidable-product (F (pr1 x)) (G (pr2 x)))
```

### Coproducts of decidable maps are decidable

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  is-decidable-map-coproduct :
    {f : A → B} {g : C → D} →
    is-decidable-map f →
    is-decidable-map g →
    is-decidable-map (map-coproduct f g)
  is-decidable-map-coproduct {f} {g} F G (inl x) =
    is-decidable-equiv' (compute-fiber-inl-map-coproduct f g x) (F x)
  is-decidable-map-coproduct {f} {g} F G (inr y) =
    is-decidable-equiv' (compute-fiber-inr-map-coproduct f g y) (G y)
```

### Decidable maps are closed under base change

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f : A → B} {g : C → D}
  where

  is-decidable-map-base-change :
    cartesian-hom-arrow g f → is-decidable-map f → is-decidable-map g
  is-decidable-map-base-change α F d =
    is-decidable-equiv
      ( equiv-fibers-cartesian-hom-arrow g f α d)
      ( F (map-codomain-cartesian-hom-arrow g f α d))
```

### Decidable maps are closed under retracts of maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y}
  where

  is-decidable-retract-map :
    f retract-of-map g → is-decidable-map g → is-decidable-map f
  is-decidable-retract-map R G x =
    is-decidable-retract-of
      ( retract-fiber-retract-map f g R x)
      ( G (map-codomain-inclusion-retract-map f g R x))
```
