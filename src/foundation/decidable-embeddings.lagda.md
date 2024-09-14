# Decidable embeddings

```agda
module foundation.decidable-embeddings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-morphisms-arrows
open import foundation.decidable-maps
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-maps
open import foundation.retracts-of-maps
open import foundation.subtype-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A [map](foundation-core.function-types.md) is said to be a
{{#concept "decidable embedding" Disambiguation="of types" Agda=is-decidable-emb}}
if it is an [embedding](foundation-core.embeddings.md) and its
[fibers](foundation-core.fibers-of-maps.md) are
[decidable types](foundation.decidable-types.md).

Equivalently, a decidable embedding is a map whose fibers are
[decidable propositions](foundation-core.decidable-propositions.md). We refer to
this condition as being a
{{#concept "decidably propositional map" Disambiguation="of types" Agda=is-decidable-prop-map}}.

## Definitions

### The condition on a map of being a decidable embedding

```agda
is-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (X → Y) → UU (l1 ⊔ l2)
is-decidable-emb f = is-emb f × is-decidable-map f

abstract
  is-emb-is-decidable-emb :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
    is-decidable-emb f → is-emb f
  is-emb-is-decidable-emb = pr1

is-decidable-map-is-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
  is-decidable-emb f → is-decidable-map f
is-decidable-map-is-decidable-emb = pr2
```

### Decidably propositional maps

```agda
is-decidable-prop-map :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (X → Y) → UU (l1 ⊔ l2)
is-decidable-prop-map {Y = Y} f = (y : Y) → is-decidable-prop (fiber f y)

abstract
  is-prop-map-is-decidable-prop-map :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
    is-decidable-prop-map f → is-prop-map f
  is-prop-map-is-decidable-prop-map H y = pr1 (H y)

is-decidable-map-is-decidable-prop-map :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
  is-decidable-prop-map f → is-decidable-map f
is-decidable-map-is-decidable-prop-map H y = pr2 (H y)
```

### The type of decidable embeddings

```agda
infix 5 _↪ᵈ_
_↪ᵈ_ :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (l1 ⊔ l2)
X ↪ᵈ Y = Σ (X → Y) is-decidable-emb

map-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → X ↪ᵈ Y → X → Y
map-decidable-emb e = pr1 e

abstract
  is-decidable-emb-map-decidable-emb :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ↪ᵈ Y) →
    is-decidable-emb (map-decidable-emb e)
  is-decidable-emb-map-decidable-emb e = pr2 e

abstract
  is-emb-map-decidable-emb :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ↪ᵈ Y) →
    is-emb (map-decidable-emb e)
  is-emb-map-decidable-emb e =
    is-emb-is-decidable-emb (is-decidable-emb-map-decidable-emb e)

abstract
  is-decidable-map-map-decidable-emb :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ↪ᵈ Y) →
    is-decidable-map (map-decidable-emb e)
  is-decidable-map-map-decidable-emb e =
    is-decidable-map-is-decidable-emb (is-decidable-emb-map-decidable-emb e)

emb-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → X ↪ᵈ Y → X ↪ Y
pr1 (emb-decidable-emb e) = map-decidable-emb e
pr2 (emb-decidable-emb e) = is-emb-map-decidable-emb e
```

## Properties

### Being a decidably propositional map is a proposition

```agda
abstract
  is-prop-is-decidable-prop-map :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
    is-prop (is-decidable-prop-map f)
  is-prop-is-decidable-prop-map f =
    is-prop-Π (λ y → is-prop-is-decidable-prop (fiber f y))
```

### Any map of which the fibers are decidable propositions is a decidable embedding

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y}
  where

  abstract
    is-decidable-emb-is-decidable-prop-map :
      is-decidable-prop-map f → is-decidable-emb f
    pr1 (is-decidable-emb-is-decidable-prop-map H) =
      is-emb-is-prop-map (is-prop-map-is-decidable-prop-map H)
    pr2 (is-decidable-emb-is-decidable-prop-map H) =
      is-decidable-map-is-decidable-prop-map H

  abstract
    is-prop-map-is-decidable-emb : is-decidable-emb f → is-prop-map f
    is-prop-map-is-decidable-emb H =
      is-prop-map-is-emb (is-emb-is-decidable-emb H)

  abstract
    is-decidable-prop-map-is-decidable-emb :
      is-decidable-emb f → is-decidable-prop-map f
    pr1 (is-decidable-prop-map-is-decidable-emb H y) =
      is-prop-map-is-decidable-emb H y
    pr2 (is-decidable-prop-map-is-decidable-emb H y) =
      is-decidable-map-is-decidable-emb H y
```

### Equivalences are decidable embeddings

```agda
abstract
  is-decidable-emb-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-equiv f → is-decidable-emb f
  is-decidable-emb-is-equiv H =
    ( is-emb-is-equiv H , is-decidable-map-is-equiv H)
```

### Identity maps are decidable embeddings

```agda
abstract
  is-decidable-emb-id :
    {l1 : Level} {A : UU l1} → is-decidable-emb (id {A = A})
  is-decidable-emb-id = (is-emb-id , is-decidable-map-id)

decidable-emb-id : {l1 : Level} {A : UU l1} → A ↪ᵈ A
decidable-emb-id = (id , is-decidable-emb-id)
```

### Being a decidable embedding is a property

```agda
abstract
  is-prop-is-decidable-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-prop (is-decidable-emb f)
  is-prop-is-decidable-emb f =
    is-prop-has-element
      ( λ H →
        is-prop-product
          ( is-property-is-emb f)
          ( is-prop-Π
            ( λ y → is-prop-is-decidable (is-prop-map-is-emb (pr1 H) y))))
```

### Decidable embeddings are closed under composition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g : B → C} {f : A → B}
  where

  abstract
    is-decidable-map-comp-is-decidable-emb' :
      is-decidable-emb g → is-decidable-map f → is-decidable-map (g ∘ f)
    is-decidable-map-comp-is-decidable-emb' K H x =
      rec-coproduct
        ( λ u →
          is-decidable-equiv
            ( ( left-unit-law-Σ-is-contr
                ( is-proof-irrelevant-is-prop
                  ( is-prop-map-is-emb (is-emb-is-decidable-emb K) x) u)
                ( u)) ∘e
              ( compute-fiber-comp g f x))
            ( H (pr1 u)))
        ( λ α → inr (λ t → α (f (pr1 t) , pr2 t)))
        ( is-decidable-map-is-decidable-emb K x)

  is-decidable-map-comp-is-decidable-emb :
    is-decidable-emb g → is-decidable-emb f → is-decidable-map (g ∘ f)
  is-decidable-map-comp-is-decidable-emb K H =
    is-decidable-map-comp-is-decidable-emb'
      ( K)
      ( is-decidable-map-is-decidable-emb H)

  is-decidable-emb-comp :
    is-decidable-emb g → is-decidable-emb f → is-decidable-emb (g ∘ f)
  is-decidable-emb-comp K H =
    ( is-emb-comp _ _ (pr1 K) (pr1 H) ,
      is-decidable-map-comp-is-decidable-emb K H)
```

### Left cancellation for decidable embeddings

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : A → B} {g : B → C}
  where

  is-decidable-emb-right-factor' :
      is-decidable-emb (g ∘ f) → is-emb g → is-decidable-emb f
  is-decidable-emb-right-factor' GH G =
    ( is-emb-right-factor g f G (is-emb-is-decidable-emb GH) ,
      is-decidable-map-right-factor'
        ( is-decidable-map-is-decidable-emb GH)
        ( is-injective-is-emb G))

  is-decidable-emb-right-factor :
      is-decidable-emb (g ∘ f) → is-decidable-emb g → is-decidable-emb f
  is-decidable-emb-right-factor GH G =
    is-decidable-emb-right-factor' GH (is-emb-is-decidable-emb G)
```

### Decidable embeddings are closed under homotopies

```agda
abstract
  is-decidable-emb-htpy :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
    f ~ g → is-decidable-emb g → is-decidable-emb f
  is-decidable-emb-htpy {f = f} {g} H K =
    ( is-emb-htpy H (is-emb-is-decidable-emb K) ,
      is-decidable-map-htpy H (is-decidable-map-is-decidable-emb K))
```

### In a commuting triangle of maps, if the top and right maps are decidable embeddings so is the left map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {top : A → B} {left : A → C} {right : B → C}
  (H : left ~ right ∘ top)
  where

  is-decidable-emb-left-map-triangle :
    is-decidable-emb top → is-decidable-emb right → is-decidable-emb left
  is-decidable-emb-left-map-triangle T R =
    is-decidable-emb-htpy H (is-decidable-emb-comp R T)
```

### In a commuting triangle of maps, if the left and right maps are decidable embeddings so is the top map

In fact, the right map need only be an embedding.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {top : A → B} {left : A → C} {right : B → C}
  (H : left ~ right ∘ top)
  where

  is-decidable-emb-top-map-triangle' :
    is-emb right → is-decidable-emb left → is-decidable-emb top
  is-decidable-emb-top-map-triangle' R' L =
    is-decidable-emb-right-factor' (is-decidable-emb-htpy (inv-htpy H) L) R'

  is-decidable-emb-top-map-triangle :
    is-decidable-emb right → is-decidable-emb left → is-decidable-emb top
  is-decidable-emb-top-map-triangle R L =
    is-decidable-emb-right-factor (is-decidable-emb-htpy (inv-htpy H) L) R
```

### Characterizing equality in the type of decidable embeddings

```agda
htpy-decidable-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A ↪ᵈ B) → UU (l1 ⊔ l2)
htpy-decidable-emb f g = map-decidable-emb f ~ map-decidable-emb g

refl-htpy-decidable-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↪ᵈ B) → htpy-decidable-emb f f
refl-htpy-decidable-emb f = refl-htpy

htpy-eq-decidable-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A ↪ᵈ B) →
  f ＝ g → htpy-decidable-emb f g
htpy-eq-decidable-emb f .f refl = refl-htpy-decidable-emb f

abstract
  is-torsorial-htpy-decidable-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↪ᵈ B) →
    is-torsorial (htpy-decidable-emb f)
  is-torsorial-htpy-decidable-emb f =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy (map-decidable-emb f))
      ( is-prop-is-decidable-emb)
      ( map-decidable-emb f)
      ( refl-htpy)
      ( is-decidable-emb-map-decidable-emb f)

abstract
  is-equiv-htpy-eq-decidable-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A ↪ᵈ B) →
    is-equiv (htpy-eq-decidable-emb f g)
  is-equiv-htpy-eq-decidable-emb f =
    fundamental-theorem-id
      ( is-torsorial-htpy-decidable-emb f)
      ( htpy-eq-decidable-emb f)

eq-htpy-decidable-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A ↪ᵈ B} →
  htpy-decidable-emb f g → f ＝ g
eq-htpy-decidable-emb {f = f} {g} =
  map-inv-is-equiv (is-equiv-htpy-eq-decidable-emb f g)
```

### Precomposing decidable embeddings with equivalences

```agda
equiv-precomp-decidable-emb-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  (C : UU l3) → (B ↪ᵈ C) ≃ (A ↪ᵈ C)
equiv-precomp-decidable-emb-equiv e C =
  equiv-Σ
    ( is-decidable-emb)
    ( equiv-precomp e C)
    ( λ g →
      equiv-iff-is-prop
        ( is-prop-is-decidable-emb g)
        ( is-prop-is-decidable-emb (g ∘ map-equiv e))
        ( λ H → is-decidable-emb-comp H (is-decidable-emb-is-equiv (pr2 e)))
        ( λ d →
          is-decidable-emb-htpy
            ( λ b → ap g (inv (is-section-map-inv-equiv e b)))
            ( is-decidable-emb-comp
              ( d)
              ( is-decidable-emb-is-equiv (is-equiv-map-inv-equiv e)))))
```

### Any map out of the empty type is a decidable embedding

```agda
abstract
  is-decidable-emb-ex-falso :
    {l : Level} {X : UU l} → is-decidable-emb (ex-falso {l} {X})
  is-decidable-emb-ex-falso = (is-emb-ex-falso , is-decidable-map-ex-falso)

decidable-emb-ex-falso :
  {l : Level} {X : UU l} → empty ↪ᵈ X
decidable-emb-ex-falso = (ex-falso , is-decidable-emb-ex-falso)

decidable-emb-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-empty A → A ↪ᵈ B
decidable-emb-is-empty {A = A} f =
  map-equiv
    ( equiv-precomp-decidable-emb-equiv (equiv-is-empty f id) _)
    ( decidable-emb-ex-falso)
```

### The map on total spaces induced by a family of decidable embeddings is a decidable embedding

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  is-decidable-emb-tot :
    {f : (x : A) → B x → C x} →
    ((x : A) → is-decidable-emb (f x)) → is-decidable-emb (tot f)
  is-decidable-emb-tot H =
    ( is-emb-tot (λ x → is-emb-is-decidable-emb (H x)) ,
      is-decidable-map-tot (λ x → is-decidable-map-is-decidable-emb (H x)))

  decidable-emb-tot : ((x : A) → B x ↪ᵈ C x) → Σ A B ↪ᵈ Σ A C
  decidable-emb-tot f =
    ( tot (λ x → map-decidable-emb (f x)) ,
      is-decidable-emb-tot (λ x → is-decidable-emb-map-decidable-emb (f x)))
```

### The map on total spaces induced by a decidable embedding on the base is a decidable embedding

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  where

  is-decidable-emb-map-Σ-map-base :
    {f : A → B} → is-decidable-emb f → is-decidable-emb (map-Σ-map-base f C)
  is-decidable-emb-map-Σ-map-base {f} H =
    ( is-emb-map-Σ-map-base C (is-emb-is-decidable-emb H) ,
      is-decidable-map-Σ-map-base C (is-decidable-map-is-decidable-emb H))

  decidable-emb-map-Σ-map-base :
    (f : A ↪ᵈ B) → Σ A (C ∘ map-decidable-emb f) ↪ᵈ Σ B C
  decidable-emb-map-Σ-map-base f =
    ( map-Σ-map-base (map-decidable-emb f) C ,
      is-decidable-emb-map-Σ-map-base ((is-decidable-emb-map-decidable-emb f)))
```

### The functoriality of dependent pair types preserves decidable embeddings

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} (D : B → UU l4)
  where

  is-decidable-emb-map-Σ :
    {f : A → B} {g : (x : A) → C x → D (f x)} →
    is-decidable-emb f →
    ((x : A) → is-decidable-emb (g x)) →
    is-decidable-emb (map-Σ D f g)
  is-decidable-emb-map-Σ {f} {g} F G =
    is-decidable-emb-left-map-triangle
      ( triangle-map-Σ D f g)
      ( is-decidable-emb-tot G)
      ( is-decidable-emb-map-Σ-map-base D F)

  decidable-emb-Σ :
    (f : A ↪ᵈ B) →
    ((x : A) → C x ↪ᵈ D (map-decidable-emb f x)) →
    Σ A C ↪ᵈ Σ B D
  decidable-emb-Σ f g =
    ( ( map-Σ D (map-decidable-emb f) (λ x → map-decidable-emb (g x))) ,
      ( is-decidable-emb-map-Σ
        ( is-decidable-emb-map-decidable-emb f)
        ( λ x → is-decidable-emb-map-decidable-emb (g x))))
```

### Products of decidable embeddings are decidable embeddings

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  is-decidable-emb-map-product :
    {f : A → B} {g : C → D} →
    is-decidable-emb f → is-decidable-emb g → is-decidable-emb (map-product f g)
  is-decidable-emb-map-product (eF , dF) (eG , dG) =
    ( is-emb-map-product eF eG , is-decidable-map-product dF dG)

  decidable-emb-product :
    A ↪ᵈ B → C ↪ᵈ D → A × C ↪ᵈ B × D
  decidable-emb-product (f , F) (g , G) =
    (map-product f g , is-decidable-emb-map-product F G)
```

### Coproducts of decidable embeddings are decidable embeddings

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  where

abstract
  is-decidable-emb-map-coproduct :
    {l1 l2 l3 l4 : Level}
    {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
    {f : A → B} {g : X → Y} →
    is-decidable-emb f →
    is-decidable-emb g →
    is-decidable-emb (map-coproduct f g)
  is-decidable-emb-map-coproduct {f = f} {g} (eF , dF) (eG , dG) =
    ( is-emb-map-coproduct eF eG , is-decidable-map-coproduct dF dG)
```

### Decidable embeddings are closed under base change

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f : A → B} {g : C → D}
  where

  is-decidable-prop-map-base-change :
    cartesian-hom-arrow g f → is-decidable-prop-map f → is-decidable-prop-map g
  is-decidable-prop-map-base-change α F d =
    is-decidable-prop-equiv
      ( equiv-fibers-cartesian-hom-arrow g f α d)
      ( F (map-codomain-cartesian-hom-arrow g f α d))

  is-decidable-emb-base-change :
    cartesian-hom-arrow g f → is-decidable-emb f → is-decidable-emb g
  is-decidable-emb-base-change α F =
    is-decidable-emb-is-decidable-prop-map
      ( is-decidable-prop-map-base-change α
        ( is-decidable-prop-map-is-decidable-emb F))
```

### Decidable embeddings are closed under retracts of maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y}
  where

  is-decidable-prop-map-retract-map :
    f retract-of-map g → is-decidable-prop-map g → is-decidable-prop-map f
  is-decidable-prop-map-retract-map R G x =
    is-decidable-prop-retract-of
      ( retract-fiber-retract-map f g R x)
      ( G (map-codomain-inclusion-retract-map f g R x))

  is-decidable-emb-retract-map :
    f retract-of-map g → is-decidable-emb g → is-decidable-emb f
  is-decidable-emb-retract-map R G =
    is-decidable-emb-is-decidable-prop-map
      ( is-decidable-prop-map-retract-map R
        ( is-decidable-prop-map-is-decidable-emb G))
```
