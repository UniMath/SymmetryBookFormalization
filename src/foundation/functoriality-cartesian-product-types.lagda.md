# Functoriality of cartesian product types

```agda
module foundation.functoriality-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.morphisms-arrows
open import foundation.sections
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.commuting-squares-of-maps
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.retracts-of-types
```

</details>

## Idea

The **functorial action** of the
[cartesian product](foundation-core.cartesian-product-types.md) takes two maps
`f : A → B` and `g : C → D` and returns a map

```text
  f × g : A × B → C × D
```

between the cartesian product types. This functorial action is _bifunctorial_ in
the sense that for any two maps `f : A → B` and `g : C → D` the diagram

```text
          f×1
    A × C ---> B × C
      |   \      |
  1×g |    \f×g  | 1×g
      |     \    |
      ∨      ∨   ∨
    A × D ---> B × D
          f×1
```

commutes.

## Definitions

### The functorial action of cartesian product types

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D)
  where

  map-product : (A × C) → (B × D)

  pr1 (map-product t) = f (pr1 t)
  pr2 (map-product t) = g (pr2 t)

  map-product-pr1 : pr1 ∘ map-product ~ f ∘ pr1
  map-product-pr1 (a , c) = refl

  map-product-pr2 : pr2 ∘ map-product ~ g ∘ pr2
  map-product-pr2 (a , c) = refl

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D)
  where

  coherence-square-map-product :
    coherence-square-maps
      ( map-product f id)
      ( map-product id g)
      ( map-product id g)
      ( map-product f id)
  coherence-square-map-product t = refl
```

## Properties

### Functoriality of products preserves identity maps

```agda
map-product-id :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  map-product (id {A = A}) (id {A = B}) ~ id
map-product-id (a , b) = refl
```

### Functoriality of products preserves composition

```agda
preserves-comp-map-product :
  {l1 l2 l3 l4 l5 l6 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {E : UU l5} {F : UU l6} (f : A → C) (g : B → D) (h : C → E) (k : D → F) →
  map-product (h ∘ f) (k ∘ g) ~ map-product h k ∘ map-product f g
preserves-comp-map-product f g h k t = refl
```

### Functoriality of products preserves homotopies

```agda
htpy-map-product :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f f' : A → C} (H : f ~ f') {g g' : B → D} (K : g ~ g') →
  map-product f g ~ map-product f' g'
htpy-map-product H K (a , b) = eq-pair (H a) (K b)
```

### Functoriality of products preserves equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  map-inv-map-product :
    (f : A → C) (g : B → D) → is-equiv f → is-equiv g → C × D → A × B
  map-inv-map-product f g H K =
    map-product (map-inv-is-equiv H) (map-inv-is-equiv K)

  is-section-map-inv-map-product :
    (f : A → C) (g : B → D) (H : is-equiv f) (K : is-equiv g) →
    map-product f g ∘ map-inv-map-product f g H K ~ id
  is-section-map-inv-map-product f g H K =
    htpy-map-product
      ( is-section-map-inv-is-equiv H)
      ( is-section-map-inv-is-equiv K)

  is-retraction-map-inv-map-product :
    (f : A → C) (g : B → D) (H : is-equiv f) (K : is-equiv g) →
    map-inv-map-product f g H K ∘ map-product f g ~ id
  is-retraction-map-inv-map-product f g H K =
    htpy-map-product
      ( is-retraction-map-inv-is-equiv H)
      ( is-retraction-map-inv-is-equiv K)

  is-equiv-map-product :
    (f : A → C) (g : B → D) →
    is-equiv f → is-equiv g → is-equiv (map-product f g)
  is-equiv-map-product f g H K =
    is-equiv-is-invertible
      ( map-inv-map-product f g H K)
      ( is-section-map-inv-map-product f g H K)
      ( is-retraction-map-inv-map-product f g H K)

  equiv-product : A ≃ C → B ≃ D → A × B ≃ C × D
  pr1 (equiv-product (f , is-equiv-f) (g , is-equiv-g)) = map-product f g
  pr2 (equiv-product (f , is-equiv-f) (g , is-equiv-g)) =
    is-equiv-map-product f g is-equiv-f is-equiv-g
```

### Functoriality of products preserves retractions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  map-retraction-map-product :
    (f : A → C) (g : B → D) → retraction f → retraction g → C × D → A × B
  map-retraction-map-product f g H K =
    map-product (map-retraction f H) (map-retraction g K)

  retraction-map-retraction-map-product :
    (f : A → C) (g : B → D) (H : retraction f) (K : retraction g) →
    is-retraction
      ( map-product f g)
      ( map-product (map-retraction f H) (map-retraction g K))
  retraction-map-retraction-map-product f g H K =
    htpy-map-product
      ( is-retraction-map-retraction f H)
      ( is-retraction-map-retraction g K)

  retraction-map-product :
    (f : A → C) (g : B → D) →
    retraction f → retraction g → retraction (map-product f g)
  retraction-map-product f g H K =
    ( map-retraction-map-product f g H K ,
      retraction-map-retraction-map-product f g H K)

  retract-map-product : A retract-of C → B retract-of D → A × B retract-of C × D
  retract-map-product (f , retraction-f) (g , retraction-g) =
    ( map-product f g , retraction-map-product f g retraction-f retraction-g)
```

### Functoriality of products preserves equivalences in either factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  equiv-product-left : A ≃ C → A × B ≃ C × B
  equiv-product-left f = equiv-product f id-equiv

  equiv-product-right : B ≃ C → A × B ≃ A × C
  equiv-product-right = equiv-product id-equiv
```

### The fibers of `map-product f g`

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) (t : C × D)
  where

  map-compute-fiber-map-product :
    fiber (map-product f g) t → fiber f (pr1 t) × fiber g (pr2 t)
  pr1 (pr1 (map-compute-fiber-map-product ((a , b) , refl))) = a
  pr2 (pr1 (map-compute-fiber-map-product ((a , b) , refl))) = refl
  pr1 (pr2 (map-compute-fiber-map-product ((a , b) , refl))) = b
  pr2 (pr2 (map-compute-fiber-map-product ((a , b) , refl))) = refl

  map-inv-compute-fiber-map-product :
    fiber f (pr1 t) × fiber g (pr2 t) → fiber (map-product f g) t
  pr1 (pr1 (map-inv-compute-fiber-map-product ((x , refl) , (y , refl)))) = x
  pr2 (pr1 (map-inv-compute-fiber-map-product ((x , refl) , (y , refl)))) = y
  pr2 (map-inv-compute-fiber-map-product ((x , refl) , (y , refl))) = refl

  is-section-map-inv-compute-fiber-map-product :
    map-compute-fiber-map-product ∘ map-inv-compute-fiber-map-product ~ id
  is-section-map-inv-compute-fiber-map-product ((x , refl) , (y , refl)) = refl

  is-retraction-map-inv-compute-fiber-map-product :
    map-inv-compute-fiber-map-product ∘ map-compute-fiber-map-product ~ id
  is-retraction-map-inv-compute-fiber-map-product ((a , b) , refl) = refl

  is-equiv-map-compute-fiber-map-product :
    is-equiv map-compute-fiber-map-product
  is-equiv-map-compute-fiber-map-product =
    is-equiv-is-invertible
      ( map-inv-compute-fiber-map-product)
      ( is-section-map-inv-compute-fiber-map-product)
      ( is-retraction-map-inv-compute-fiber-map-product)

  compute-fiber-map-product :
    fiber (map-product f g) t ≃ (fiber f (pr1 t) × fiber g (pr2 t))
  pr1 compute-fiber-map-product = map-compute-fiber-map-product
  pr2 compute-fiber-map-product = is-equiv-map-compute-fiber-map-product
```

### `map-product f g : A × B → C × D` is an equivalence if and only if we have `D → is-equiv f` and `C → is-equiv g`

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D)
  where

  is-equiv-left-factor-is-equiv-map-product' :
    D → is-equiv (map-product f g) → is-equiv f
  is-equiv-left-factor-is-equiv-map-product'
    d is-equiv-fg =
    is-equiv-is-contr-map
      ( λ x →
        is-contr-left-factor-product
          ( fiber f x)
          ( fiber g d)
          ( is-contr-is-equiv'
            ( fiber (map-product f g) (x , d))
            ( map-compute-fiber-map-product f g (x , d))
            ( is-equiv-map-compute-fiber-map-product f g (x , d))
            ( is-contr-map-is-equiv is-equiv-fg (x , d))))

  is-equiv-right-factor-is-equiv-map-product' :
    C → is-equiv (map-product f g) → is-equiv g
  is-equiv-right-factor-is-equiv-map-product'
    c is-equiv-fg =
    is-equiv-is-contr-map
      ( λ y →
        is-contr-right-factor-product
          ( fiber f c)
          ( fiber g y)
          ( is-contr-is-equiv'
            ( fiber (map-product f g) (c , y))
            ( map-compute-fiber-map-product f g (c , y))
            ( is-equiv-map-compute-fiber-map-product f g (c , y))
            ( is-contr-map-is-equiv is-equiv-fg (c , y))))

  map-inv-map-product' : (D → is-equiv f) → (C → is-equiv g) → C × D → A × B
  pr1 (map-inv-map-product' F G (c , d)) = map-inv-is-equiv (F d) c
  pr2 (map-inv-map-product' F G (c , d)) = map-inv-is-equiv (G c) d

  abstract
    is-section-map-inv-map-product' :
      (F : D → is-equiv f) (G : C → is-equiv g) →
      is-section (map-product f g) (map-inv-map-product' F G)
    is-section-map-inv-map-product' F G (c , d) =
      eq-pair
        ( is-section-map-inv-is-equiv (F d) c)
        ( is-section-map-inv-is-equiv (G c) d)

    is-retraction-map-inv-map-product' :
      (F : D → is-equiv f) (G : C → is-equiv g) →
      is-retraction (map-product f g) (map-inv-map-product' F G)
    is-retraction-map-inv-map-product' F G (a , b) =
      eq-pair
        ( is-retraction-map-inv-is-equiv (F (g b)) a)
        ( is-retraction-map-inv-is-equiv (G (f a)) b)

  is-equiv-map-product' :
    (D → is-equiv f) → (C → is-equiv g) → is-equiv (map-product f g)
  is-equiv-map-product' F G =
    is-equiv-is-invertible
      ( map-inv-map-product' F G)
      ( is-section-map-inv-map-product' F G)
      ( is-retraction-map-inv-map-product' F G)
```

### The functorial action of products on arrows

Given a pair of [morphisms of arrows](foundation.morphisms-arrows.md)
`α : f → g` and `β : h → i`, there is an induced morphism of arrows
`α × β : f × h → g × i` and this construction is functorial.

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {C : UU l5} {D : UU l6} {Z : UU l7} {W : UU l8}
  (f : A → B) (g : X → Y) (h : C → D) (i : Z → W)
  (α : hom-arrow f g) (β : hom-arrow h i)
  where

  product-hom-arrow : hom-arrow (map-product f h) (map-product g i)
  product-hom-arrow =
    ( ( map-product
        ( map-domain-hom-arrow f g α)
        ( map-domain-hom-arrow h i β)) ,
      ( map-product
        ( map-codomain-hom-arrow f g α)
        ( map-codomain-hom-arrow h i β)) ,
      ( htpy-map-product
        ( coh-hom-arrow f g α)
        ( coh-hom-arrow h i β)))
```

### Computing the action on paths of the functorial action of cartesian products

We have an equivalence of maps

```text
                                      pair-eq
              ((a , x) = (a' , x')) -----------> (a = a') × (x = x')
                       |                 ~                |
                       |                                  |
  ap (map-product f g) |                                  | map-product (ap f) (ap g)
                       |                                  |
                       ∨                 ~                ∨
          ((f a , g x) = (f a' , g x')) ---> (f a = f a') × (g x = g x')
                                      pair-eq
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) {a a' : A} {x x' : X}
  where

  compute-ap-map-product :
    pair-eq ∘ ap (map-product f g) ~
    map-product (ap f {a} {a'}) (ap g {x} {x'}) ∘ pair-eq
  compute-ap-map-product refl = refl
```

## See also

- Arithmetical laws involving cartesian product types are recorded in
  [`foundation.type-arithmetic-cartesian-product-types`](foundation.type-arithmetic-cartesian-product-types.md).
- Equality proofs in cartesian product types are characterized in
  [`foundation.equality-cartesian-product-types`](foundation.equality-cartesian-product-types.md).
- The universal property of cartesian product types is treated in
  [`foundation.universal-property-cartesian-product-types`](foundation.universal-property-cartesian-product-types.md).
- Functorial properties of dependent pair types are recorded in
  [`foundation.functoriality-dependent-pair-types`](foundation.functoriality-dependent-pair-types.md).
- Functorial properties of dependent product types are recorded in
  [`foundation.functoriality-dependent-function-types`](foundation.functoriality-dependent-function-types.md).
- Functorial properties of coproduct types are recorded in
  [`foundation.functoriality-coproduct-types`](foundation.functoriality-coproduct-types.md).
