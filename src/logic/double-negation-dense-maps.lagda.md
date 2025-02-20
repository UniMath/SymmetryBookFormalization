# Dense maps

```agda
module logic.double-negation-dense-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.connected-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.double-negation
open import foundation.embeddings
open import foundation.equality-cartesian-product-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.irrefutable-propositions
open import foundation.postcomposition-dependent-functions
open import foundation.propositional-truncations
open import foundation.split-surjective-maps
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.surjective-maps
open import foundation.truncated-types
open import foundation.univalence
open import foundation.universal-property-family-of-fibers-of-maps
open import foundation.universal-property-propositional-truncation
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.constant-maps
open import foundation-core.contractible-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.homotopies
open import foundation-core.precomposition-dependent-functions
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.retracts-of-types
open import foundation-core.sections
open import foundation-core.sets
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-maps
open import foundation-core.truncation-levels

open import logic.double-negation-stable-embeddings

open import orthogonal-factorization-systems.extensions-maps
```

</details>

## Idea

A map `f : A → B` is {{#concept "dense" Agda=is-double-negation-dense-map}}, if
all of its [fibers](foundation-core.fibers-of-maps.md) are
[irrefutable](logic.irrefutable-propositions.md). I.e., for every `y : B`, it is
not not true that `y` has a preimage under `f`.

## Definitions

### The predicate on maps of being double negation dense

```agda
is-double-negation-dense-map-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → Prop (l1 ⊔ l2)
is-double-negation-dense-map-Prop {B = B} f =
  Π-Prop B (double-negation-type-Prop ∘ fiber f)

is-double-negation-dense-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-double-negation-dense-map f = type-Prop (is-double-negation-dense-map-Prop f)

is-prop-is-double-negation-dense-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-double-negation-dense-map f)
is-prop-is-double-negation-dense-map f =
  is-prop-type-Prop (is-double-negation-dense-map-Prop f)

infix 5 _↠¬¬_
_↠¬¬_ : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A ↠¬¬ B = Σ (A → B) is-double-negation-dense-map

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↠¬¬ B)
  where

  map-double-negation-dense-map : A → B
  map-double-negation-dense-map = pr1 f

  is-double-negation-dense-map-double-negation-dense-map :
    is-double-negation-dense-map map-double-negation-dense-map
  is-double-negation-dense-map-double-negation-dense-map = pr2 f
```

### The type of all double negation dense maps out of a type

```agda
Double-Negation-Dense-Map :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Double-Negation-Dense-Map l2 A = Σ (UU l2) (A ↠¬¬_)

module _
  {l1 l2 : Level} {A : UU l1} (f : Double-Negation-Dense-Map l2 A)
  where

  type-Double-Negation-Dense-Map : UU l2
  type-Double-Negation-Dense-Map = pr1 f

  double-negation-dense-map-Double-Negation-Dense-Map :
    A ↠¬¬ type-Double-Negation-Dense-Map
  double-negation-dense-map-Double-Negation-Dense-Map = pr2 f

  map-Double-Negation-Dense-Map : A → type-Double-Negation-Dense-Map
  map-Double-Negation-Dense-Map =
    map-double-negation-dense-map
      double-negation-dense-map-Double-Negation-Dense-Map

  is-double-negation-dense-map-Double-Negation-Dense-Map :
    is-double-negation-dense-map map-Double-Negation-Dense-Map
  is-double-negation-dense-map-Double-Negation-Dense-Map =
    is-double-negation-dense-map-double-negation-dense-map
      double-negation-dense-map-Double-Negation-Dense-Map
```

## Properties

### Any surjective map is dense

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-double-negation-dense-map-is-surjective :
    {f : A → B} → is-surjective f → is-double-negation-dense-map f
  is-double-negation-dense-map-is-surjective H =
    intro-double-negation-type-trunc-Prop ∘ H

  double-negation-dense-map-surjection : (A ↠ B) → (A ↠¬¬ B)
  double-negation-dense-map-surjection =
    tot (λ _ → is-double-negation-dense-map-is-surjective)
```

### Any map that has a section is dense

```agda
is-double-negation-dense-map-has-section :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  section f → is-double-negation-dense-map f
is-double-negation-dense-map-has-section (g , G) b =
  intro-double-negation (g b , G b)
```

### The underlying irrefutable surjection of a retract

```agda
double-negation-dense-map-retract :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A retract-of B → B ↠¬¬ A
double-negation-dense-map-retract R =
  ( map-retraction-retract R ,
    is-double-negation-dense-map-has-section (section-retract R))
```

### Any split surjective map is dense

```agda
is-double-negation-dense-map-is-split-surjective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-split-surjective f → is-double-negation-dense-map f
is-double-negation-dense-map-is-split-surjective H =
  intro-double-negation ∘ H
```

### Any equivalence is dense

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-double-negation-dense-map-is-equiv :
    {f : A → B} → is-equiv f → is-double-negation-dense-map f
  is-double-negation-dense-map-is-equiv H =
    is-double-negation-dense-map-has-section (section-is-equiv H)

  is-double-negation-dense-map-equiv :
    (e : A ≃ B) → is-double-negation-dense-map (map-equiv e)
  is-double-negation-dense-map-equiv e =
    is-double-negation-dense-map-is-equiv (is-equiv-map-equiv e)

  double-negation-dense-map-equiv : A ≃ B → A ↠¬¬ B
  double-negation-dense-map-equiv e =
    (map-equiv e , is-double-negation-dense-map-equiv e)

  double-negation-dense-map-inv-equiv : B ≃ A → A ↠¬¬ B
  double-negation-dense-map-inv-equiv e =
    double-negation-dense-map-equiv (inv-equiv e)
```

### The identity function is dense

```agda
module _
  {l : Level} {A : UU l}
  where

  is-double-negation-dense-map-id : is-double-negation-dense-map (id {A = A})
  is-double-negation-dense-map-id a = intro-double-negation (a , refl)
```

### A (k+1)-connected map is dense

```agda
is-double-negation-dense-map-is-connected-map :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  {f : A → B} → is-connected-map (succ-𝕋 k) f →
  is-double-negation-dense-map f
is-double-negation-dense-map-is-connected-map k H =
  is-double-negation-dense-map-is-surjective
    ( is-surjective-is-connected-map k H)
```

### Maps which are homotopic to dense maps are dense

```agda
module _
  { l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-double-negation-dense-map-htpy :
      {f g : A → B} → f ~ g →
      is-double-negation-dense-map g → is-double-negation-dense-map f
    is-double-negation-dense-map-htpy {f} {g} H K b =
      map-double-negation (map-equiv-fiber-htpy H b) (K b)

  abstract
    is-double-negation-dense-map-htpy' :
      {f g : A → B} → f ~ g →
      is-double-negation-dense-map f → is-double-negation-dense-map g
    is-double-negation-dense-map-htpy' H =
      is-double-negation-dense-map-htpy (inv-htpy H)
```

### A map that is both dense and a double negation stable embedding is an equivalence

```agda
abstract
  is-equiv-is-double-negation-stable-emb-is-double-negation-dense-map :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-double-negation-dense-map f →
    is-double-negation-stable-emb f →
    is-equiv f
  is-equiv-is-double-negation-stable-emb-is-double-negation-dense-map H K =
    is-equiv-is-contr-map
      ( λ y →
        is-proof-irrelevant-is-prop
          ( is-prop-map-is-double-negation-stable-emb K y)
          ( is-double-negation-eliminating-map-is-double-negation-stable-emb K y
            ( H y)))
```

### The composite of dense maps is dense

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  is-double-negation-dense-map-comp :
    {g : B → X} {h : A → B} →
    is-double-negation-dense-map g →
    is-double-negation-dense-map h →
    is-double-negation-dense-map (g ∘ h)
  is-double-negation-dense-map-comp {g} {h} G H x =
    map-double-negation
      ( map-inv-compute-fiber-comp g h x)
      ( is-irrefutable-Σ (G x) (H ∘ pr1))

  is-double-negation-dense-map-left-map-triangle :
    (f : A → X) (g : B → X) (h : A → B) → f ~ g ∘ h →
    is-double-negation-dense-map g →
    is-double-negation-dense-map h →
    is-double-negation-dense-map f
  is-double-negation-dense-map-left-map-triangle f g h K G H =
    is-double-negation-dense-map-htpy K (is-double-negation-dense-map-comp G H)

  comp-double-negation-dense-map : B ↠¬¬ X → A ↠¬¬ B → A ↠¬¬ X
  comp-double-negation-dense-map (g , G) (h , H) =
    ( g ∘ h , is-double-negation-dense-map-comp G H)
```

### Functoriality of products preserves being dense

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  is-double-negation-dense-map-product :
    {f : A → C} {g : B → D} →
    is-double-negation-dense-map f →
    is-double-negation-dense-map g →
    is-double-negation-dense-map (map-product f g)
  is-double-negation-dense-map-product {f} {g} F G (c , d) =
    map-double-negation
      ( map-inv-compute-fiber-map-product f g (c , d))
      ( is-irrefutable-product (F c) (G d))

  double-negation-dense-map-product :
    (A ↠¬¬ C) → (B ↠¬¬ D) → ((A × B) ↠¬¬ (C × D))
  double-negation-dense-map-product f g =
    map-product
      ( map-double-negation-dense-map f)
      ( map-double-negation-dense-map g) ,
    is-double-negation-dense-map-product
      ( is-double-negation-dense-map-double-negation-dense-map f)
      ( is-double-negation-dense-map-double-negation-dense-map g)
```

### The composite of a surjective map before an equivalence is dense

```agda
is-double-negation-dense-map-left-comp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (e : B ≃ C) {f : A → B} →
  is-double-negation-dense-map f →
  is-double-negation-dense-map (map-equiv e ∘ f)
is-double-negation-dense-map-left-comp-equiv e =
  is-double-negation-dense-map-comp (is-double-negation-dense-map-equiv e)
```

### The composite of a surjective map after an equivalence is dense

```agda
is-double-negation-dense-map-right-comp-equiv :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : B → C} →
  is-double-negation-dense-map f →
  (e : A ≃ B) →
  is-double-negation-dense-map (f ∘ map-equiv e)
is-double-negation-dense-map-right-comp-equiv H e =
  is-double-negation-dense-map-comp H (is-double-negation-dense-map-equiv e)
```

### If a composite is dense, then so is its left factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  is-double-negation-dense-map-left-factor :
    {g : B → X} (h : A → B) →
    is-double-negation-dense-map (g ∘ h) → is-double-negation-dense-map g
  is-double-negation-dense-map-left-factor {g} h GH x =
    map-double-negation (pr1 ∘ map-compute-fiber-comp g h x) (GH x)

  is-double-negation-dense-map-right-map-triangle' :
    (f : A → X) (g : B → X) (h : A → B) → g ∘ h ~ f →
    is-double-negation-dense-map f → is-double-negation-dense-map g
  is-double-negation-dense-map-right-map-triangle' f g h K F =
    is-double-negation-dense-map-left-factor h
      ( is-double-negation-dense-map-htpy K F)

  is-double-negation-dense-map-right-map-triangle :
    (f : A → X) (g : B → X) (h : A → B) → f ~ g ∘ h →
    is-double-negation-dense-map f → is-double-negation-dense-map g
  is-double-negation-dense-map-right-map-triangle f g h K =
    is-double-negation-dense-map-right-map-triangle' f g h (inv-htpy K)
```

### Characterization of the identity type of `A ↠¬¬ B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A ↠¬¬ B)
  where

  htpy-double-negation-dense-map : (A ↠¬¬ B) → UU (l1 ⊔ l2)
  htpy-double-negation-dense-map g =
    map-double-negation-dense-map f ~ map-double-negation-dense-map g

  refl-htpy-double-negation-dense-map : htpy-double-negation-dense-map f
  refl-htpy-double-negation-dense-map = refl-htpy

  is-torsorial-htpy-double-negation-dense-map :
    is-torsorial htpy-double-negation-dense-map
  is-torsorial-htpy-double-negation-dense-map =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy (map-double-negation-dense-map f))
      ( is-prop-is-double-negation-dense-map)
      ( map-double-negation-dense-map f)
      ( refl-htpy)
      ( is-double-negation-dense-map-double-negation-dense-map f)

  htpy-eq-double-negation-dense-map :
    (g : A ↠¬¬ B) → (f ＝ g) → htpy-double-negation-dense-map g
  htpy-eq-double-negation-dense-map .f refl =
    refl-htpy-double-negation-dense-map

  is-equiv-htpy-eq-double-negation-dense-map :
    (g : A ↠¬¬ B) → is-equiv (htpy-eq-double-negation-dense-map g)
  is-equiv-htpy-eq-double-negation-dense-map =
    fundamental-theorem-id
      is-torsorial-htpy-double-negation-dense-map
      htpy-eq-double-negation-dense-map

  extensionality-double-negation-dense-map :
    (g : A ↠¬¬ B) → (f ＝ g) ≃ htpy-double-negation-dense-map g
  extensionality-double-negation-dense-map g =
    ( htpy-eq-double-negation-dense-map g ,
    is-equiv-htpy-eq-double-negation-dense-map g)

  eq-htpy-double-negation-dense-map :
    (g : A ↠¬¬ B) → htpy-double-negation-dense-map g → f ＝ g
  eq-htpy-double-negation-dense-map g =
    map-inv-equiv (extensionality-double-negation-dense-map g)
```

### Characterization of the identity type of `Double-Negation-Dense-Map l2 A`

```agda
equiv-Double-Negation-Dense-Map :
  {l1 l2 l3 : Level} {A : UU l1} →
  Double-Negation-Dense-Map l2 A →
  Double-Negation-Dense-Map l3 A →
  UU (l1 ⊔ l2 ⊔ l3)
equiv-Double-Negation-Dense-Map f g =
  Σ ( type-Double-Negation-Dense-Map f ≃
      type-Double-Negation-Dense-Map g)
    ( λ e →
      map-equiv e ∘ map-Double-Negation-Dense-Map f ~
      map-Double-Negation-Dense-Map g)

module _
  {l1 l2 : Level} {A : UU l1} (f : Double-Negation-Dense-Map l2 A)
  where

  id-equiv-Double-Negation-Dense-Map : equiv-Double-Negation-Dense-Map f f
  pr1 id-equiv-Double-Negation-Dense-Map = id-equiv
  pr2 id-equiv-Double-Negation-Dense-Map = refl-htpy

  is-torsorial-equiv-Double-Negation-Dense-Map :
    is-torsorial (equiv-Double-Negation-Dense-Map f)
  is-torsorial-equiv-Double-Negation-Dense-Map =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv (type-Double-Negation-Dense-Map f))
      ( type-Double-Negation-Dense-Map f , id-equiv)
      ( is-torsorial-htpy-double-negation-dense-map
        ( double-negation-dense-map-Double-Negation-Dense-Map f))

  equiv-eq-Double-Negation-Dense-Map :
    (g : Double-Negation-Dense-Map l2 A) →
    f ＝ g → equiv-Double-Negation-Dense-Map f g
  equiv-eq-Double-Negation-Dense-Map .f refl =
    id-equiv-Double-Negation-Dense-Map

  is-equiv-equiv-eq-Double-Negation-Dense-Map :
    (g : Double-Negation-Dense-Map l2 A) →
    is-equiv (equiv-eq-Double-Negation-Dense-Map g)
  is-equiv-equiv-eq-Double-Negation-Dense-Map =
    fundamental-theorem-id
      is-torsorial-equiv-Double-Negation-Dense-Map
      equiv-eq-Double-Negation-Dense-Map

  extensionality-Double-Negation-Dense-Map :
    (g : Double-Negation-Dense-Map l2 A) →
    (f ＝ g) ≃ equiv-Double-Negation-Dense-Map f g
  pr1 (extensionality-Double-Negation-Dense-Map g) =
    equiv-eq-Double-Negation-Dense-Map g
  pr2 (extensionality-Double-Negation-Dense-Map g) =
    is-equiv-equiv-eq-Double-Negation-Dense-Map g

  eq-equiv-Double-Negation-Dense-Map :
    (g : Double-Negation-Dense-Map l2 A) →
    equiv-Double-Negation-Dense-Map f g → f ＝ g
  eq-equiv-Double-Negation-Dense-Map g =
    map-inv-equiv (extensionality-Double-Negation-Dense-Map g)
```

### Postcomposition of extensions along dense maps by a double negation stable embedding is an equivalence

```text
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  is-double-negation-dense-map-postcomp-extension-surjective-map :
    (f : A → B) (i : A → X) (g : X → Y) →
    is-double-negation-dense-map f → is-double-negation-stable-emb g →
    is-double-negation-dense-map (postcomp-extension f i g)
  is-double-negation-dense-map-postcomp-extension-surjective-map f i g H K (h , L) =
    intro-double-negation
      ( ( j , N) ,
        ( eq-htpy-extension f
          ( g ∘ i)
          ( postcomp-extension f i g (j , N))
          ( h , L)
          ( M)
          ( λ a →
            ( ap
              ( concat' (g (i a)) (M (f a)))
              ( is-section-map-inv-is-equiv
                ( K (i a) (j (f a)))
                ( L a ∙ inv (M (f a))))) ∙
            ( is-section-inv-concat' (M (f a)) (L a)))))
    where

    J : (b : B) → fiber g (h b)
    J =
      apply-dependent-universal-property-double-negation-dense-map-is-double-negation-dense-map f H
        ( λ b → fiber-emb-Prop (g , K) (h b))
        ( λ a → (i a , L a))

    j : B → X
    j b = pr1 (J b)

    M : (g ∘ j) ~ h
    M b = pr2 (J b)

    N : i ~ (j ∘ f)
    N a = map-inv-is-equiv (K (i a) (j (f a))) (L a ∙ inv (M (f a)))

  is-equiv-postcomp-extension-is-double-negation-dense-map :
    (f : A → B) (i : A → X) (g : X → Y) →
    is-double-negation-dense-map f → is-double-negation-stable-emb g →
    is-equiv (postcomp-extension f i g)
  is-equiv-postcomp-extension-is-double-negation-dense-map f i g H K =
    is-equiv-is-double-negation-stable-emb-is-double-negation-dense-map
      ( is-double-negation-dense-map-postcomp-extension-surjective-map f i g H K)
      ( is-double-negation-stable-emb-postcomp-extension f i g K)

  equiv-postcomp-extension-double-negation-dense-map :
    (f : A ↠¬¬ B) (i : A → X) (g : X ↪¬¬ Y) →
    extension (map-double-negation-dense-map f) i ≃
    extension (map-double-negation-dense-map f) (map-double-negation-stable-emb g ∘ i)
  pr1 (equiv-postcomp-extension-double-negation-dense-map f i g) =
    postcomp-extension (map-double-negation-dense-map f) i (map-double-negation-stable-emb g)
  pr2 (equiv-postcomp-extension-double-negation-dense-map f i g) =
    is-equiv-postcomp-extension-is-double-negation-dense-map
      ( map-double-negation-dense-map f)
      ( i)
      ( map-double-negation-stable-emb g)
      ( is-double-negation-dense-map-double-negation-dense-map f)
      ( is-double-negation-stable-emb-map-double-negation-stable-emb g)
```

### Every type that maps double negation densely onto an irrefutable type is irrefutable

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-irrefutable-is-double-negation-dense-map :
    {f : A → B} → is-double-negation-dense-map f → ¬¬ B → ¬¬ A
  is-irrefutable-is-double-negation-dense-map F nnb na =
    nnb (λ b → F b (λ p → na (pr1 p)))

  is-irrefutable-double-negation-dense-map :
    A ↠¬¬ B → ¬¬ B → ¬¬ A
  is-irrefutable-double-negation-dense-map f =
    is-irrefutable-is-double-negation-dense-map
      ( is-double-negation-dense-map-double-negation-dense-map f)
```

### The type of double negation dense maps `A ↠¬¬ B` is equivalent to the type of families `P` of irrefutable types over `B` equipped with an equivalence `A ≃ Σ B P`

> This remains to be shown.

## External links

- [TypeTopology.Density](https://martinescardo.github.io/TypeTopology/TypeTopology.Density.html)
  at TypeTopology
