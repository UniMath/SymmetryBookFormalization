# Embeddings

```agda
module foundation.embeddings where

open import foundation-core.embeddings public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.truncated-maps
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.commuting-squares-of-maps
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.pullbacks
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.torsorial-type-families
open import foundation-core.truncation-levels
```

</details>

## Properties

### Being an embedding is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-property-is-emb : (f : A → B) → is-prop (is-emb f)
  is-property-is-emb f =
    is-prop-Π (λ x → is-prop-Π (λ y → is-property-is-equiv (ap f)))

  is-emb-Prop : (A → B) → Prop (l1 ⊔ l2)
  pr1 (is-emb-Prop f) = is-emb f
  pr2 (is-emb-Prop f) = is-property-is-emb f
```

### Embeddings are closed under homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-emb-htpy : {f g : A → B} (H : f ~ g) → is-emb g → is-emb f
    is-emb-htpy {f} {g} H is-emb-g x y =
      is-equiv-top-is-equiv-left-square
        ( ap g)
        ( concat' (f x) (H y))
        ( ap f)
        ( concat (H x) (g y))
        ( nat-htpy H)
        ( is-equiv-concat (H x) (g y))
        ( is-emb-g x y)
        ( is-equiv-concat' (f x) (H y))

  is-emb-htpy-emb : {f : A → B} (e : A ↪ B) → f ~ map-emb e → is-emb f
  is-emb-htpy-emb e H = is-emb-htpy H (is-emb-map-emb e)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-emb-htpy' : {f g : A → B} (H : f ~ g) → is-emb f → is-emb g
    is-emb-htpy' H is-emb-f = is-emb-htpy (inv-htpy H) is-emb-f

  is-emb-htpy-emb' : (e : A ↪ B) {g : A → B} → map-emb e ~ g → is-emb g
  is-emb-htpy-emb' e H = is-emb-htpy' H (is-emb-map-emb e)
```

### Any map between propositions is an embedding

```agda
is-emb-is-prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-prop A → is-prop B → is-emb f
is-emb-is-prop H K =
  is-emb-is-prop-map (is-trunc-map-is-trunc-domain-codomain neg-one-𝕋 H K)
```

### Embeddings are closed under composition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-emb-comp :
    (g : B → C) (h : A → B) → is-emb g → is-emb h → is-emb (g ∘ h)
  is-emb-comp g h is-emb-g is-emb-h x y =
    is-equiv-left-map-triangle
      ( ap (g ∘ h))
      ( ap g)
      ( ap h)
      ( ap-comp g h)
      ( is-emb-h x y)
      ( is-emb-g (h x) (h y))

  abstract
    is-emb-left-map-triangle :
      (f : A → C) (g : B → C) (h : A → B) (H : coherence-triangle-maps f g h) →
      is-emb g → is-emb h → is-emb f
    is-emb-left-map-triangle f g h H is-emb-g is-emb-h =
      is-emb-htpy H (is-emb-comp g h is-emb-g is-emb-h)

  comp-emb :
    (B ↪ C) → (A ↪ B) → (A ↪ C)
  pr1 (comp-emb (g , H) (f , K)) = g ∘ f
  pr2 (comp-emb (g , H) (f , K)) = is-emb-comp g f H K
```

### The right factor of a composed embedding is an embedding

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-emb-right-factor :
    (g : B → C) (h : A → B) →
    is-emb g → is-emb (g ∘ h) → is-emb h
  is-emb-right-factor g h is-emb-g is-emb-gh x y =
    is-equiv-top-map-triangle
      ( ap (g ∘ h))
      ( ap g)
      ( ap h)
      ( ap-comp g h)
      ( is-emb-g (h x) (h y))
      ( is-emb-gh x y)

  abstract
    is-emb-top-map-triangle :
      (f : A → C) (g : B → C) (h : A → B) (H : coherence-triangle-maps f g h) →
      is-emb g → is-emb f → is-emb h
    is-emb-top-map-triangle f g h H is-emb-g is-emb-f x y =
      is-equiv-top-map-triangle
        ( ap (g ∘ h))
        ( ap g)
        ( ap h)
        ( ap-comp g h)
        ( is-emb-g (h x) (h y))
        ( is-emb-htpy (inv-htpy H) is-emb-f x y)

  abstract
    is-emb-triangle-is-equiv :
      (f : A → C) (g : B → C) (e : A → B) (H : coherence-triangle-maps f g e) →
      is-equiv e → is-emb g → is-emb f
    is-emb-triangle-is-equiv f g e H is-equiv-e is-emb-g =
      is-emb-left-map-triangle f g e H is-emb-g (is-emb-is-equiv is-equiv-e)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  abstract
    is-emb-triangle-is-equiv' :
      (f : A → C) (g : B → C) (e : A → B) (H : coherence-triangle-maps f g e) →
      is-equiv e → is-emb f → is-emb g
    is-emb-triangle-is-equiv' f g e H is-equiv-e is-emb-f =
      is-emb-triangle-is-equiv g f
        ( map-inv-is-equiv is-equiv-e)
        ( triangle-section f g e H
          ( pair
            ( map-inv-is-equiv is-equiv-e)
            ( is-section-map-inv-is-equiv is-equiv-e)))
        ( is-equiv-map-inv-is-equiv is-equiv-e)
        ( is-emb-f)
```

### The map on total spaces induced by a family of embeddings is an embedding

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  is-emb-tot :
    {f : (x : A) → B x → C x} → ((x : A) → is-emb (f x)) → is-emb (tot f)
  is-emb-tot H =
    is-emb-is-prop-map (is-prop-map-tot (λ x → is-prop-map-is-emb (H x)))

  emb-tot : ((x : A) → B x ↪ C x) → Σ A B ↪ Σ A C
  pr1 (emb-tot f) = tot (λ x → map-emb (f x))
  pr2 (emb-tot f) = is-emb-tot (λ x → is-emb-map-emb (f x))
```

### The functoriality of dependent pair types preserves embeddings

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-emb-map-Σ-map-base :
      {f : A → B} (C : B → UU l3) → is-emb f → is-emb (map-Σ-map-base f C)
    is-emb-map-Σ-map-base C H =
      is-emb-is-prop-map (is-prop-map-map-Σ-map-base C (is-prop-map-is-emb H))

  emb-Σ-emb-base :
    (f : A ↪ B) (C : B → UU l3) → Σ A (λ a → C (map-emb f a)) ↪ Σ B C
  pr1 (emb-Σ-emb-base f C) = map-Σ-map-base (map-emb f) C
  pr2 (emb-Σ-emb-base f C) =
    is-emb-map-Σ-map-base C (is-emb-map-emb f)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  where

  is-emb-map-Σ :
    (D : B → UU l4) {f : A → B} {g : (x : A) → C x → D (f x)} →
    is-emb f → ((x : A) → is-emb (g x)) → is-emb (map-Σ D f g)
  is-emb-map-Σ D H K =
    is-emb-is-prop-map
      ( is-prop-map-map-Σ D
        ( is-prop-map-is-emb H)
        ( λ x → is-prop-map-is-emb (K x)))

  emb-Σ :
    (D : B → UU l4) (f : A ↪ B) (g : (x : A) → C x ↪ D (map-emb f x)) →
    Σ A C ↪ Σ B D
  pr1 (emb-Σ D f g) = map-Σ D (map-emb f) (λ x → map-emb (g x))
  pr2 (emb-Σ D f g) =
    is-emb-map-Σ D (is-emb-map-emb f) (λ x → is-emb-map-emb (g x))
```

### Equivalence on total spaces induced by embedding on the base types

We saw above that given an embedding `f : A ↪ B` and a type family `C` over `B`
we obtain an embedding

```text
  Σ A (C ∘ f) ↪ Σ B C.
```

This embedding can be upgraded to an equivalence if we furthermore know that the
support of `C` is contained in the image of `f`. More precisely, if we are given
a section `((b , c) : Σ B C) → fiber f b`, then it follows that

```text
  Σ A (C ∘ f) ≃ Σ B C.
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : B → UU l3} (f : A ↪ B)
  (H : ((b , c) : Σ B C) → fiber (map-emb f) b)
  where

  map-inv-Σ-emb-base : Σ B C → Σ A (C ∘ map-emb f)
  pr1 (map-inv-Σ-emb-base u) = pr1 (H u)
  pr2 (map-inv-Σ-emb-base u) = inv-tr C (pr2 (H u)) (pr2 u)

  is-section-map-inv-Σ-emb-base :
    is-section (map-Σ-map-base (map-emb f) C) map-inv-Σ-emb-base
  is-section-map-inv-Σ-emb-base (b , c) =
    ap
      ( λ s → (pr1 s , inv-tr C (pr2 s) c))
      ( eq-is-contr (is-torsorial-Id' b))

  is-retraction-map-inv-Σ-emb-base :
    is-retraction (map-Σ-map-base (map-emb f) C) map-inv-Σ-emb-base
  is-retraction-map-inv-Σ-emb-base (a , c) =
    ap
      ( λ s → (pr1 s , inv-tr C (pr2 s) c))
      ( eq-is-prop (is-prop-map-is-emb (pr2 f) (map-emb f a)))

  equiv-Σ-emb-base : Σ A (C ∘ map-emb f) ≃ Σ B C
  pr1 equiv-Σ-emb-base = map-Σ-map-base (map-emb f) C
  pr2 equiv-Σ-emb-base =
    is-equiv-is-invertible
      map-inv-Σ-emb-base
      is-section-map-inv-Σ-emb-base
      is-retraction-map-inv-Σ-emb-base
```

### The product of two embeddings is an embedding

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  emb-product : (A ↪ C) → (B ↪ D) → ((A × B) ↪ (C × D))
  emb-product f g = emb-Σ (λ _ → D) f (λ _ → g)

  is-emb-map-product :
    {f : A → C} {g : B → D} → is-emb f → is-emb g → (is-emb (map-product f g))
  is-emb-map-product {f} {g} is-emb-f is-emb-g =
    is-emb-map-emb (emb-product (f , is-emb-f) (g , is-emb-g))
```

### If the action on identifications has a section, then `f` is an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-emb-section-ap :
      ((x y : A) → section (ap f {x} {y})) → is-emb f
    is-emb-section-ap section-ap-f x =
      fundamental-theorem-id-section x (λ y → ap f) (section-ap-f x)
```

### If there is an equivalence `(f x = f y) ≃ (x = y)` that sends `refl` to `refl`, then f is an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-emb-equiv-refl-to-refl :
      (e : (x y : A) → (f x ＝ f y) ≃ (x ＝ y)) →
      ((x : A) → map-equiv (e x x) refl ＝ refl) →
      is-emb f
    is-emb-equiv-refl-to-refl e p x y =
      is-equiv-htpy-equiv
        ( inv-equiv (e x y))
        ( λ where
          refl →
            inv (is-retraction-map-inv-equiv (e x x) refl) ∙
            ap (map-equiv (inv-equiv (e x x))) (p x))
```

### Embeddings are closed under pullback

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  abstract
    is-emb-vertical-map-cone-is-pullback :
      is-pullback f g c → is-emb g → is-emb (vertical-map-cone f g c)
    is-emb-vertical-map-cone-is-pullback pb is-emb-g =
      is-emb-is-prop-map
        ( is-trunc-vertical-map-is-pullback neg-one-𝕋 f g c pb
          ( is-prop-map-is-emb is-emb-g))

  abstract
    is-emb-horizontal-map-cone-is-pullback :
      is-pullback f g c → is-emb f → is-emb (horizontal-map-cone f g c)
    is-emb-horizontal-map-cone-is-pullback pb is-emb-f =
      is-emb-is-prop-map
        ( is-trunc-horizontal-map-is-pullback neg-one-𝕋 f g c pb
          ( is-prop-map-is-emb is-emb-f))
```

### In a commuting square of which the sides are embeddings, the top map is an embedding if and only if the bottom map is an embedding

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (top : A → C) (left : A → B) (right : C → D) (bottom : B → D)
  (H : coherence-square-maps top left right bottom)
  where

  is-emb-top-is-emb-bottom-is-equiv-coherence-square-maps :
    is-equiv left → is-equiv right → is-emb bottom → is-emb top
  is-emb-top-is-emb-bottom-is-equiv-coherence-square-maps K L M =
    is-emb-right-factor
      ( right)
      ( top)
      ( is-emb-is-equiv L)
      ( is-emb-htpy'
        ( H)
        ( is-emb-comp bottom left M (is-emb-is-equiv K)))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (top : A → C) (left : A → B) (right : C → D) (bottom : B → D)
  (H : coherence-square-maps top left right bottom)
  where

  is-emb-bottom-is-emb-top-is-equiv-coherence-square-maps :
    is-equiv left → is-equiv right → is-emb top → is-emb bottom
  is-emb-bottom-is-emb-top-is-equiv-coherence-square-maps K L M =
    is-emb-top-is-emb-bottom-is-equiv-coherence-square-maps
      ( bottom)
      ( map-inv-is-equiv K)
      ( map-inv-is-equiv L)
      ( top)
      ( vertical-inv-equiv-coherence-square-maps
        ( top)
        ( left , K)
        ( right , L)
        ( bottom)
        ( H))
      ( is-equiv-map-inv-is-equiv K)
      ( is-equiv-map-inv-is-equiv L)
      ( M)
```

### A map is an embedding if and only if it has contractible fibers at values

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-emb-is-contr-fibers-values' :
    ((a : A) → is-contr (fiber' f (f a))) → is-emb f
  is-emb-is-contr-fibers-values' c a =
    fundamental-theorem-id (c a) (λ x → ap f {a} {x})

  is-emb-is-contr-fibers-values :
    ((a : A) → is-contr (fiber f (f a))) → is-emb f
  is-emb-is-contr-fibers-values c =
    is-emb-is-contr-fibers-values'
      ( λ a →
        is-contr-equiv'
          ( fiber f (f a))
          ( equiv-fiber f (f a))
          ( c a))

  is-contr-fibers-values-is-emb' :
    is-emb f → ((a : A) → is-contr (fiber' f (f a)))
  is-contr-fibers-values-is-emb' e a =
    fundamental-theorem-id' (λ x → ap f {a} {x}) (e a)

  is-contr-fibers-values-is-emb :
    is-emb f → ((a : A) → is-contr (fiber f (f a)))
  is-contr-fibers-values-is-emb e a =
    is-contr-equiv
      ( fiber' f (f a))
      ( equiv-fiber f (f a))
      ( is-contr-fibers-values-is-emb' e a)
```

### A family of logical equivalences between the fibers of two embeddings into a type induces an equivalence between their domain types

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A ↪ X) (g : B ↪ X)
  (H : (x : X) → fiber (map-emb f) x ↔ fiber (map-emb g) x)
  where

  fam-equiv-logical-equiv-fiber-emb :
    (x : X) → fiber (map-emb f) x ≃ fiber (map-emb g) x
  fam-equiv-logical-equiv-fiber-emb x =
    equiv-iff
      ( fiber-emb-Prop f x)
      ( fiber-emb-Prop g x)
      ( forward-implication (H x))
      ( backward-implication (H x))

  equiv-domain-logical-equiv-fiber-emb :
    A ≃ B
  equiv-domain-logical-equiv-fiber-emb =
    equiv-total-fiber (map-emb g) ∘e
    equiv-tot fam-equiv-logical-equiv-fiber-emb ∘e
    inv-equiv-total-fiber (map-emb f)

  map-equiv-domain-logical-equiv-fiber-emb :
    A → B
  map-equiv-domain-logical-equiv-fiber-emb =
    map-equiv equiv-domain-logical-equiv-fiber-emb

  coherence-triangle-equiv-domain-logical-equiv-fiber-emb :
    coherence-triangle-maps
      ( map-emb f)
      ( map-emb g)
      ( map-equiv-domain-logical-equiv-fiber-emb)
  coherence-triangle-equiv-domain-logical-equiv-fiber-emb a =
    inv (pr2 (forward-implication (H (map-emb f a)) (a , refl)))
```

## See also

- [Propositional maps (core)](foundation-core.propositional-maps.md)
- [Propositional-maps](foundation.propositional-maps.md)
- [Subtype duality](foundation.subtype-duality.md)
