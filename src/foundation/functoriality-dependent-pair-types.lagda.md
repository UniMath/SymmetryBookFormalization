# Functoriality of dependent pair types

```agda
module foundation.functoriality-dependent-pair-types where

open import foundation-core.functoriality-dependent-pair-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-homotopies
open import foundation.dependent-pair-types
open import foundation.morphisms-arrows
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-maps
open import foundation-core.dependent-identifications
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositional-maps
open import foundation-core.retracts-of-types
open import foundation-core.sections
open import foundation-core.transport-along-identifications
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Properties

### The map `htpy-map-Σ` preserves homotopies

Given a [homotopy](foundation.homotopies.md) `H : f ~ f'` and a family of
[dependent homotopies](foundation.dependent-homotopies.md) `K a : g a ~ g' a`
over `H`, expressed as
[commuting triangles](foundation.commuting-triangles-of-maps.md)

```text
        g a
   C a -----> D (f a)
      \      /
  g' a \    / tr D (H a)
        ∨  ∨
      D (f' a)         ,
```

we get a homotopy `htpy-map-Σ H K : map-Σ f g ~ map-Σ f' g'`.

This assignment itself preserves homotopies: given `H` and `K` as above,
`H' : f ~ f'` with `K' a : g a ~ g' a` over `H'`, we would like to express
coherences between the pairs `H, H'` and `K, K'` which would ensure
`htpy-map-Σ H K ~ htpy-map-Σ H' K'`. Because `H` and `H'` have the same type, we
may require a homotopy `α : H ~ H'`, but `K` and `K'` are families of dependent
homotopies over different homotopies, so their coherence is provided as a family
of
[commuting triangles of identifications](foundation.commuting-triangles-of-identifications.md)

```text
                      ap (λ p → tr D p (g a c)) (α a)
  tr D (H a) (g a c) --------------------------------- tr D (H' a) (g a c)
                     \                               /
                        \                         /
                           \                   /
                      K a c   \             /   K' a c
                                 \       /
                                    \ /
                                  g' a c        .
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} (D : B → UU l4)
  {f f' : A → B} {H H' : f ~ f'}
  {g : (a : A) → C a → D (f a)}
  {g' : (a : A) → C a → D (f' a)}
  {K : (a : A) → dependent-homotopy (λ _ → D) (λ _ → H a) (g a) (g' a)}
  {K' : (a : A) → dependent-homotopy (λ _ → D) (λ _ → H' a) (g a) (g' a)}
  where

  abstract
    htpy-htpy-map-Σ :
      (α : H ~ H') →
      (β :
        (a : A) (c : C a) →
        K a c ＝ ap (λ p → tr D p (g a c)) (α a) ∙ K' a c) →
      htpy-map-Σ D H g K ~ htpy-map-Σ D H' g K'
    htpy-htpy-map-Σ α β (a , c) =
      ap
        ( eq-pair-Σ')
        ( eq-pair-Σ
          ( α a)
          ( map-compute-dependent-identification-eq-value-function
            ( λ p → tr D p (g a c))
            ( λ _ → g' a c)
            ( α a)
            ( K a c)
            ( K' a c)
            ( inv
              ( ( ap
                  ( K a c ∙_)
                  ( ap-const (g' a c) (α a))) ∙
                ( right-unit) ∙
                ( β a c)))))
```

As a corollary of the above statement, we can provide a condition which
guarantees that `htpy-map-Σ` is homotopic to the trivial homotopy.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} (D : B → UU l4)
  {f : A → B} {H : f ~ f}
  {g : (a : A) → C a → D (f a)}
  {K : (a : A) → tr D (H a) ∘ g a ~ g a}
  where

  abstract
    htpy-htpy-map-Σ-refl-htpy :
      (α : H ~ refl-htpy) →
      (β : (a : A) (c : C a) → K a c ＝ ap (λ p → tr D p (g a c)) (α a)) →
      htpy-map-Σ D H g K ~ refl-htpy
    htpy-htpy-map-Σ-refl-htpy α β =
      htpy-htpy-map-Σ D α (λ a c → β a c ∙ inv right-unit)
```

### The map on total spaces induced by a family of truncated maps is truncated

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f : (x : A) → B x → C x}
  where

  abstract
    is-trunc-map-tot : ((x : A) → is-trunc-map k (f x)) → is-trunc-map k (tot f)
    is-trunc-map-tot H y =
      is-trunc-equiv k
        ( fiber (f (pr1 y)) (pr2 y))
        ( compute-fiber-tot f y)
        ( H (pr1 y) (pr2 y))

  abstract
    is-trunc-map-is-trunc-map-tot :
      is-trunc-map k (tot f) → ((x : A) → is-trunc-map k (f x))
    is-trunc-map-is-trunc-map-tot is-trunc-tot-f x z =
      is-trunc-equiv k
        ( fiber (tot f) (x , z))
        ( inv-compute-fiber-tot f (x , z))
        ( is-trunc-tot-f (x , z))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f : (x : A) → B x → C x}
  where

  abstract
    is-contr-map-tot :
      ((x : A) → is-contr-map (f x)) → is-contr-map (tot f)
    is-contr-map-tot =
      is-trunc-map-tot neg-two-𝕋

  abstract
    is-prop-map-tot : ((x : A) → is-prop-map (f x)) → is-prop-map (tot f)
    is-prop-map-tot = is-trunc-map-tot neg-one-𝕋
```

### The functoriality of dependent pair types preserves truncatedness

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-trunc-map-map-Σ-map-base :
      (k : 𝕋) {f : A → B} (C : B → UU l3) →
      is-trunc-map k f → is-trunc-map k (map-Σ-map-base f C)
    is-trunc-map-map-Σ-map-base k {f} C H y =
      is-trunc-equiv' k
        ( fiber f (pr1 y))
        ( compute-fiber-map-Σ-map-base f C y)
        ( H (pr1 y))

  abstract
    is-prop-map-map-Σ-map-base :
      {f : A → B} (C : B → UU l3) →
      is-prop-map f → is-prop-map (map-Σ-map-base f C)
    is-prop-map-map-Σ-map-base C = is-trunc-map-map-Σ-map-base neg-one-𝕋 C

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  where

  abstract
    is-trunc-map-map-Σ :
      (k : 𝕋) (D : B → UU l4) {f : A → B} {g : (x : A) → C x → D (f x)} →
      is-trunc-map k f → ((x : A) → is-trunc-map k (g x)) →
      is-trunc-map k (map-Σ D f g)
    is-trunc-map-map-Σ k D {f} {g} H K =
      is-trunc-map-left-map-triangle k
        ( map-Σ D f g)
        ( map-Σ-map-base f D)
        ( tot g)
        ( triangle-map-Σ D f g)
        ( is-trunc-map-map-Σ-map-base k D H)
        ( is-trunc-map-tot k K)

  module _
    (D : B → UU l4) {f : A → B} {g : (x : A) → C x → D (f x)}
    where

    abstract
      is-contr-map-map-Σ :
        is-contr-map f → ((x : A) → is-contr-map (g x)) →
        is-contr-map (map-Σ D f g)
      is-contr-map-map-Σ = is-trunc-map-map-Σ neg-two-𝕋 D

    abstract
      is-prop-map-map-Σ :
        is-prop-map f → ((x : A) → is-prop-map (g x)) →
        is-prop-map (map-Σ D f g)
      is-prop-map-map-Σ = is-trunc-map-map-Σ neg-one-𝕋 D
```

### Commuting squares of maps on total spaces

#### Functoriality of `Σ` preserves commuting squares of maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {A : UU l1} {P : A → UU l2}
  {B : UU l3} {Q : B → UU l4}
  {C : UU l5} {R : C → UU l6}
  {D : UU l7} (S : D → UU l8)
  {top' : A → C} {left' : A → B} {right' : C → D} {bottom' : B → D}
  (top : (a : A) → P a → R (top' a))
  (left : (a : A) → P a → Q (left' a))
  (right : (c : C) → R c → S (right' c))
  (bottom : (b : B) → Q b → S (bottom' b))
  where

  coherence-square-maps-Σ :
    {H' : coherence-square-maps top' left' right' bottom'} →
    ( (a : A) (p : P a) →
      dependent-identification S
        ( H' a)
        ( bottom _ (left _ p))
        ( right _ (top _ p))) →
    coherence-square-maps
      ( map-Σ R top' top)
      ( map-Σ Q left' left)
      ( map-Σ S right' right)
      ( map-Σ S bottom' bottom)
  coherence-square-maps-Σ {H'} H (a , p) = eq-pair-Σ (H' a) (H a p)
```

#### Commuting squares of induced maps on total spaces

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {P : A → UU l2} {Q : A → UU l3} {R : A → UU l4} {S : A → UU l5}
  (top : (a : A) → P a → R a)
  (left : (a : A) → P a → Q a)
  (right : (a : A) → R a → S a)
  (bottom : (a : A) → Q a → S a)
  where

  coherence-square-maps-tot :
    ((a : A) → coherence-square-maps (top a) (left a) (right a) (bottom a)) →
    coherence-square-maps (tot top) (tot left) (tot right) (tot bottom)
  coherence-square-maps-tot H (a , p) = eq-pair-eq-fiber (H a p)
```

#### `map-Σ-map-base` preserves commuting squares of maps

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} (S : D → UU l5)
  (top : A → C) (left : A → B) (right : C → D) (bottom : B → D)
  where

  coherence-square-maps-map-Σ-map-base :
    (H : coherence-square-maps top left right bottom) →
    coherence-square-maps
      ( map-Σ (S ∘ right) top (λ a → tr S (H a)))
      ( map-Σ-map-base left (S ∘ bottom))
      ( map-Σ-map-base right S)
      ( map-Σ-map-base bottom S)
  coherence-square-maps-map-Σ-map-base H (a , p) = eq-pair-Σ (H a) refl
```

### Commuting triangles of maps on total spaces

#### Functoriality of `Σ` preserves commuting triangles of maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {P : A → UU l2}
  {B : UU l3} {Q : B → UU l4}
  {C : UU l5} (R : C → UU l6)
  {left' : A → C} {right' : B → C} {top' : A → B}
  (left : (a : A) → P a → R (left' a))
  (right : (b : B) → Q b → R (right' b))
  (top : (a : A) → P a → Q (top' a))
  where

  coherence-triangle-maps-Σ :
    {H' : coherence-triangle-maps left' right' top'} →
    ( (a : A) (p : P a) →
      dependent-identification R (H' a) (left _ p) (right _ (top _ p))) →
    coherence-triangle-maps
      ( map-Σ R left' left)
      ( map-Σ R right' right)
      ( map-Σ Q top' top)
  coherence-triangle-maps-Σ {H'} H (a , p) = eq-pair-Σ (H' a) (H a p)
```

#### `map-Σ-map-base` preserves commuting triangles of maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (S : X → UU l4)
  (left : A → X) (right : B → X) (top : A → B)
  where

  coherence-triangle-maps-map-Σ-map-base :
    (H : coherence-triangle-maps left right top) →
    coherence-triangle-maps
      ( map-Σ-map-base left S)
      ( map-Σ-map-base right S)
      ( map-Σ (S ∘ right) top (λ a → tr S (H a)))
  coherence-triangle-maps-map-Σ-map-base H (a , _) = eq-pair-Σ (H a) refl
```

### The action of `map-Σ-map-base` on identifications of the form `eq-pair-Σ` is given by the action on the base

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3)
  where

  compute-ap-map-Σ-map-base-eq-pair-Σ :
    { s s' : A} (p : s ＝ s') {t : C (f s)} {t' : C (f s')}
    ( q : tr (C ∘ f) p t ＝ t') →
    ap (map-Σ-map-base f C) (eq-pair-Σ p q) ＝
    eq-pair-Σ (ap f p) (substitution-law-tr C f p ∙ q)
  compute-ap-map-Σ-map-base-eq-pair-Σ refl refl = refl
```

### The action of `ind-Σ` on identifications in fibers of dependent pair types is given by the action of the fibers of the function with the first argument fixed

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} {B : A → UU l2} {C : UU l3}
  (f : (a : A) (b : B a) → C)
  where

  compute-ap-ind-Σ-eq-pair-eq-fiber :
    {a : A} {b b' : B a} (p : b ＝ b') →
    ap (ind-Σ f) (eq-pair-eq-fiber p) ＝ ap (f a) p
  compute-ap-ind-Σ-eq-pair-eq-fiber refl = refl
```

### Computing the inverse of `equiv-tot`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  compute-inv-equiv-tot :
    (e : (x : A) → B x ≃ C x) →
    map-inv-equiv (equiv-tot e) ~
    map-equiv (equiv-tot (λ x → inv-equiv (e x)))
  compute-inv-equiv-tot e (a , c) =
    is-injective-equiv
      ( equiv-tot e)
      ( ( is-section-map-inv-equiv (equiv-tot e) (a , c)) ∙
        ( eq-pair-eq-fiber (inv (is-section-map-inv-equiv (e a) c))))
```

### If every fiber has an element then the base is a retract of the dependent sum

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  section-pr1-section : ((x : A) → B x) → section (pr1 {A = A} {B})
  section-pr1-section f = ((λ x → (x , f x)) , refl-htpy)

  retract-base-Σ-section-family : ((x : A) → B x) → A retract-of (Σ A B)
  retract-base-Σ-section-family f = retract-section pr1 (section-pr1-section f)
```

### Dependent sums of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {I : UU l5} {A : I → UU l1} {B : I → UU l2} {X : I → UU l3} {Y : I → UU l4}
  (f : (i : I) → A i → B i) (g : (i : I) → X i → Y i)
  (α : (i : I) → hom-arrow (f i) (g i))
  where

  tot-hom-arrow : hom-arrow (tot f) (tot g)
  pr1 tot-hom-arrow =
    tot (λ i → map-domain-hom-arrow (f i) (g i) (α i))
  pr1 (pr2 tot-hom-arrow) =
    tot (λ i → map-codomain-hom-arrow (f i) (g i) (α i))
  pr2 (pr2 tot-hom-arrow) =
    tot-htpy (λ i → coh-hom-arrow (f i) (g i) (α i))
```

## See also

- Arithmetical laws involving dependent pair types are recorded in
  [`foundation.type-arithmetic-dependent-pair-types`](foundation.type-arithmetic-dependent-pair-types.md).
- Equality proofs in dependent pair types are characterized in
  [`foundation.equality-dependent-pair-types`](foundation.equality-dependent-pair-types.md).
- The universal property of dependent pair types is treated in
  [`foundation.universal-property-dependent-pair-types`](foundation.universal-property-dependent-pair-types.md).
- Functorial properties of cartesian product types are recorded in
  [`foundation.functoriality-cartesian-product-types`](foundation.functoriality-cartesian-product-types.md).
- Functorial properties of dependent product types are recorded in
  [`foundation.functoriality-dependent-function-types`](foundation.functoriality-dependent-function-types.md).
