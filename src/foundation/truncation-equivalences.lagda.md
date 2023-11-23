# `k`-Equivalences

```agda
module foundation.truncation-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.connected-maps
open import foundation.connected-types
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-truncation
open import foundation.identity-types
open import foundation.truncations
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-truncation
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-function-types
open import foundation-core.homotopies
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

A map `f : A → B` is said to be a `k`-equivalence if the map
`map-trunc k f : trunc k A → trunc k B` is an equivalence.

## Definition

```agda
is-truncation-equivalence :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-truncation-equivalence k f = is-equiv (map-trunc k f)

truncation-equivalence :
  {l1 l2 : Level} (k : 𝕋) → UU l1 → UU l2 → UU (l1 ⊔ l2)
truncation-equivalence k A B = Σ (A → B) (is-truncation-equivalence k)

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  (f : truncation-equivalence k A B)
  where

  map-truncation-equivalence : A → B
  map-truncation-equivalence = pr1 f

  is-truncation-equivalence-truncation-equivalence :
    is-truncation-equivalence k map-truncation-equivalence
  is-truncation-equivalence-truncation-equivalence = pr2 f
```

## Properties

### A map `f : A → B` is a `k`-equivalence if and only if `- ∘ f : (B → X) → (A → X)` is an equivalence for every `k`-truncated type `X`

```agda
is-equiv-precomp-is-truncation-equivalence :
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
  is-truncation-equivalence k f →
  (X : Truncated-Type l3 k) → is-equiv (precomp f (type-Truncated-Type X))
is-equiv-precomp-is-truncation-equivalence k f H X =
  is-equiv-bottom-is-equiv-top-square
    ( precomp unit-trunc (type-Truncated-Type X))
    ( precomp unit-trunc (type-Truncated-Type X))
    ( precomp (map-trunc k f) (type-Truncated-Type X))
    ( precomp f (type-Truncated-Type X))
    ( precomp-coherence-square-maps
      ( unit-trunc)
      ( f)
      ( map-trunc k f)
      ( unit-trunc)
      ( inv-htpy (coherence-square-map-trunc k f))
      ( type-Truncated-Type X))
    ( is-truncation-trunc X)
    ( is-truncation-trunc X)
    ( is-equiv-precomp-is-equiv (map-trunc k f) H (type-Truncated-Type X))

is-truncation-equivalence-is-equiv-precomp :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
  ( (l : Level) (X : Truncated-Type l k) →
    is-equiv (precomp f (type-Truncated-Type X))) →
  is-truncation-equivalence k f
is-truncation-equivalence-is-equiv-precomp k {A} {B} f H =
  is-equiv-is-equiv-precomp-Truncated-Type k
    ( trunc k A)
    ( trunc k B)
    ( map-trunc k f)
    ( λ X →
      is-equiv-top-is-equiv-bottom-square
        ( precomp unit-trunc (type-Truncated-Type X))
        ( precomp unit-trunc (type-Truncated-Type X))
        ( precomp (map-trunc k f) (type-Truncated-Type X))
        ( precomp f (type-Truncated-Type X))
        ( precomp-coherence-square-maps
          ( unit-trunc)
          ( f)
          ( map-trunc k f)
          ( unit-trunc)
          ( inv-htpy (coherence-square-map-trunc k f))
          ( type-Truncated-Type X))
        ( is-truncation-trunc X)
        ( is-truncation-trunc X)
        ( H _ X))
```

### An equivalence is a `k`-equivalence for all `k`

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-truncation-equivalence-is-equiv :
    is-equiv f → is-truncation-equivalence k f
  is-truncation-equivalence-is-equiv e = is-equiv-map-equiv-trunc k (f , e)
```

### Every `k`-connected map is a `k`-equivalence

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-truncation-equivalence-is-connected-map :
    is-connected-map k f → is-truncation-equivalence k f
  is-truncation-equivalence-is-connected-map c =
    is-truncation-equivalence-is-equiv-precomp k f
      ( λ l X → dependent-universal-property-is-connected-map k c (λ _ → X))
```

### The `k`-equivalences are closed under composition

```agda
module _
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-truncation-equivalence-comp :
    (g : B → C) (f : A → B) →
    is-truncation-equivalence k f →
    is-truncation-equivalence k g →
    is-truncation-equivalence k (g ∘ f)
  is-truncation-equivalence-comp g f ef eg =
    is-equiv-htpy
      ( map-trunc k g ∘ map-trunc k f)
        ( preserves-comp-map-trunc k g f)
      ( is-equiv-comp (map-trunc k g) (map-trunc k f) ef eg)

  truncation-equivalence-comp :
    truncation-equivalence k B C →
    truncation-equivalence k A B →
    truncation-equivalence k A C
  pr1 (truncation-equivalence-comp g f) =
    map-truncation-equivalence k g ∘ map-truncation-equivalence k f
  pr2 (truncation-equivalence-comp g f) =
    is-truncation-equivalence-comp
      ( map-truncation-equivalence k g)
      ( map-truncation-equivalence k f)
      ( is-truncation-equivalence-truncation-equivalence k f)
      ( is-truncation-equivalence-truncation-equivalence k g)
```

### The class of `k`-equivalences has the 3-for-2 property

```agda
module _
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B) (e : is-truncation-equivalence k (g ∘ f))
  where

  is-truncation-equivalence-left-factor :
    is-truncation-equivalence k f → is-truncation-equivalence k g
  is-truncation-equivalence-left-factor ef =
    is-equiv-left-factor
      ( map-trunc k g)
      ( map-trunc k f)
      ( is-equiv-htpy
        ( map-trunc k (g ∘ f))
        ( inv-htpy (preserves-comp-map-trunc k g f)) e)
      ( ef)

  is-truncation-equivalence-right-factor :
    is-truncation-equivalence k g → is-truncation-equivalence k f
  is-truncation-equivalence-right-factor eg =
    is-equiv-right-factor
      ( map-trunc k g)
      ( map-trunc k f)
      ( eg)
      ( is-equiv-htpy
        ( map-trunc k (g ∘ f))
        ( inv-htpy (preserves-comp-map-trunc k g f))
        ( e))
```

### Composing `k`-equivalences with equivalences

```agda
module _
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-truncation-equivalence-is-equiv-is-truncation-equivalence :
    (g : B → C) (f : A → B) →
    is-truncation-equivalence k g →
    is-equiv f →
    is-truncation-equivalence k (g ∘ f)
  is-truncation-equivalence-is-equiv-is-truncation-equivalence g f eg ef =
    is-truncation-equivalence-comp g f
      ( is-truncation-equivalence-is-equiv f ef)
      ( eg)

  is-truncation-equivalence-is-truncation-equivalence-is-equiv :
    (g : B → C) (f : A → B) →
    is-equiv g →
    is-truncation-equivalence k f →
    is-truncation-equivalence k (g ∘ f)
  is-truncation-equivalence-is-truncation-equivalence-is-equiv g f eg ef =
    is-truncation-equivalence-comp g f
      ( ef)
      ( is-truncation-equivalence-is-equiv g eg)

  is-truncation-equivalence-equiv-is-truncation-equivalence :
    (g : B → C) (f : A ≃ B) →
    is-truncation-equivalence k g →
    is-truncation-equivalence k (g ∘ map-equiv f)
  is-truncation-equivalence-equiv-is-truncation-equivalence g f eg =
    is-truncation-equivalence-is-equiv-is-truncation-equivalence g
      ( map-equiv f)
      ( eg)
      ( is-equiv-map-equiv f)

  is-truncation-equivalence-is-truncation-equivalence-equiv :
    (g : B ≃ C) (f : A → B) →
    is-truncation-equivalence k f →
    is-truncation-equivalence k (map-equiv g ∘ f)
  is-truncation-equivalence-is-truncation-equivalence-equiv g f ef =
    is-truncation-equivalence-is-truncation-equivalence-is-equiv
      ( map-equiv g)
      ( f)
      ( is-equiv-map-equiv g)
      ( ef)
```

### The map on dependent pair types induced by the unit of the `(k+1)`-truncation is a `k`-equivalence

This is an instance of Lemma 2.27 in Christensen, Opie, Rijke & Scoccola
[CORS'20] listed below.

```agda
module _
  {l1 l2 : Level} {k : 𝕋}
  {X : UU l1} (P : (type-trunc (succ-𝕋 k) X) → UU l2)
  where

  map-Σ-map-base-unit-trunc :
    Σ X (P ∘ unit-trunc) → Σ (type-trunc (succ-𝕋 k) X) P
  map-Σ-map-base-unit-trunc = map-Σ-map-base unit-trunc P

  is-truncation-equivalence-map-Σ-map-base-unit-trunc :
    is-truncation-equivalence k map-Σ-map-base-unit-trunc
  is-truncation-equivalence-map-Σ-map-base-unit-trunc =
    is-truncation-equivalence-is-equiv-precomp k
      ( map-Σ-map-base-unit-trunc)
      ( λ l X →
        is-equiv-equiv
          ( equiv-ev-pair)
          ( equiv-ev-pair)
          ( refl-htpy)
          ( dependent-universal-property-trunc
            ( λ t →
              ( ( P t → type-Truncated-Type X) ,
                ( is-trunc-succ-is-trunc k
                  ( is-trunc-function-type k
                    ( is-trunc-type-Truncated-Type X)))))))
```

### There is an `k`-equivalence between the fiber of a map and the fiber of its `(k+1)`-truncation

This is an instance of Corollary 2.29 in [CORS'20].

We consider the following composition of maps

```text
   fiber f b = Σ A (λ a → f a = b)
             → Σ A (λ a → ∥ f a ＝ b ∥)
             ≃ Σ A (λ a → | f a | = | b |
             ≃ Σ A (λ a → ∥ f ∥ | a | = | b |)
             → Σ ∥ A ∥ (λ t → ∥ f ∥ t = | b |)
             = fiber ∥ f ∥ | b |
```

where the first and last maps are `k`-equivalences.

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  fiber-map-trunc-fiber :
    fiber f b → fiber (map-trunc (succ-𝕋 k) f) (unit-trunc b)
  fiber-map-trunc-fiber =
    ( map-Σ-map-base-unit-trunc
      ( λ t → map-trunc (succ-𝕋 k) f t ＝ unit-trunc b)) ∘
    ( tot
      ( λ a →
        ( concat (naturality-unit-trunc (succ-𝕋 k) f a) (unit-trunc b)) ∘
        ( map-effectiveness-trunc k (f a) b) ∘
        ( unit-trunc)))

  is-truncation-equivalence-fiber-map-trunc-fiber :
    is-truncation-equivalence k fiber-map-trunc-fiber
  is-truncation-equivalence-fiber-map-trunc-fiber =
    is-truncation-equivalence-comp
      ( map-Σ-map-base-unit-trunc
        ( λ t → map-trunc (succ-𝕋 k) f t ＝ unit-trunc b))
      ( tot
        ( λ a →
          ( concat (naturality-unit-trunc (succ-𝕋 k) f a) (unit-trunc b)) ∘
          ( map-effectiveness-trunc k (f a) b) ∘
          ( unit-trunc)))
      ( is-truncation-equivalence-is-truncation-equivalence-equiv
        ( equiv-tot
          ( λ a →
            ( equiv-concat
              ( naturality-unit-trunc (succ-𝕋 k) f a)
              ( unit-trunc b)) ∘e
            ( effectiveness-trunc k (f a) b)))
        ( λ (a , p) → a , unit-trunc p)
        ( is-equiv-map-equiv (equiv-trunc-Σ k)))
      ( is-truncation-equivalence-map-Σ-map-base-unit-trunc
        ( λ t → map-trunc (succ-𝕋 k) f t ＝ unit-trunc b))

  truncation-equivalence-fiber-map-trunc-fiber :
    truncation-equivalence k
      ( fiber f b)
      ( fiber (map-trunc (succ-𝕋 k) f) (unit-trunc b))
  pr1 truncation-equivalence-fiber-map-trunc-fiber = fiber-map-trunc-fiber
  pr2 truncation-equivalence-fiber-map-trunc-fiber =
    is-truncation-equivalence-fiber-map-trunc-fiber
```

### Being `k`-connected is invariant under `k`-equivalences

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2}
  where

  is-connected-is-truncation-equivalence :
    (f : A → B) → is-truncation-equivalence k f →
    is-connected k B → is-connected k A
  is-connected-is-truncation-equivalence f e =
    is-contr-equiv (type-trunc k B) (map-trunc k f , e)

  is-connected-truncation-equivalence :
    truncation-equivalence k A B → is-connected k B → is-connected k A
  is-connected-truncation-equivalence f =
    is-connected-is-truncation-equivalence
      ( map-truncation-equivalence k f)
      ( is-truncation-equivalence-truncation-equivalence k f)
```

### Every `(k+1)`-equivalence is `k`-connected

This is an instance of Proposition 2.30 in Christensen, Opie, Rijke & Scoccola
listed below.

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-connected-map-is-truncation-equivalence :
    is-truncation-equivalence (succ-𝕋 k) f → is-connected-map k f
  is-connected-map-is-truncation-equivalence e b =
    is-connected-truncation-equivalence
      ( truncation-equivalence-fiber-map-trunc-fiber f b)
      ( is-connected-is-contr k (is-contr-map-is-equiv e (unit-trunc b)))
```

## References

The notion of `k`-equivalence is a special case of the notion of
`L`-equivalence, where `L` is a reflective subuniverse. They were studied in the
paper

- J. D. Christensen, M. Opie, E. Rijke, and L. Scoccola. Localization in
  Homotopy Type Theory. Higher Structures, 2020. [CORS'20]

The class of `k`-equivalences is left orthogonal to the class of `k`-étale maps.
This was shown in

- F. Cherubini, and E. Rijke. Modal descent. Mathematical Structures in Computer
  Science, 2021.
