# `k`-acyclic maps

```agda
module synthetic-homotopy-theory.truncated-acyclic-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.connected-maps
open import foundation.connected-types
open import foundation.constant-maps
open import foundation.dependent-epimorphisms-with-respect-to-truncated-types
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.embeddings
open import foundation.epimorphisms-with-respect-to-truncated-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.precomposition-dependent-functions
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.truncated-types
open import foundation.truncation-equivalences
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.codiagonals-of-maps
open import synthetic-homotopy-theory.suspensions-of-types
open import synthetic-homotopy-theory.truncated-acyclic-types
```

</details>

## Idea

A map `f : A → B` is said to be **`k`-acyclic** if its
[fibers](foundation-core.fibers-of-maps.md) are
[`k`-acyclic types](synthetic-homotopy-theory.truncated-acyclic-types.md).

## Definitions

### The predicate of being a `k`-acyclic map

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  where

  is-truncated-acyclic-map-Prop : (A → B) → Prop (l1 ⊔ l2)
  is-truncated-acyclic-map-Prop f =
    Π-Prop B (λ b → is-truncated-acyclic-Prop k (fiber f b))

  is-truncated-acyclic-map : (A → B) → UU (l1 ⊔ l2)
  is-truncated-acyclic-map f = type-Prop (is-truncated-acyclic-map-Prop f)

  is-prop-is-truncated-acyclic-map :
    (f : A → B) → is-prop (is-truncated-acyclic-map f)
  is-prop-is-truncated-acyclic-map f =
    is-prop-type-Prop (is-truncated-acyclic-map-Prop f)
```

## Properties

### A map is `k`-acyclic if and only if it is an [epimorphism with respect to `k`-types](foundation.epimorphisms-with-respect-to-truncated-types.md)

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-truncated-acyclic-map-is-epimorphism-Truncated-Type :
    is-epimorphism-Truncated-Type k f → is-truncated-acyclic-map k f
  is-truncated-acyclic-map-is-epimorphism-Truncated-Type e b =
    is-connected-equiv
      ( equiv-fiber-codiagonal-map-suspension-fiber f b)
      ( is-connected-codiagonal-map-is-epimorphism-Truncated-Type k f e b)

  is-epimorphism-is-truncated-acyclic-map-Truncated-Type :
    is-truncated-acyclic-map k f → is-epimorphism-Truncated-Type k f
  is-epimorphism-is-truncated-acyclic-map-Truncated-Type ac =
    is-epimorphism-is-connected-codiagonal-map-Truncated-Type k f
      ( λ b →
        is-connected-equiv'
          ( equiv-fiber-codiagonal-map-suspension-fiber f b)
          ( ac b))
```

### A type is `k`-acyclic if and only if its terminal map is a `k`-acyclic map

```agda
module _
  {l : Level} {k : 𝕋} (A : UU l)
  where

  is-truncated-acyclic-map-terminal-map-is-truncated-acyclic :
    is-truncated-acyclic k A →
    is-truncated-acyclic-map k (terminal-map {A = A})
  is-truncated-acyclic-map-terminal-map-is-truncated-acyclic ac u =
    is-truncated-acyclic-equiv (equiv-fiber-terminal-map u) ac

  is-truncated-acyclic-is-truncated-acyclic-map-terminal-map :
    is-truncated-acyclic-map k (terminal-map {A = A}) →
    is-truncated-acyclic k A
  is-truncated-acyclic-is-truncated-acyclic-map-terminal-map ac =
    is-truncated-acyclic-equiv inv-equiv-fiber-terminal-map-star (ac star)
```

### A type is `k`-acyclic if and only if the constant map from any `k`-type is an embedding

More precisely, `A` is `k`-acyclic if and only if for all `k`-types `X`, the map

```text
 const : X → (A → X)
```

is an embedding.

```agda
module _
  {l : Level} {k : 𝕋} (A : UU l)
  where

  is-emb-const-is-truncated-acyclic-Truncated-Type :
    is-truncated-acyclic k A →
    {l' : Level} (X : Truncated-Type l' k) →
    is-emb (const A (type-Truncated-Type X))
  is-emb-const-is-truncated-acyclic-Truncated-Type ac X =
    is-emb-comp
      ( precomp terminal-map (type-Truncated-Type X))
      ( map-inv-left-unit-law-function-type (type-Truncated-Type X))
      ( is-epimorphism-is-truncated-acyclic-map-Truncated-Type terminal-map
        ( is-truncated-acyclic-map-terminal-map-is-truncated-acyclic A ac)
        ( X))
      ( is-emb-is-equiv
        ( is-equiv-map-inv-left-unit-law-function-type (type-Truncated-Type X)))

  is-truncated-acyclic-is-emb-const-Truncated-Type :
    ({l' : Level} (X : Truncated-Type l' k) →
    is-emb (const A (type-Truncated-Type X))) →
    is-truncated-acyclic k A
  is-truncated-acyclic-is-emb-const-Truncated-Type e =
    is-truncated-acyclic-is-truncated-acyclic-map-terminal-map A
      ( is-truncated-acyclic-map-is-epimorphism-Truncated-Type
        ( terminal-map)
        ( λ X →
          is-emb-triangle-is-equiv'
            ( const A (type-Truncated-Type X))
            ( precomp terminal-map (type-Truncated-Type X))
            ( map-inv-left-unit-law-function-type (type-Truncated-Type X))
            ( refl-htpy)
            ( is-equiv-map-inv-left-unit-law-function-type
              ( type-Truncated-Type X))
            ( e X)))
```

### A type is `k`-acyclic if and only if the constant map from any identity type of any `k`-type is an equivalence

More precisely, `A` is `k`-acyclic if and only if for all `k`-types `X` and
elements `x,y : X`, the map

```text
 const : (x ＝ y) → (A → x ＝ y)
```

is an equivalence.

```agda
module _
  {l : Level} {k : 𝕋} (A : UU l)
  where

  is-equiv-const-Id-is-acyclic-Truncated-Type :
    is-truncated-acyclic k A →
    {l' : Level} (X : Truncated-Type l' k) (x y : type-Truncated-Type X) →
    is-equiv (const A (x ＝ y))
  is-equiv-const-Id-is-acyclic-Truncated-Type ac X x y =
    is-equiv-htpy
      ( htpy-eq ∘ ap (const A (type-Truncated-Type X)) {x} {y})
      ( htpy-ap-diagonal-htpy-eq-diagonal-Id A x y)
      ( is-equiv-comp
        ( htpy-eq)
        ( ap (const A (type-Truncated-Type X)))
        ( is-emb-const-is-truncated-acyclic-Truncated-Type A ac X x y)
        ( funext
          ( const A (type-Truncated-Type X) x)
          ( const A (type-Truncated-Type X) y)))

  is-truncated-acyclic-is-equiv-const-Id-Truncated-Type :
    ( {l' : Level} (X : Truncated-Type l' k) (x y : type-Truncated-Type X) →
      is-equiv (const A (x ＝ y))) →
    is-truncated-acyclic k A
  is-truncated-acyclic-is-equiv-const-Id-Truncated-Type h =
    is-truncated-acyclic-is-emb-const-Truncated-Type A
      ( λ X →
        ( λ x y →
          is-equiv-right-factor
            ( htpy-eq)
            ( ap (const A (type-Truncated-Type X)))
            ( funext
              ( const A (type-Truncated-Type X) x)
              ( const A (type-Truncated-Type X) y))
            ( is-equiv-htpy
              ( const A (x ＝ y))
              ( htpy-diagonal-Id-ap-diagonal-htpy-eq A x y)
              ( h X x y))))
```

### A map is `k`-acyclic if and only if it is an [dependent `k`-epimorphism](foundation.dependent-epimorphisms-with-respect-to-truncated-types.md)

The proof is similar to that of dependent epimorphisms and
[acyclic-maps](synthetic-homotopy-theory.acyclic-maps.md).

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-truncated-acyclic-map-is-dependent-epimorphism-Truncated-Type :
    is-dependent-epimorphism-Truncated-Type k f → is-truncated-acyclic-map k f
  is-truncated-acyclic-map-is-dependent-epimorphism-Truncated-Type e =
    is-truncated-acyclic-map-is-epimorphism-Truncated-Type f
      ( is-epimorphism-is-dependent-epimorphism-Truncated-Type f e)

  is-dependent-epimorphism-is-truncated-acyclic-map-Truncated-Type :
    is-truncated-acyclic-map k f → is-dependent-epimorphism-Truncated-Type k f
  is-dependent-epimorphism-is-truncated-acyclic-map-Truncated-Type ac C =
    is-emb-comp
      ( precomp-Π
        ( map-inv-equiv-total-fiber f)
        ( type-Truncated-Type ∘ C ∘ pr1) ∘ ind-Σ)
      ( map-Π (λ b → const (fiber f b) (type-Truncated-Type (C b))))
      ( is-emb-comp
        ( precomp-Π
          ( map-inv-equiv-total-fiber f)
          ( type-Truncated-Type ∘ C ∘ pr1))
        ( ind-Σ)
        ( is-emb-is-equiv
          ( is-equiv-precomp-Π-is-equiv
            ( is-equiv-map-inv-equiv-total-fiber f)
              (type-Truncated-Type ∘ C ∘ pr1)))
        ( is-emb-is-equiv is-equiv-ind-Σ))
      ( is-emb-map-Π
        ( λ b →
          is-emb-const-is-truncated-acyclic-Truncated-Type
            ( fiber f b)
            ( ac b)
            ( C b)))
```

In particular, every `k`-epimorphism is actually a dependent `k`-epimorphism.

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-dependent-epimorphism-is-epimorphism-Truncated-Type :
    is-epimorphism-Truncated-Type k f →
    is-dependent-epimorphism-Truncated-Type k f
  is-dependent-epimorphism-is-epimorphism-Truncated-Type e =
    is-dependent-epimorphism-is-truncated-acyclic-map-Truncated-Type f
      ( is-truncated-acyclic-map-is-epimorphism-Truncated-Type f e)
```

### The class of `k`-acyclic maps is closed under composition and has the right cancellation property

Since the `k`-acyclic maps are precisely the `k`-epimorphisms this follows from
the corresponding facts about
[`k`-epimorphisms](foundation.epimorphisms-with-respect-to-truncated-types.md).

```agda
module _
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B)
  where

  is-truncated-acyclic-map-comp :
    is-truncated-acyclic-map k g →
    is-truncated-acyclic-map k f →
    is-truncated-acyclic-map k (g ∘ f)
  is-truncated-acyclic-map-comp ag af =
    is-truncated-acyclic-map-is-epimorphism-Truncated-Type (g ∘ f)
      ( is-epimorphism-comp-Truncated-Type k g f
        ( is-epimorphism-is-truncated-acyclic-map-Truncated-Type g ag)
        ( is-epimorphism-is-truncated-acyclic-map-Truncated-Type f af))

  is-truncated-acyclic-map-left-factor :
    is-truncated-acyclic-map k (g ∘ f) →
    is-truncated-acyclic-map k f →
    is-truncated-acyclic-map k g
  is-truncated-acyclic-map-left-factor ac af =
    is-truncated-acyclic-map-is-epimorphism-Truncated-Type g
      ( is-epimorphism-left-factor-Truncated-Type k g f
        ( is-epimorphism-is-truncated-acyclic-map-Truncated-Type (g ∘ f) ac)
        ( is-epimorphism-is-truncated-acyclic-map-Truncated-Type f af))
```

### Every `k`-connected map is `(k+1)`-acyclic

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-truncated-acyclic-map-succ-is-connected-map :
    is-connected-map k f → is-truncated-acyclic-map (succ-𝕋 k) f
  is-truncated-acyclic-map-succ-is-connected-map c b =
    is-truncated-acyclic-succ-is-connected (c b)
```

In particular, the unit of the `k`-truncation is `(k+1)`-acyclic

```agda
is-truncated-acyclic-map-succ-unit-trunc :
  {l : Level} {k : 𝕋} (A : UU l) →
  is-truncated-acyclic-map (succ-𝕋 k) (unit-trunc {A = A})
is-truncated-acyclic-map-succ-unit-trunc {k = k} A =
  is-truncated-acyclic-map-succ-is-connected-map
    ( unit-trunc)
    ( is-connected-map-unit-trunc k)
```

### A type is `(k+1)`-acyclic if and only if its `k`-truncation is

```agda
module _
  {l : Level} {k : 𝕋} (A : UU l)
  where

  is-truncated-succ-acyclic-is-truncated-succ-acyclic-type-trunc :
    is-truncated-acyclic (succ-𝕋 k) (type-trunc k A) →
    is-truncated-acyclic (succ-𝕋 k) A
  is-truncated-succ-acyclic-is-truncated-succ-acyclic-type-trunc ac =
    is-truncated-acyclic-is-truncated-acyclic-map-terminal-map A
      ( is-truncated-acyclic-map-comp
        ( terminal-map)
        ( unit-trunc)
        ( is-truncated-acyclic-map-terminal-map-is-truncated-acyclic
          ( type-trunc k A)
          ( ac))
        ( is-truncated-acyclic-map-succ-unit-trunc A))

  is-truncated-succ-acyclic-type-trunc-is-truncated-succ-acyclic :
    is-truncated-acyclic (succ-𝕋 k) A →
    is-truncated-acyclic (succ-𝕋 k) (type-trunc k A)
  is-truncated-succ-acyclic-type-trunc-is-truncated-succ-acyclic ac =
    is-truncated-acyclic-is-truncated-acyclic-map-terminal-map
      ( type-trunc k A)
      ( is-truncated-acyclic-map-left-factor
        ( terminal-map)
        ( unit-trunc)
        ( is-truncated-acyclic-map-terminal-map-is-truncated-acyclic A ac)
        ( is-truncated-acyclic-map-succ-unit-trunc A))
```

### Every `k`-equivalence is `k`-acyclic

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-truncated-acyclic-map-is-truncation-equivalence :
    is-truncation-equivalence k f → is-truncated-acyclic-map k f
  is-truncated-acyclic-map-is-truncation-equivalence e =
    is-truncated-acyclic-map-is-epimorphism-Truncated-Type f
      ( λ C →
        is-emb-is-equiv
          ( is-equiv-precomp-is-truncation-equivalence k f e C))
```

## See also

- [Acyclic maps](synthetic-homotopy-theory.acyclic-maps.md)
- [Acyclic types](synthetic-homotopy-theory.acyclic-types.md)
- [`k`-acyclic types](synthetic-homotopy-theory.truncated-acyclic-types.md)
- [Dependent epimorphisms](foundation.dependent-epimorphisms.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)
