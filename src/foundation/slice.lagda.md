---
title: Morphisms of the slice category of types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.slice where

open import foundation.contractible-types using
  ( is-contr; is-contr-equiv')
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (_↪_; map-emb; is-emb-map-emb)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.equivalences using
  ( is-equiv; _≃_; _∘e_; map-inv-equiv; is-equiv-has-inverse; map-equiv;
    is-fiberwise-equiv; is-property-is-equiv; id-equiv; map-inv-is-equiv)
open import foundation.fibers-of-maps using
  ( fib; equiv-fib-pr1; equiv-total-fib; triangle-map-equiv-total-fib)
open import foundation.function-extensionality using
  ( equiv-funext; eq-htpy)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-dependent-function-types using
  ( equiv-map-Π)
open import foundation.functoriality-dependent-pair-types using
  ( equiv-tot; fib-triangle; is-fiberwise-equiv-is-equiv-triangle;
    is-equiv-triangle-is-fiberwise-equiv; equiv-Σ)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.homotopies using
  ( _~_; refl-htpy; _∙h_; _·l_; right-unit-htpy; is-contr-total-htpy; _·r_;
    equiv-concat-htpy)
open import foundation.identity-types using (_＝_; refl; inv; inv-inv; _∙_)
open import foundation.injective-maps using (is-injective-emb)
open import foundation.propositional-maps using
  ( is-prop-map-is-emb; equiv-is-prop-map-is-emb)
open import foundation.propositions using
  ( equiv-prop; is-prop-Π; is-prop; is-prop-is-equiv; UU-Prop)
open import foundation.structure using
  ( hom-structure; fam-structure; structure-map)
open import foundation.structure-identity-principle using
  ( extensionality-Σ; is-contr-total-Eq-structure)
open import foundation.type-arithmetic-dependent-pair-types using
  ( inv-assoc-Σ; equiv-right-swap-Σ)
open import foundation.type-theoretic-principle-of-choice using
  ( inv-distributive-Π-Σ)
open import foundation.univalence using
  ( is-contr-total-equiv; eq-equiv-fam)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)
```

## Idea

The slice of a category over an object X is the category of morphisms into X. A morphism in the slice from `f : A → X` to `g : B → X` consists of a function `h : A → B` such that the triangle `f ~ g ∘ h` commutes. We make these definitions for types.

## Definition

### The objects of the slice category of types

```agda
slice-UU : (l : Level) {l1 : Level} (A : UU l1) → UU (l1 ⊔ lsuc l)
slice-UU l A = Σ (UU l) (λ X → X → A)

Fib : {l l1 : Level} (A : UU l1) → slice-UU l A → A → UU (l1 ⊔ l)
Fib A f = fib (pr2 f)

Pr1 : {l l1 : Level} (A : UU l1) → (A → UU l) → slice-UU (l1 ⊔ l) A
pr1 (Pr1 A B) = Σ A B
pr2 (Pr1 A B) = pr1
```

### The morphisms of the slice category of types

```agda
hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → UU (l1 ⊔ (l2 ⊔ l3))
hom-slice {A = A} {B} f g = Σ (A → B) (λ h → f ~ (g ∘ h))

map-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → hom-slice f g → A → B
map-hom-slice f g h = pr1 h

triangle-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (h : hom-slice f g) →
  f ~ (g ∘ (map-hom-slice f g h))
triangle-hom-slice f g h = pr2 h
```

## Properties

### We characterize the identity type of hom-slice

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X)
  where

  htpy-hom-slice : (h h' : hom-slice f g) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-hom-slice h h' =
    Σ ( map-hom-slice f g h ~ map-hom-slice f g h')
      ( λ K →
        ( (triangle-hom-slice f g h) ∙h (g ·l K)) ~
        ( triangle-hom-slice f g h'))

  extensionality-hom-slice :
    (h h' : hom-slice f g) → (h ＝ h') ≃ htpy-hom-slice h h'
  extensionality-hom-slice (pair h H) =
    extensionality-Σ
      ( λ {h'} H' (K : h ~ h') → (H ∙h (g ·l K)) ~ H')
      ( refl-htpy)
      ( right-unit-htpy)
      ( λ h' → equiv-funext)
      ( λ H' → equiv-concat-htpy (right-unit-htpy) H' ∘e equiv-funext)

  eq-htpy-hom-slice :
    (h h' : hom-slice f g) → htpy-hom-slice h h' → h ＝ h'
  eq-htpy-hom-slice h h' = map-inv-equiv (extensionality-hom-slice h h')
```

```agda
comp-hom-slice :
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (h : C → X) →
  hom-slice g h → hom-slice f g → hom-slice f h
pr1 (comp-hom-slice f g h j i) = map-hom-slice g h j ∘ map-hom-slice f g i
pr2 (comp-hom-slice f g h j i) =
  ( triangle-hom-slice f g i) ∙h
  ( (triangle-hom-slice g h j) ·r (map-hom-slice f g i))

id-hom-slice :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) → hom-slice f f
pr1 (id-hom-slice f) = id
pr2 (id-hom-slice f) = refl-htpy

is-equiv-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → hom-slice f g → UU (l2 ⊔ l3)
is-equiv-hom-slice f g h = is-equiv (map-hom-slice f g h)
```

### Morphisms in the slice are equivalently described as families of maps between fibers

```agda
fiberwise-hom-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  hom-slice f g → (x : X) → (fib f x) → (fib g x)
fiberwise-hom-hom-slice f g (pair h H) = fib-triangle f g h H

hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  ((x : X) → (fib f x) → (fib g x)) → hom-slice f g
pr1 (hom-slice-fiberwise-hom f g α) a = pr1 (α (f a) (pair a refl))
pr2 (hom-slice-fiberwise-hom f g α) a = inv (pr2 (α (f a) (pair a refl)))

issec-hom-slice-fiberwise-hom-eq-htpy :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (α : (x : X) → (fib f x) → (fib g x)) (x : X) →
  (fiberwise-hom-hom-slice f g (hom-slice-fiberwise-hom f g α) x) ~ (α x)
issec-hom-slice-fiberwise-hom-eq-htpy f g α .(f a) (pair a refl) =
  eq-pair-Σ refl (inv-inv (pr2 (α (f a) (pair a refl))))

issec-hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  ((fiberwise-hom-hom-slice f g) ∘ (hom-slice-fiberwise-hom f g)) ~ id
issec-hom-slice-fiberwise-hom f g α =
  eq-htpy (λ x → eq-htpy (issec-hom-slice-fiberwise-hom-eq-htpy f g α x))

isretr-hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  ((hom-slice-fiberwise-hom f g) ∘ (fiberwise-hom-hom-slice f g)) ~ id
isretr-hom-slice-fiberwise-hom f g (pair h H) =
  eq-pair-Σ refl (eq-htpy (λ a → (inv-inv (H a))))

abstract
  is-equiv-fiberwise-hom-hom-slice :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X) →
    is-equiv (fiberwise-hom-hom-slice f g)
  is-equiv-fiberwise-hom-hom-slice f g =
    is-equiv-has-inverse
      ( hom-slice-fiberwise-hom f g)
      ( issec-hom-slice-fiberwise-hom f g)
      ( isretr-hom-slice-fiberwise-hom f g)

equiv-fiberwise-hom-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  hom-slice f g ≃ ((x : X) → fib f x → fib g x)
pr1 (equiv-fiberwise-hom-hom-slice f g) = fiberwise-hom-hom-slice f g
pr2 (equiv-fiberwise-hom-hom-slice f g) = is-equiv-fiberwise-hom-hom-slice f g

abstract
  is-equiv-hom-slice-fiberwise-hom :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X) →
    is-equiv (hom-slice-fiberwise-hom f g)
  is-equiv-hom-slice-fiberwise-hom f g =
    is-equiv-has-inverse
      ( fiberwise-hom-hom-slice f g)
      ( isretr-hom-slice-fiberwise-hom f g)
      ( issec-hom-slice-fiberwise-hom f g)

equiv-hom-slice-fiberwise-hom :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  ((x : X) → fib f x → fib g x) ≃ hom-slice f g
pr1 (equiv-hom-slice-fiberwise-hom f g) = hom-slice-fiberwise-hom f g
pr2 (equiv-hom-slice-fiberwise-hom f g) = is-equiv-hom-slice-fiberwise-hom f g

equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → UU (l1 ⊔ (l2 ⊔ l3))
equiv-slice {A = A} {B} f g = Σ (A ≃ B) (λ e → f ~ (g ∘ (map-equiv e)))

hom-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice f g → hom-slice f g
pr1 (hom-equiv-slice f g e) = pr1 (pr1 e)
pr2 (hom-equiv-slice f g e) = pr2 e
```

```agda
abstract
  is-fiberwise-equiv-fiberwise-equiv-equiv-slice :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X)
    (t : hom-slice f g) → is-equiv (pr1 t) →
    is-fiberwise-equiv (fiberwise-hom-hom-slice f g t)
  is-fiberwise-equiv-fiberwise-equiv-equiv-slice f g (pair h H) =
    is-fiberwise-equiv-is-equiv-triangle f g h H

abstract
  is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A → X) (g : B → X) →
    (t : hom-slice f g) →
    ((x : X) → is-equiv (fiberwise-hom-hom-slice f g t x)) →
    is-equiv (pr1 t)
  is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice
    f g (pair h H) =
    is-equiv-triangle-is-fiberwise-equiv f g h H

equiv-fiberwise-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice f g ≃ Σ ((x : X) → (fib f x) → (fib g x)) is-fiberwise-equiv
equiv-fiberwise-equiv-equiv-slice f g =
  equiv-Σ is-fiberwise-equiv (equiv-fiberwise-hom-hom-slice f g) α ∘e
  equiv-right-swap-Σ
  where
  α   : ( h : hom-slice f g) →
        is-equiv (pr1 h) ≃
        is-fiberwise-equiv (map-equiv (equiv-fiberwise-hom-hom-slice f g) h)
  α h = equiv-prop
          ( is-property-is-equiv _)
          ( is-prop-Π (λ x → is-property-is-equiv _))
          ( is-fiberwise-equiv-fiberwise-equiv-equiv-slice f g h)
          ( is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice
            f g h)

fiberwise-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice f g → Σ ((x : X) → (fib f x) → (fib g x)) is-fiberwise-equiv
fiberwise-equiv-equiv-slice f g =
  map-equiv (equiv-fiberwise-equiv-equiv-slice f g)

equiv-fam-equiv-equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) →
  equiv-slice f g ≃ ((x : X) → (fib f x) ≃ (fib g x))
equiv-fam-equiv-equiv-slice f g =
  ( inv-distributive-Π-Σ) ∘e
  ( equiv-fiberwise-equiv-equiv-slice f g)
```

### The type of slice morphisms into an embedding is a proposition

```agda
abstract
  is-prop-hom-slice :
    { l1 l2 l3 : Level} {X : UU l1} {A : UU l2} (f : A → X) →
    { B : UU l3} (i : B ↪ X) → is-prop (hom-slice f (map-emb i))
  is-prop-hom-slice {X = X} f i =
    is-prop-is-equiv
      ( is-equiv-fiberwise-hom-hom-slice f (map-emb i))
      ( is-prop-Π
        ( λ x → is-prop-Π
          ( λ p → is-prop-map-is-emb (is-emb-map-emb i) x)))
```

```agda
abstract
  is-equiv-hom-slice-emb :
    {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
    (f : A ↪ X) (g : B ↪ X) (h : hom-slice (map-emb f) (map-emb g)) →
    hom-slice (map-emb g) (map-emb f) →
    is-equiv-hom-slice (map-emb f) (map-emb g) h
  is-equiv-hom-slice-emb f g h i =
    is-equiv-has-inverse
      ( map-hom-slice (map-emb g) (map-emb f) i)
      ( λ y →
        is-injective-emb g
        ( inv
          ( ( triangle-hom-slice
              ( map-emb g)
              ( map-emb f)
              ( i)
              ( y)) ∙
            ( triangle-hom-slice
              ( map-emb f)
              ( map-emb g)
              ( h)
              ( map-hom-slice (map-emb g) (map-emb f) i y)))))
      ( λ x →
        is-injective-emb f
        ( inv
          ( ( triangle-hom-slice (map-emb f) (map-emb g) h x) ∙
            ( triangle-hom-slice (map-emb g) (map-emb f) i
              ( map-hom-slice
                ( map-emb f)
                ( map-emb g)
                ( h)
                ( x))))))
```

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  equiv-slice' : (f g : slice-UU l2 A) → UU (l1 ⊔ l2)
  equiv-slice' f g = equiv-slice (pr2 f) (pr2 g)

  id-equiv-slice-UU : (f : slice-UU l2 A) → equiv-slice' f f
  pr1 (id-equiv-slice-UU f) = id-equiv
  pr2 (id-equiv-slice-UU f) = refl-htpy

  equiv-eq-slice-UU : (f g : slice-UU l2 A) → f ＝ g → equiv-slice' f g
  equiv-eq-slice-UU f .f refl = id-equiv-slice-UU f

  abstract
    is-contr-total-equiv-slice' :
      (f : slice-UU l2 A) → is-contr (Σ (slice-UU l2 A) (equiv-slice' f))
    is-contr-total-equiv-slice' (pair X f) =
      is-contr-total-Eq-structure
        ( λ Y g e → f ~ (g ∘ map-equiv e))
        ( is-contr-total-equiv X)
        ( pair X id-equiv)
        ( is-contr-total-htpy f)

  abstract
    is-equiv-equiv-eq-slice-UU :
      (f g : slice-UU l2 A) → is-equiv (equiv-eq-slice-UU f g)
    is-equiv-equiv-eq-slice-UU f =
      fundamental-theorem-id f
        ( id-equiv-slice-UU f)
        ( is-contr-total-equiv-slice' f)
        ( equiv-eq-slice-UU f)

  eq-equiv-slice :
    (f g : slice-UU l2 A) → equiv-slice' f g → f ＝ g
  eq-equiv-slice f g =
    map-inv-is-equiv (is-equiv-equiv-eq-slice-UU f g)

abstract
  issec-Pr1 :
    {l1 l2 : Level} {A : UU l1} → (Fib {l1 ⊔ l2} A ∘ Pr1 {l1 ⊔ l2} A) ~ id
  issec-Pr1 B = eq-equiv-fam (equiv-fib-pr1 B)

  isretr-Pr1 :
    {l1 l2 : Level} {A : UU l1} → (Pr1 {l1 ⊔ l2} A ∘ Fib {l1 ⊔ l2} A) ~ id
  isretr-Pr1 {A = A} (pair X f) =
    eq-equiv-slice
      ( Pr1 A (Fib A (pair X f)))
      ( pair X f)
      ( pair (equiv-total-fib f) (triangle-map-equiv-total-fib f))

  is-equiv-Fib :
    {l1 : Level} (l2 : Level) (A : UU l1) → is-equiv (Fib {l1 ⊔ l2} A)
  is-equiv-Fib l2 A =
    is-equiv-has-inverse (Pr1 A) (issec-Pr1 {l2 = l2}) (isretr-Pr1 {l2 = l2})

equiv-Fib :
  {l1 : Level} (l2 : Level) (A : UU l1) → slice-UU (l1 ⊔ l2) A ≃ (A → UU (l1 ⊔ l2))
pr1 (equiv-Fib l2 A) = Fib A
pr2 (equiv-Fib l2 A) = is-equiv-Fib l2 A

abstract
  is-equiv-Pr1 :
    {l1 : Level} (l2 : Level) (A : UU l1) → is-equiv (Pr1 {l1 ⊔ l2} A)
  is-equiv-Pr1 {l1} l2 A =
    is-equiv-has-inverse (Fib A) (isretr-Pr1 {l2 = l2}) (issec-Pr1 {l2 = l2})

equiv-Pr1 :
  {l1 : Level} (l2 : Level) (A : UU l1) → (A → UU (l1 ⊔ l2)) ≃ slice-UU (l1 ⊔ l2) A
pr1 (equiv-Pr1 l2 A) = Pr1 A
pr2 (equiv-Pr1 l2 A) = is-equiv-Pr1 l2 A
```

```agda
slice-UU-structure :
  {l1 l2 : Level} (l : Level) (P : UU (l1 ⊔ l) → UU l2) (B : UU l1) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
slice-UU-structure l P B = Σ (UU l) (λ A → hom-structure P A B)

equiv-Fib-structure :
  {l1 l3 : Level} (l : Level) (P : UU (l1 ⊔ l) → UU l3) (B : UU l1) →
  slice-UU-structure (l1 ⊔ l) P B ≃ fam-structure P B
equiv-Fib-structure {l1} {l3} l P B =
  ( ( inv-distributive-Π-Σ) ∘e
    ( equiv-Σ
      ( λ C → (b : B) → P (C b))
      ( equiv-Fib l B)
      ( λ f → equiv-map-Π (λ b → id-equiv)))) ∘e
  ( inv-assoc-Σ (UU (l1 ⊔ l)) (λ A → A → B) (λ f → structure-map P (pr2 f)))
```

```agda
slice-UU-emb : (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
slice-UU-emb l A = Σ (UU l) (λ X → X ↪ A)

equiv-Fib-Prop :
  (l : Level) {l1 : Level} (A : UU l1) →
  slice-UU-emb (l1 ⊔ l) A ≃ (A → UU-Prop (l1 ⊔ l))
equiv-Fib-Prop l A =
  ( equiv-Fib-structure l is-prop A) ∘e
  ( equiv-tot (λ X → equiv-tot equiv-is-prop-map-is-emb))
```
