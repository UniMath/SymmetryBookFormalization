# Fibers of extended iterated maps

```agda
{-# OPTIONS --allow-unsolved-metas #-}
module foundation.fibers-of-extended-iterated-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import set-theory.increasing-binary-sequences
open import set-theory.inequality-increasing-binary-sequences
open import foundation.fixed-points-endofunctions
open import set-theory.bounded-increasing-binary-sequences
open import foundation.strictly-right-unital-concatenation-identifications
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.cartesian-product-types
open import foundation-core.homotopies
open import foundation.booleans
open import foundation-core.identity-types
open import foundation-core.empty-types
open import foundation-core.postcomposition-functions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.transport-along-identifications
```

</details>

## Idea

Given an endomap `f : A → A`, an
[extended natural number](set-theory.increasing-binary-sequences.md) `n : ℕ∞`
and an element `b : A`, the
{{#concept "fiber" Disambiguation="of the extended iterated map" Agda=fiber-extended-iterate}}
of the extended iterate `fⁿ` at `b` can be recorded by the data

```text
  fⁿ xₙ ＝ ⋯ ＝ f² x₂ ＝ f x₁ ＝ x₀ ＝ b
```

## Definition

```agda
module _
  (n : ℕ∞↑) {l : Level} {A : UU l} (f : A → A) (b : A)
  where

  fiber-extended-iterate : UU l
  fiber-extended-iterate =
    Σ ( bounded-ℕ∞↑ n → A)
      ( λ x →
        ( x (zero-bounded-ℕ∞↑ n) ＝ b) ×
        ( (k : succ-bounded-ℕ∞↑ n) →
          f (x (bounded-succ-succ-bounded-ℕ∞↑ n k)) ＝
          x (bounded-succ-bounded-ℕ∞↑ n k)))

  fiber-extended-iterate' : UU l
  fiber-extended-iterate' =
   Σ ( bounded-ℕ∞↑ (succ-ℕ∞↑ n) → A)
      ( λ x →
        ( b ＝ x (zero-bounded-ℕ∞↑ (succ-ℕ∞↑ n))) ×
        ( (k : bounded-ℕ∞↑ n) →
          x (inclusion-bounded-succ-bounded-ℕ∞↑ n k) ＝
          f (x (inclusion-succ-bounded-ℕ∞↑ n k))))

module _
  (n : ℕ∞↑) {l : Level} {A : UU l} (f : A → A) {b : A}
  where

  sequence-fiber-extended-iterate :
    fiber-extended-iterate n f b → bounded-ℕ∞↑ n → A
  sequence-fiber-extended-iterate = pr1

  inclusion-fiber-extended-iterate : fiber-extended-iterate n f b → A
  inclusion-fiber-extended-iterate p =
    sequence-fiber-extended-iterate p (n , refl-leq-ℕ∞↑ n)
```

## Properties

### Fibers of the trivial iterate

```agda
fiber-extended-iterate-zero :
  {l : Level} {A : UU l} (f : A → A) (a : A) →
  fiber-extended-iterate zero-ℕ∞↑ f a
fiber-extended-iterate-zero f a =
    ( λ _ → a) ,
    ( refl) ,
    ( λ k → ex-falso (is-succ-bounded-succ-bounded-ℕ∞↑ zero-ℕ∞↑ k 0))
```

### Fibers of extended iterated endomaps from fixed points

```agda
module _
  {l : Level} {A : UU l} (n : ℕ∞↑) (f : A → A)
  where

  fiber-extended-iterate-fixed-point' :
    (a : A) → f a ＝ a → fiber-extended-iterate n f a
  fiber-extended-iterate-fixed-point' a p =
    ((λ _ → a) , refl , (λ _ → p))

  fiber-extended-iterate-fixed-point :
    (p : fixed-point f) → fiber-extended-iterate n f (pr1 p)
  fiber-extended-iterate-fixed-point (a , p) =
    fiber-extended-iterate-fixed-point' a p
```

### Padding fibers of extended iterated endomaps

```agda
module _
  {l : Level} {A : UU l} (n : ℕ∞↑) (f : A → A) (a : A)
  where

  pad-left-fiber-extended-iterate :
    (p : fiber-extended-iterate n f a)
    (x : A) → f x ＝ sequence-fiber-extended-iterate n f p (self-bounded-ℕ∞↑ n) →
    fiber-extended-iterate (succ-ℕ∞↑ n) f a
  pad-left-fiber-extended-iterate p x q = (λ x₁ → {!   !}) , {!   !}
```

### Shifting fibers of extended iterated endomaps

```agda
module _
  {l : Level} {A : UU l} (n : ℕ∞↑) (f : A → A) (a : A)
  where

  ap-fiber-extended-iterate :
    (p : fiber-extended-iterate n f a) → fiber-extended-iterate n f (f a)
  ap-fiber-extended-iterate (x , p₀ , p) = (f ∘ x , ap f p₀ , ap f ∘ p)

  ap-fiber-extended-iterate' :
    (p : fiber-extended-iterate n f a) → fiber-extended-iterate (succ-ℕ∞↑ n) f (f a)
  ap-fiber-extended-iterate' p =
    pad-left-fiber-extended-iterate n f (f a) (ap-fiber-extended-iterate p) (sequence-fiber-extended-iterate n f p (self-bounded-ℕ∞↑ n)) refl

  compute-ap-fiber-extended-iterate' :
    (p : fiber-extended-iterate n f a) →
    inclusion-fiber-extended-iterate (succ-ℕ∞↑ n) f (ap-fiber-extended-iterate' p) ＝ inclusion-fiber-extended-iterate n f p
  compute-ap-fiber-extended-iterate' p = {!   !}
```

### If `n` is finite then `fiber-extended-iterate n f` is the fiber of `fⁿ⁺¹`

> Proof: induct on `n`

### If the fibers of `f` are decidable then so is `extended-fiber-iterate n f`

### Characterization of the identity types of the fibers of a map

#### The case of `fiber-extended-iterate`

```text
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  Eq-fiber-extended-iterate : fiber-extended-iterate f b → fiber-extended-iterate f b → UU (l1 ⊔ l2)
  Eq-fiber-extended-iterate s t = Σ (pr1 s ＝ pr1 t) (λ α → ap f α ∙ pr2 t ＝ pr2 s)

  refl-Eq-fiber-extended-iterate : (s : fiber-extended-iterate f b) → Eq-fiber-extended-iterate s s
  pr1 (refl-Eq-fiber-extended-iterate s) = refl
  pr2 (refl-Eq-fiber-extended-iterate s) = refl

  Eq-eq-fiber-extended-iterate : {s t : fiber-extended-iterate f b} → s ＝ t → Eq-fiber-extended-iterate s t
  Eq-eq-fiber-extended-iterate {s} refl = refl-Eq-fiber-extended-iterate s

  eq-Eq-fiber-extended-iterate-uncurry : {s t : fiber-extended-iterate f b} → Eq-fiber-extended-iterate s t → s ＝ t
  eq-Eq-fiber-extended-iterate-uncurry (refl , refl) = refl

  eq-Eq-fiber-extended-iterate :
    {s t : fiber-extended-iterate f b} (α : pr1 s ＝ pr1 t) → ap f α ∙ pr2 t ＝ pr2 s → s ＝ t
  eq-Eq-fiber-extended-iterate α β = eq-Eq-fiber-extended-iterate-uncurry (α , β)

  is-section-eq-Eq-fiber-extended-iterate :
    {s t : fiber-extended-iterate f b} →
    is-section (Eq-eq-fiber-extended-iterate {s} {t}) (eq-Eq-fiber-extended-iterate-uncurry {s} {t})
  is-section-eq-Eq-fiber-extended-iterate (refl , refl) = refl

  is-retraction-eq-Eq-fiber-extended-iterate :
    {s t : fiber-extended-iterate f b} →
    is-retraction (Eq-eq-fiber-extended-iterate {s} {t}) (eq-Eq-fiber-extended-iterate-uncurry {s} {t})
  is-retraction-eq-Eq-fiber-extended-iterate refl = refl

  abstract
    is-equiv-Eq-eq-fiber-extended-iterate : {s t : fiber-extended-iterate f b} → is-equiv (Eq-eq-fiber-extended-iterate {s} {t})
    is-equiv-Eq-eq-fiber-extended-iterate =
      is-equiv-is-invertible
        eq-Eq-fiber-extended-iterate-uncurry
        is-section-eq-Eq-fiber-extended-iterate
        is-retraction-eq-Eq-fiber-extended-iterate

  equiv-Eq-eq-fiber-extended-iterate : {s t : fiber-extended-iterate f b} → (s ＝ t) ≃ Eq-fiber-extended-iterate s t
  pr1 equiv-Eq-eq-fiber-extended-iterate = Eq-eq-fiber-extended-iterate
  pr2 equiv-Eq-eq-fiber-extended-iterate = is-equiv-Eq-eq-fiber-extended-iterate

  abstract
    is-equiv-eq-Eq-fiber-extended-iterate :
      {s t : fiber-extended-iterate f b} → is-equiv (eq-Eq-fiber-extended-iterate-uncurry {s} {t})
    is-equiv-eq-Eq-fiber-extended-iterate =
      is-equiv-is-invertible
        Eq-eq-fiber-extended-iterate
        is-retraction-eq-Eq-fiber-extended-iterate
        is-section-eq-Eq-fiber-extended-iterate

  equiv-eq-Eq-fiber-extended-iterate : {s t : fiber-extended-iterate f b} → Eq-fiber-extended-iterate s t ≃ (s ＝ t)
  pr1 equiv-eq-Eq-fiber-extended-iterate = eq-Eq-fiber-extended-iterate-uncurry
  pr2 equiv-eq-Eq-fiber-extended-iterate = is-equiv-eq-Eq-fiber-extended-iterate

  compute-ap-inclusion-fiber-extended-iterate-eq-Eq-fiber-extended-iterate :
    {s t : fiber-extended-iterate f b} (α : pr1 s ＝ pr1 t) (β : ap f α ∙ pr2 t ＝ pr2 s) →
    ap (inclusion-fiber-extended-iterate f) (eq-Eq-fiber-extended-iterate α β) ＝ α
  compute-ap-inclusion-fiber-extended-iterate-eq-Eq-fiber-extended-iterate refl refl = refl
```

#### The case of `fiber-extended-iterate'`

```text
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  Eq-fiber-extended-iterate' : fiber-extended-iterate' f b → fiber-extended-iterate' f b → UU (l1 ⊔ l2)
  Eq-fiber-extended-iterate' s t = Σ (pr1 s ＝ pr1 t) (λ α → pr2 t ＝ pr2 s ∙ ap f α)

  refl-Eq-fiber-extended-iterate' : (s : fiber-extended-iterate' f b) → Eq-fiber-extended-iterate' s s
  pr1 (refl-Eq-fiber-extended-iterate' s) = refl
  pr2 (refl-Eq-fiber-extended-iterate' s) = inv right-unit

  Eq-eq-fiber-extended-iterate' : {s t : fiber-extended-iterate' f b} → s ＝ t → Eq-fiber-extended-iterate' s t
  Eq-eq-fiber-extended-iterate' {s} refl = refl-Eq-fiber-extended-iterate' s

  eq-Eq-fiber-extended-iterate-uncurry' : {s t : fiber-extended-iterate' f b} → Eq-fiber-extended-iterate' s t → s ＝ t
  eq-Eq-fiber-extended-iterate-uncurry' {x , p} (refl , refl) =
    ap (pair _) (inv right-unit)

  eq-Eq-fiber-extended-iterate' :
    {s t : fiber-extended-iterate' f b} (α : pr1 s ＝ pr1 t) → pr2 t ＝ pr2 s ∙ ap f α → s ＝ t
  eq-Eq-fiber-extended-iterate' α β = eq-Eq-fiber-extended-iterate-uncurry' (α , β)

  is-section-eq-Eq-fiber-extended-iterate' :
    {s t : fiber-extended-iterate' f b} →
    is-section (Eq-eq-fiber-extended-iterate' {s} {t}) (eq-Eq-fiber-extended-iterate-uncurry' {s} {t})
  is-section-eq-Eq-fiber-extended-iterate' {x , refl} (refl , refl) = refl

  is-retraction-eq-Eq-fiber-extended-iterate' :
    {s t : fiber-extended-iterate' f b} →
    is-retraction (Eq-eq-fiber-extended-iterate' {s} {t}) (eq-Eq-fiber-extended-iterate-uncurry' {s} {t})
  is-retraction-eq-Eq-fiber-extended-iterate' {x , refl} refl = refl

  abstract
    is-equiv-Eq-eq-fiber-extended-iterate' :
      {s t : fiber-extended-iterate' f b} → is-equiv (Eq-eq-fiber-extended-iterate' {s} {t})
    is-equiv-Eq-eq-fiber-extended-iterate' =
      is-equiv-is-invertible
        eq-Eq-fiber-extended-iterate-uncurry'
        is-section-eq-Eq-fiber-extended-iterate'
        is-retraction-eq-Eq-fiber-extended-iterate'

  equiv-Eq-eq-fiber-extended-iterate' : {s t : fiber-extended-iterate' f b} → (s ＝ t) ≃ Eq-fiber-extended-iterate' s t
  pr1 equiv-Eq-eq-fiber-extended-iterate' = Eq-eq-fiber-extended-iterate'
  pr2 equiv-Eq-eq-fiber-extended-iterate' = is-equiv-Eq-eq-fiber-extended-iterate'

  abstract
    is-equiv-eq-Eq-fiber-extended-iterate' :
      {s t : fiber-extended-iterate' f b} → is-equiv (eq-Eq-fiber-extended-iterate-uncurry' {s} {t})
    is-equiv-eq-Eq-fiber-extended-iterate' =
      is-equiv-is-invertible
        Eq-eq-fiber-extended-iterate'
        is-retraction-eq-Eq-fiber-extended-iterate'
        is-section-eq-Eq-fiber-extended-iterate'

  equiv-eq-Eq-fiber-extended-iterate' : {s t : fiber-extended-iterate' f b} → Eq-fiber-extended-iterate' s t ≃ (s ＝ t)
  pr1 equiv-eq-Eq-fiber-extended-iterate' = eq-Eq-fiber-extended-iterate-uncurry'
  pr2 equiv-eq-Eq-fiber-extended-iterate' = is-equiv-eq-Eq-fiber-extended-iterate'
```

### `fiber-extended-iterate f y` and `fiber-extended-iterate' f y` are equivalent

```text
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (y : B)
  where

  map-equiv-fiber-extended-iterate : fiber-extended-iterate f y → fiber-extended-iterate' f y
  pr1 (map-equiv-fiber-extended-iterate (x , _)) = x
  pr2 (map-equiv-fiber-extended-iterate (x , p)) = inv p

  map-inv-equiv-fiber-extended-iterate : fiber-extended-iterate' f y → fiber-extended-iterate f y
  pr1 (map-inv-equiv-fiber-extended-iterate (x , _)) = x
  pr2 (map-inv-equiv-fiber-extended-iterate (x , p)) = inv p

  is-section-map-inv-equiv-fiber-extended-iterate :
    is-section map-equiv-fiber-extended-iterate map-inv-equiv-fiber-extended-iterate
  is-section-map-inv-equiv-fiber-extended-iterate (x , refl) = refl

  is-retraction-map-inv-equiv-fiber-extended-iterate :
    is-retraction map-equiv-fiber-extended-iterate map-inv-equiv-fiber-extended-iterate
  is-retraction-map-inv-equiv-fiber-extended-iterate (x , refl) = refl

  is-equiv-map-equiv-fiber-extended-iterate : is-equiv map-equiv-fiber-extended-iterate
  is-equiv-map-equiv-fiber-extended-iterate =
    is-equiv-is-invertible
      map-inv-equiv-fiber-extended-iterate
      is-section-map-inv-equiv-fiber-extended-iterate
      is-retraction-map-inv-equiv-fiber-extended-iterate

  equiv-fiber-extended-iterate : fiber-extended-iterate f y ≃ fiber-extended-iterate' f y
  pr1 equiv-fiber-extended-iterate = map-equiv-fiber-extended-iterate
  pr2 equiv-fiber-extended-iterate = is-equiv-map-equiv-fiber-extended-iterate
```

### Computing the fibers of a projection map

```text
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (a : A)
  where

  map-fiber-extended-iterate-pr1 : fiber-extended-iterate (pr1 {B = B}) a → B a
  map-fiber-extended-iterate-pr1 ((x , y) , p) = tr B p y

  map-inv-fiber-extended-iterate-pr1 : B a → fiber-extended-iterate (pr1 {B = B}) a
  map-inv-fiber-extended-iterate-pr1 b = (a , b) , refl

  is-section-map-inv-fiber-extended-iterate-pr1 :
    is-section map-fiber-extended-iterate-pr1 map-inv-fiber-extended-iterate-pr1
  is-section-map-inv-fiber-extended-iterate-pr1 b = refl

  is-retraction-map-inv-fiber-extended-iterate-pr1 :
    is-retraction map-fiber-extended-iterate-pr1 map-inv-fiber-extended-iterate-pr1
  is-retraction-map-inv-fiber-extended-iterate-pr1 ((.a , y) , refl) = refl

  abstract
    is-equiv-map-fiber-extended-iterate-pr1 : is-equiv map-fiber-extended-iterate-pr1
    is-equiv-map-fiber-extended-iterate-pr1 =
      is-equiv-is-invertible
        map-inv-fiber-extended-iterate-pr1
        is-section-map-inv-fiber-extended-iterate-pr1
        is-retraction-map-inv-fiber-extended-iterate-pr1

  equiv-fiber-extended-iterate-pr1 : fiber-extended-iterate (pr1 {B = B}) a ≃ B a
  pr1 equiv-fiber-extended-iterate-pr1 = map-fiber-extended-iterate-pr1
  pr2 equiv-fiber-extended-iterate-pr1 = is-equiv-map-fiber-extended-iterate-pr1

  abstract
    is-equiv-map-inv-fiber-extended-iterate-pr1 : is-equiv map-inv-fiber-extended-iterate-pr1
    is-equiv-map-inv-fiber-extended-iterate-pr1 =
      is-equiv-is-invertible
        map-fiber-extended-iterate-pr1
        is-retraction-map-inv-fiber-extended-iterate-pr1
        is-section-map-inv-fiber-extended-iterate-pr1

  inv-equiv-fiber-extended-iterate-pr1 : B a ≃ fiber-extended-iterate (pr1 {B = B}) a
  pr1 inv-equiv-fiber-extended-iterate-pr1 = map-inv-fiber-extended-iterate-pr1
  pr2 inv-equiv-fiber-extended-iterate-pr1 = is-equiv-map-inv-fiber-extended-iterate-pr1
```

### The total space of fibers

```text
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  map-equiv-total-fiber-extended-iterate : Σ B (fiber-extended-iterate f) → A
  map-equiv-total-fiber-extended-iterate t = pr1 (pr2 t)

  triangle-map-equiv-total-fiber-extended-iterate : pr1 ~ f ∘ map-equiv-total-fiber-extended-iterate
  triangle-map-equiv-total-fiber-extended-iterate t = inv (pr2 (pr2 t))

  map-inv-equiv-total-fiber-extended-iterate : A → Σ B (fiber-extended-iterate f)
  pr1 (map-inv-equiv-total-fiber-extended-iterate x) = f x
  pr1 (pr2 (map-inv-equiv-total-fiber-extended-iterate x)) = x
  pr2 (pr2 (map-inv-equiv-total-fiber-extended-iterate x)) = refl

  is-retraction-map-inv-equiv-total-fiber-extended-iterate :
    is-retraction map-equiv-total-fiber-extended-iterate map-inv-equiv-total-fiber-extended-iterate
  is-retraction-map-inv-equiv-total-fiber-extended-iterate (.(f x) , x , refl) = refl

  is-section-map-inv-equiv-total-fiber-extended-iterate :
    is-section map-equiv-total-fiber-extended-iterate map-inv-equiv-total-fiber-extended-iterate
  is-section-map-inv-equiv-total-fiber-extended-iterate x = refl

  abstract
    is-equiv-map-equiv-total-fiber-extended-iterate : is-equiv map-equiv-total-fiber-extended-iterate
    is-equiv-map-equiv-total-fiber-extended-iterate =
      is-equiv-is-invertible
        map-inv-equiv-total-fiber-extended-iterate
        is-section-map-inv-equiv-total-fiber-extended-iterate
        is-retraction-map-inv-equiv-total-fiber-extended-iterate

    is-equiv-map-inv-equiv-total-fiber-extended-iterate : is-equiv map-inv-equiv-total-fiber-extended-iterate
    is-equiv-map-inv-equiv-total-fiber-extended-iterate =
      is-equiv-is-invertible
        map-equiv-total-fiber-extended-iterate
        is-retraction-map-inv-equiv-total-fiber-extended-iterate
        is-section-map-inv-equiv-total-fiber-extended-iterate

  equiv-total-fiber-extended-iterate : Σ B (fiber-extended-iterate f) ≃ A
  pr1 equiv-total-fiber-extended-iterate = map-equiv-total-fiber-extended-iterate
  pr2 equiv-total-fiber-extended-iterate = is-equiv-map-equiv-total-fiber-extended-iterate

  inv-equiv-total-fiber-extended-iterate : A ≃ Σ B (fiber-extended-iterate f)
  pr1 inv-equiv-total-fiber-extended-iterate = map-inv-equiv-total-fiber-extended-iterate
  pr2 inv-equiv-total-fiber-extended-iterate = is-equiv-map-inv-equiv-total-fiber-extended-iterate
```

### Fibers of compositions

```text
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (g : B → X) (h : A → B) (x : X)
  where

  map-compute-fiber-extended-iterate-comp :
    fiber-extended-iterate (g ∘ h) x → Σ (fiber-extended-iterate g x) (λ t → fiber-extended-iterate h (pr1 t))
  pr1 (pr1 (map-compute-fiber-extended-iterate-comp (a , p))) = h a
  pr2 (pr1 (map-compute-fiber-extended-iterate-comp (a , p))) = p
  pr1 (pr2 (map-compute-fiber-extended-iterate-comp (a , p))) = a
  pr2 (pr2 (map-compute-fiber-extended-iterate-comp (a , p))) = refl

  map-inv-compute-fiber-extended-iterate-comp :
    Σ (fiber-extended-iterate g x) (λ t → fiber-extended-iterate h (pr1 t)) → fiber-extended-iterate (g ∘ h) x
  pr1 (map-inv-compute-fiber-extended-iterate-comp t) = pr1 (pr2 t)
  pr2 (map-inv-compute-fiber-extended-iterate-comp t) = ap g (pr2 (pr2 t)) ∙ pr2 (pr1 t)

  is-section-map-inv-compute-fiber-extended-iterate-comp :
    is-section map-compute-fiber-extended-iterate-comp map-inv-compute-fiber-extended-iterate-comp
  is-section-map-inv-compute-fiber-extended-iterate-comp ((.(h a) , refl) , (a , refl)) = refl

  is-retraction-map-inv-compute-fiber-extended-iterate-comp :
    is-retraction map-compute-fiber-extended-iterate-comp map-inv-compute-fiber-extended-iterate-comp
  is-retraction-map-inv-compute-fiber-extended-iterate-comp (a , refl) = refl

  abstract
    is-equiv-map-compute-fiber-extended-iterate-comp :
      is-equiv map-compute-fiber-extended-iterate-comp
    is-equiv-map-compute-fiber-extended-iterate-comp =
      is-equiv-is-invertible
        ( map-inv-compute-fiber-extended-iterate-comp)
        ( is-section-map-inv-compute-fiber-extended-iterate-comp)
        ( is-retraction-map-inv-compute-fiber-extended-iterate-comp)

  compute-fiber-extended-iterate-comp :
    fiber-extended-iterate (g ∘ h) x ≃ Σ (fiber-extended-iterate g x) (λ t → fiber-extended-iterate h (pr1 t))
  pr1 compute-fiber-extended-iterate-comp = map-compute-fiber-extended-iterate-comp
  pr2 compute-fiber-extended-iterate-comp = is-equiv-map-compute-fiber-extended-iterate-comp

  abstract
    is-equiv-map-inv-compute-fiber-extended-iterate-comp :
      is-equiv map-inv-compute-fiber-extended-iterate-comp
    is-equiv-map-inv-compute-fiber-extended-iterate-comp =
        is-equiv-is-invertible
          ( map-compute-fiber-extended-iterate-comp)
          ( is-retraction-map-inv-compute-fiber-extended-iterate-comp)
          ( is-section-map-inv-compute-fiber-extended-iterate-comp)

  inv-compute-fiber-extended-iterate-comp :
    Σ (fiber-extended-iterate g x) (λ t → fiber-extended-iterate h (pr1 t)) ≃ fiber-extended-iterate (g ∘ h) x
  pr1 inv-compute-fiber-extended-iterate-comp = map-inv-compute-fiber-extended-iterate-comp
  pr2 inv-compute-fiber-extended-iterate-comp = is-equiv-map-inv-compute-fiber-extended-iterate-comp
```

### Fibers of homotopic maps are equivalent

```text
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f g : A → B} (H : g ~ f) (y : B)
  where

  map-equiv-fiber-extended-iterate-htpy : fiber-extended-iterate f y → fiber-extended-iterate g y
  map-equiv-fiber-extended-iterate-htpy (x , p) = x , H x ∙ᵣ p

  map-inv-equiv-fiber-extended-iterate-htpy : fiber-extended-iterate g y → fiber-extended-iterate f y
  map-inv-equiv-fiber-extended-iterate-htpy (x , p) = x , inv (H x) ∙ᵣ p

  is-section-map-inv-equiv-fiber-extended-iterate-htpy :
    is-section map-equiv-fiber-extended-iterate-htpy map-inv-equiv-fiber-extended-iterate-htpy
  is-section-map-inv-equiv-fiber-extended-iterate-htpy (x , refl) =
    eq-Eq-fiber-extended-iterate g (g x) refl (inv (right-inv-right-strict-concat (H x)))

  is-retraction-map-inv-equiv-fiber-extended-iterate-htpy :
    is-retraction map-equiv-fiber-extended-iterate-htpy map-inv-equiv-fiber-extended-iterate-htpy
  is-retraction-map-inv-equiv-fiber-extended-iterate-htpy (x , refl) =
    eq-Eq-fiber-extended-iterate f (f x) refl (inv (left-inv-right-strict-concat (H x)))

  is-equiv-map-equiv-fiber-extended-iterate-htpy : is-equiv map-equiv-fiber-extended-iterate-htpy
  is-equiv-map-equiv-fiber-extended-iterate-htpy =
    is-equiv-is-invertible
      map-inv-equiv-fiber-extended-iterate-htpy
      is-section-map-inv-equiv-fiber-extended-iterate-htpy
      is-retraction-map-inv-equiv-fiber-extended-iterate-htpy

  equiv-fiber-extended-iterate-htpy : fiber-extended-iterate f y ≃ fiber-extended-iterate g y
  equiv-fiber-extended-iterate-htpy = map-equiv-fiber-extended-iterate-htpy , is-equiv-map-equiv-fiber-extended-iterate-htpy
```

We repeat the construction for `fiber-extended-iterate'`.

```text
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f g : A → B} (H : g ~ f) (y : B)
  where

  map-equiv-fiber-extended-iterate-htpy' : fiber-extended-iterate' f y → fiber-extended-iterate' g y
  map-equiv-fiber-extended-iterate-htpy' (x , p) = (x , p ∙ inv (H x))

  map-inv-equiv-fiber-extended-iterate-htpy' : fiber-extended-iterate' g y → fiber-extended-iterate' f y
  map-inv-equiv-fiber-extended-iterate-htpy' (x , p) = (x , p ∙ H x)

  is-section-map-inv-equiv-fiber-extended-iterate-htpy' :
    is-section map-equiv-fiber-extended-iterate-htpy' map-inv-equiv-fiber-extended-iterate-htpy'
  is-section-map-inv-equiv-fiber-extended-iterate-htpy' (x , p) =
    ap (pair x) (is-retraction-inv-concat' (H x) p)

  is-retraction-map-inv-equiv-fiber-extended-iterate-htpy' :
    is-retraction map-equiv-fiber-extended-iterate-htpy' map-inv-equiv-fiber-extended-iterate-htpy'
  is-retraction-map-inv-equiv-fiber-extended-iterate-htpy' (x , p) =
    ap (pair x) (is-section-inv-concat' (H x) p)

  is-equiv-map-equiv-fiber-extended-iterate-htpy' : is-equiv map-equiv-fiber-extended-iterate-htpy'
  is-equiv-map-equiv-fiber-extended-iterate-htpy' =
    is-equiv-is-invertible
      map-inv-equiv-fiber-extended-iterate-htpy'
      is-section-map-inv-equiv-fiber-extended-iterate-htpy'
      is-retraction-map-inv-equiv-fiber-extended-iterate-htpy'

  equiv-fiber-extended-iterate-htpy' : fiber-extended-iterate' f y ≃ fiber-extended-iterate' g y
  equiv-fiber-extended-iterate-htpy' = map-equiv-fiber-extended-iterate-htpy' , is-equiv-map-equiv-fiber-extended-iterate-htpy'
```

## Table of files about fibers of maps

The following table lists files that are about fibers of maps as a general
concept.

{{#include tables/fibers-of-maps.md}}
