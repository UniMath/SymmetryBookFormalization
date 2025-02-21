# Fibers of transfinitely iterated maps

```agda
module foundation.fibers-of-transfinitely-iterated-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import set-theory.increasing-binary-sequences
open import set-theory.inequality-increasing-binary-sequences
open import set-theory.bounded-increasing-binary-sequences
open import foundation.strictly-right-unital-concatenation-identifications
open import foundation.decidable-embeddings
open import foundation.coproduct-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.cartesian-product-types
open import foundation.decidable-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.identity-types
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
{{#concept "fiber-transfinite-iterate" Disambiguation="of the extended iterated map" }}
of `fⁿ` at `b` can be recorded by the data

```text
  fⁿ xₙ ＝ ⋯ ＝ f² x₂ ＝ f x₁ ＝ x₀ ＝ b
```

## Definition

```agda
module _
  {l1 : Level} {A : UU l1} (f : A → A) (b : A)
  where

  fiber-transfinite-iterate : UU l1
  fiber-transfinite-iterate =
    Σ ( ℕ∞↑ → A)
      ( λ x → (f (x zero-ℕ∞↑) ＝ b) × ((k : ℕ∞↑) → f (x (succ-ℕ∞↑ (succ-ℕ∞↑ k))) ＝ x (succ-ℕ∞↑ k)))

  fiber-transfinite-iterate' : UU l1
  fiber-transfinite-iterate' =
   Σ (ℕ∞↑ → A)
    ( λ x → (b ＝ f (x zero-ℕ∞↑)) × ((k : ℕ∞↑) → x k ＝ f (x (succ-ℕ∞↑ k))))


module _
  {l1 : Level} {A : UU l1} (f : A → A) (b : A)
  where

  sequence-fiber-transfinite-iterate :
    fiber-transfinite-iterate f b → ℕ∞↑ → A
  sequence-fiber-transfinite-iterate = pr1

  inclusion-fiber-transfinite-iterate : fiber-transfinite-iterate f b → A
  inclusion-fiber-transfinite-iterate p =
    sequence-fiber-transfinite-iterate p infinity-ℕ∞↑
```

## Properties

### If the fibers of `f` are decidable then so is `fiber-transfinite-iterate f`

```agda
module _
  {l1 : Level} {A : UU l1} (f : A → A) (F : is-decidable-emb f)
  where


  is-decidable-fiber-transfinite-iterate :
    (b : A) → is-decidable (fiber-transfinite-iterate f b)
  is-decidable-fiber-transfinite-iterate b =
    rec-coproduct (λ p → is-decidable-fiber-transfinite-iterate {!   !}) (λ np → inr λ p' → np (sequence-fiber-transfinite-iterate f b p' zero-ℕ∞↑ , pr1 (pr2 p'))) (is-decidable-map-is-decidable-emb F b)

  is-prop-fiber-transfinite-iterate :
    (b : A) → is-prop (fiber-transfinite-iterate f b)
  is-prop-fiber-transfinite-iterate b =
    is-prop-is-proof-irrelevant (λ p → {!   !}) -- requires characterizing the identity type
```

### Characterization of the identity types of the fibers of a map

#### The case of `fiber-transfinite-iterate`

```text
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  Eq-fiber-transfinite-iterate : fiber-transfinite-iterate f b → fiber-transfinite-iterate f b → UU (l1 ⊔ l2)
  Eq-fiber-transfinite-iterate s t = Σ (pr1 s ＝ pr1 t) (λ α → ap f α ∙ pr2 t ＝ pr2 s)

  refl-Eq-fiber-transfinite-iterate : (s : fiber-transfinite-iterate f b) → Eq-fiber-transfinite-iterate s s
  pr1 (refl-Eq-fiber-transfinite-iterate s) = refl
  pr2 (refl-Eq-fiber-transfinite-iterate s) = refl

  Eq-eq-fiber-transfinite-iterate : {s t : fiber-transfinite-iterate f b} → s ＝ t → Eq-fiber-transfinite-iterate s t
  Eq-eq-fiber-transfinite-iterate {s} refl = refl-Eq-fiber-transfinite-iterate s

  eq-Eq-fiber-transfinite-iterate-uncurry : {s t : fiber-transfinite-iterate f b} → Eq-fiber-transfinite-iterate s t → s ＝ t
  eq-Eq-fiber-transfinite-iterate-uncurry (refl , refl) = refl

  eq-Eq-fiber-transfinite-iterate :
    {s t : fiber-transfinite-iterate f b} (α : pr1 s ＝ pr1 t) → ap f α ∙ pr2 t ＝ pr2 s → s ＝ t
  eq-Eq-fiber-transfinite-iterate α β = eq-Eq-fiber-transfinite-iterate-uncurry (α , β)

  is-section-eq-Eq-fiber-transfinite-iterate :
    {s t : fiber-transfinite-iterate f b} →
    is-section (Eq-eq-fiber-transfinite-iterate {s} {t}) (eq-Eq-fiber-transfinite-iterate-uncurry {s} {t})
  is-section-eq-Eq-fiber-transfinite-iterate (refl , refl) = refl

  is-retraction-eq-Eq-fiber-transfinite-iterate :
    {s t : fiber-transfinite-iterate f b} →
    is-retraction (Eq-eq-fiber-transfinite-iterate {s} {t}) (eq-Eq-fiber-transfinite-iterate-uncurry {s} {t})
  is-retraction-eq-Eq-fiber-transfinite-iterate refl = refl

  abstract
    is-equiv-Eq-eq-fiber-transfinite-iterate : {s t : fiber-transfinite-iterate f b} → is-equiv (Eq-eq-fiber-transfinite-iterate {s} {t})
    is-equiv-Eq-eq-fiber-transfinite-iterate =
      is-equiv-is-invertible
        eq-Eq-fiber-transfinite-iterate-uncurry
        is-section-eq-Eq-fiber-transfinite-iterate
        is-retraction-eq-Eq-fiber-transfinite-iterate

  equiv-Eq-eq-fiber-transfinite-iterate : {s t : fiber-transfinite-iterate f b} → (s ＝ t) ≃ Eq-fiber-transfinite-iterate s t
  pr1 equiv-Eq-eq-fiber-transfinite-iterate = Eq-eq-fiber-transfinite-iterate
  pr2 equiv-Eq-eq-fiber-transfinite-iterate = is-equiv-Eq-eq-fiber-transfinite-iterate

  abstract
    is-equiv-eq-Eq-fiber-transfinite-iterate :
      {s t : fiber-transfinite-iterate f b} → is-equiv (eq-Eq-fiber-transfinite-iterate-uncurry {s} {t})
    is-equiv-eq-Eq-fiber-transfinite-iterate =
      is-equiv-is-invertible
        Eq-eq-fiber-transfinite-iterate
        is-retraction-eq-Eq-fiber-transfinite-iterate
        is-section-eq-Eq-fiber-transfinite-iterate

  equiv-eq-Eq-fiber-transfinite-iterate : {s t : fiber-transfinite-iterate f b} → Eq-fiber-transfinite-iterate s t ≃ (s ＝ t)
  pr1 equiv-eq-Eq-fiber-transfinite-iterate = eq-Eq-fiber-transfinite-iterate-uncurry
  pr2 equiv-eq-Eq-fiber-transfinite-iterate = is-equiv-eq-Eq-fiber-transfinite-iterate

  compute-ap-inclusion-fiber-transfinite-iterate-eq-Eq-fiber-transfinite-iterate :
    {s t : fiber-transfinite-iterate f b} (α : pr1 s ＝ pr1 t) (β : ap f α ∙ pr2 t ＝ pr2 s) →
    ap (inclusion-fiber-transfinite-iterate f) (eq-Eq-fiber-transfinite-iterate α β) ＝ α
  compute-ap-inclusion-fiber-transfinite-iterate-eq-Eq-fiber-transfinite-iterate refl refl = refl
```

#### The case of `fiber-transfinite-iterate'`

```text
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  Eq-fiber-transfinite-iterate' : fiber-transfinite-iterate' f b → fiber-transfinite-iterate' f b → UU (l1 ⊔ l2)
  Eq-fiber-transfinite-iterate' s t = Σ (pr1 s ＝ pr1 t) (λ α → pr2 t ＝ pr2 s ∙ ap f α)

  refl-Eq-fiber-transfinite-iterate' : (s : fiber-transfinite-iterate' f b) → Eq-fiber-transfinite-iterate' s s
  pr1 (refl-Eq-fiber-transfinite-iterate' s) = refl
  pr2 (refl-Eq-fiber-transfinite-iterate' s) = inv right-unit

  Eq-eq-fiber-transfinite-iterate' : {s t : fiber-transfinite-iterate' f b} → s ＝ t → Eq-fiber-transfinite-iterate' s t
  Eq-eq-fiber-transfinite-iterate' {s} refl = refl-Eq-fiber-transfinite-iterate' s

  eq-Eq-fiber-transfinite-iterate-uncurry' : {s t : fiber-transfinite-iterate' f b} → Eq-fiber-transfinite-iterate' s t → s ＝ t
  eq-Eq-fiber-transfinite-iterate-uncurry' {x , p} (refl , refl) =
    ap (pair _) (inv right-unit)

  eq-Eq-fiber-transfinite-iterate' :
    {s t : fiber-transfinite-iterate' f b} (α : pr1 s ＝ pr1 t) → pr2 t ＝ pr2 s ∙ ap f α → s ＝ t
  eq-Eq-fiber-transfinite-iterate' α β = eq-Eq-fiber-transfinite-iterate-uncurry' (α , β)

  is-section-eq-Eq-fiber-transfinite-iterate' :
    {s t : fiber-transfinite-iterate' f b} →
    is-section (Eq-eq-fiber-transfinite-iterate' {s} {t}) (eq-Eq-fiber-transfinite-iterate-uncurry' {s} {t})
  is-section-eq-Eq-fiber-transfinite-iterate' {x , refl} (refl , refl) = refl

  is-retraction-eq-Eq-fiber-transfinite-iterate' :
    {s t : fiber-transfinite-iterate' f b} →
    is-retraction (Eq-eq-fiber-transfinite-iterate' {s} {t}) (eq-Eq-fiber-transfinite-iterate-uncurry' {s} {t})
  is-retraction-eq-Eq-fiber-transfinite-iterate' {x , refl} refl = refl

  abstract
    is-equiv-Eq-eq-fiber-transfinite-iterate' :
      {s t : fiber-transfinite-iterate' f b} → is-equiv (Eq-eq-fiber-transfinite-iterate' {s} {t})
    is-equiv-Eq-eq-fiber-transfinite-iterate' =
      is-equiv-is-invertible
        eq-Eq-fiber-transfinite-iterate-uncurry'
        is-section-eq-Eq-fiber-transfinite-iterate'
        is-retraction-eq-Eq-fiber-transfinite-iterate'

  equiv-Eq-eq-fiber-transfinite-iterate' : {s t : fiber-transfinite-iterate' f b} → (s ＝ t) ≃ Eq-fiber-transfinite-iterate' s t
  pr1 equiv-Eq-eq-fiber-transfinite-iterate' = Eq-eq-fiber-transfinite-iterate'
  pr2 equiv-Eq-eq-fiber-transfinite-iterate' = is-equiv-Eq-eq-fiber-transfinite-iterate'

  abstract
    is-equiv-eq-Eq-fiber-transfinite-iterate' :
      {s t : fiber-transfinite-iterate' f b} → is-equiv (eq-Eq-fiber-transfinite-iterate-uncurry' {s} {t})
    is-equiv-eq-Eq-fiber-transfinite-iterate' =
      is-equiv-is-invertible
        Eq-eq-fiber-transfinite-iterate'
        is-retraction-eq-Eq-fiber-transfinite-iterate'
        is-section-eq-Eq-fiber-transfinite-iterate'

  equiv-eq-Eq-fiber-transfinite-iterate' : {s t : fiber-transfinite-iterate' f b} → Eq-fiber-transfinite-iterate' s t ≃ (s ＝ t)
  pr1 equiv-eq-Eq-fiber-transfinite-iterate' = eq-Eq-fiber-transfinite-iterate-uncurry'
  pr2 equiv-eq-Eq-fiber-transfinite-iterate' = is-equiv-eq-Eq-fiber-transfinite-iterate'
```

### `fiber-transfinite-iterate f y` and `fiber-transfinite-iterate' f y` are equivalent

```text
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (y : B)
  where

  map-equiv-fiber-transfinite-iterate : fiber-transfinite-iterate f y → fiber-transfinite-iterate' f y
  pr1 (map-equiv-fiber-transfinite-iterate (x , _)) = x
  pr2 (map-equiv-fiber-transfinite-iterate (x , p)) = inv p

  map-inv-equiv-fiber-transfinite-iterate : fiber-transfinite-iterate' f y → fiber-transfinite-iterate f y
  pr1 (map-inv-equiv-fiber-transfinite-iterate (x , _)) = x
  pr2 (map-inv-equiv-fiber-transfinite-iterate (x , p)) = inv p

  is-section-map-inv-equiv-fiber-transfinite-iterate :
    is-section map-equiv-fiber-transfinite-iterate map-inv-equiv-fiber-transfinite-iterate
  is-section-map-inv-equiv-fiber-transfinite-iterate (x , refl) = refl

  is-retraction-map-inv-equiv-fiber-transfinite-iterate :
    is-retraction map-equiv-fiber-transfinite-iterate map-inv-equiv-fiber-transfinite-iterate
  is-retraction-map-inv-equiv-fiber-transfinite-iterate (x , refl) = refl

  is-equiv-map-equiv-fiber-transfinite-iterate : is-equiv map-equiv-fiber-transfinite-iterate
  is-equiv-map-equiv-fiber-transfinite-iterate =
    is-equiv-is-invertible
      map-inv-equiv-fiber-transfinite-iterate
      is-section-map-inv-equiv-fiber-transfinite-iterate
      is-retraction-map-inv-equiv-fiber-transfinite-iterate

  equiv-fiber-transfinite-iterate : fiber-transfinite-iterate f y ≃ fiber-transfinite-iterate' f y
  pr1 equiv-fiber-transfinite-iterate = map-equiv-fiber-transfinite-iterate
  pr2 equiv-fiber-transfinite-iterate = is-equiv-map-equiv-fiber-transfinite-iterate
```

### Computing the fibers of a projection map

```text
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (a : A)
  where

  map-fiber-transfinite-iterate-pr1 : fiber-transfinite-iterate (pr1 {B = B}) a → B a
  map-fiber-transfinite-iterate-pr1 ((x , y) , p) = tr B p y

  map-inv-fiber-transfinite-iterate-pr1 : B a → fiber-transfinite-iterate (pr1 {B = B}) a
  map-inv-fiber-transfinite-iterate-pr1 b = (a , b) , refl

  is-section-map-inv-fiber-transfinite-iterate-pr1 :
    is-section map-fiber-transfinite-iterate-pr1 map-inv-fiber-transfinite-iterate-pr1
  is-section-map-inv-fiber-transfinite-iterate-pr1 b = refl

  is-retraction-map-inv-fiber-transfinite-iterate-pr1 :
    is-retraction map-fiber-transfinite-iterate-pr1 map-inv-fiber-transfinite-iterate-pr1
  is-retraction-map-inv-fiber-transfinite-iterate-pr1 ((.a , y) , refl) = refl

  abstract
    is-equiv-map-fiber-transfinite-iterate-pr1 : is-equiv map-fiber-transfinite-iterate-pr1
    is-equiv-map-fiber-transfinite-iterate-pr1 =
      is-equiv-is-invertible
        map-inv-fiber-transfinite-iterate-pr1
        is-section-map-inv-fiber-transfinite-iterate-pr1
        is-retraction-map-inv-fiber-transfinite-iterate-pr1

  equiv-fiber-transfinite-iterate-pr1 : fiber-transfinite-iterate (pr1 {B = B}) a ≃ B a
  pr1 equiv-fiber-transfinite-iterate-pr1 = map-fiber-transfinite-iterate-pr1
  pr2 equiv-fiber-transfinite-iterate-pr1 = is-equiv-map-fiber-transfinite-iterate-pr1

  abstract
    is-equiv-map-inv-fiber-transfinite-iterate-pr1 : is-equiv map-inv-fiber-transfinite-iterate-pr1
    is-equiv-map-inv-fiber-transfinite-iterate-pr1 =
      is-equiv-is-invertible
        map-fiber-transfinite-iterate-pr1
        is-retraction-map-inv-fiber-transfinite-iterate-pr1
        is-section-map-inv-fiber-transfinite-iterate-pr1

  inv-equiv-fiber-transfinite-iterate-pr1 : B a ≃ fiber-transfinite-iterate (pr1 {B = B}) a
  pr1 inv-equiv-fiber-transfinite-iterate-pr1 = map-inv-fiber-transfinite-iterate-pr1
  pr2 inv-equiv-fiber-transfinite-iterate-pr1 = is-equiv-map-inv-fiber-transfinite-iterate-pr1
```

### The total space of fibers

```text
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  map-equiv-total-fiber-transfinite-iterate : Σ B (fiber-transfinite-iterate f) → A
  map-equiv-total-fiber-transfinite-iterate t = pr1 (pr2 t)

  triangle-map-equiv-total-fiber-transfinite-iterate : pr1 ~ f ∘ map-equiv-total-fiber-transfinite-iterate
  triangle-map-equiv-total-fiber-transfinite-iterate t = inv (pr2 (pr2 t))

  map-inv-equiv-total-fiber-transfinite-iterate : A → Σ B (fiber-transfinite-iterate f)
  pr1 (map-inv-equiv-total-fiber-transfinite-iterate x) = f x
  pr1 (pr2 (map-inv-equiv-total-fiber-transfinite-iterate x)) = x
  pr2 (pr2 (map-inv-equiv-total-fiber-transfinite-iterate x)) = refl

  is-retraction-map-inv-equiv-total-fiber-transfinite-iterate :
    is-retraction map-equiv-total-fiber-transfinite-iterate map-inv-equiv-total-fiber-transfinite-iterate
  is-retraction-map-inv-equiv-total-fiber-transfinite-iterate (.(f x) , x , refl) = refl

  is-section-map-inv-equiv-total-fiber-transfinite-iterate :
    is-section map-equiv-total-fiber-transfinite-iterate map-inv-equiv-total-fiber-transfinite-iterate
  is-section-map-inv-equiv-total-fiber-transfinite-iterate x = refl

  abstract
    is-equiv-map-equiv-total-fiber-transfinite-iterate : is-equiv map-equiv-total-fiber-transfinite-iterate
    is-equiv-map-equiv-total-fiber-transfinite-iterate =
      is-equiv-is-invertible
        map-inv-equiv-total-fiber-transfinite-iterate
        is-section-map-inv-equiv-total-fiber-transfinite-iterate
        is-retraction-map-inv-equiv-total-fiber-transfinite-iterate

    is-equiv-map-inv-equiv-total-fiber-transfinite-iterate : is-equiv map-inv-equiv-total-fiber-transfinite-iterate
    is-equiv-map-inv-equiv-total-fiber-transfinite-iterate =
      is-equiv-is-invertible
        map-equiv-total-fiber-transfinite-iterate
        is-retraction-map-inv-equiv-total-fiber-transfinite-iterate
        is-section-map-inv-equiv-total-fiber-transfinite-iterate

  equiv-total-fiber-transfinite-iterate : Σ B (fiber-transfinite-iterate f) ≃ A
  pr1 equiv-total-fiber-transfinite-iterate = map-equiv-total-fiber-transfinite-iterate
  pr2 equiv-total-fiber-transfinite-iterate = is-equiv-map-equiv-total-fiber-transfinite-iterate

  inv-equiv-total-fiber-transfinite-iterate : A ≃ Σ B (fiber-transfinite-iterate f)
  pr1 inv-equiv-total-fiber-transfinite-iterate = map-inv-equiv-total-fiber-transfinite-iterate
  pr2 inv-equiv-total-fiber-transfinite-iterate = is-equiv-map-inv-equiv-total-fiber-transfinite-iterate
```

### Fibers of compositions

```text
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (g : B → X) (h : A → B) (x : X)
  where

  map-compute-fiber-transfinite-iterate-comp :
    fiber-transfinite-iterate (g ∘ h) x → Σ (fiber-transfinite-iterate g x) (λ t → fiber-transfinite-iterate h (pr1 t))
  pr1 (pr1 (map-compute-fiber-transfinite-iterate-comp (a , p))) = h a
  pr2 (pr1 (map-compute-fiber-transfinite-iterate-comp (a , p))) = p
  pr1 (pr2 (map-compute-fiber-transfinite-iterate-comp (a , p))) = a
  pr2 (pr2 (map-compute-fiber-transfinite-iterate-comp (a , p))) = refl

  map-inv-compute-fiber-transfinite-iterate-comp :
    Σ (fiber-transfinite-iterate g x) (λ t → fiber-transfinite-iterate h (pr1 t)) → fiber-transfinite-iterate (g ∘ h) x
  pr1 (map-inv-compute-fiber-transfinite-iterate-comp t) = pr1 (pr2 t)
  pr2 (map-inv-compute-fiber-transfinite-iterate-comp t) = ap g (pr2 (pr2 t)) ∙ pr2 (pr1 t)

  is-section-map-inv-compute-fiber-transfinite-iterate-comp :
    is-section map-compute-fiber-transfinite-iterate-comp map-inv-compute-fiber-transfinite-iterate-comp
  is-section-map-inv-compute-fiber-transfinite-iterate-comp ((.(h a) , refl) , (a , refl)) = refl

  is-retraction-map-inv-compute-fiber-transfinite-iterate-comp :
    is-retraction map-compute-fiber-transfinite-iterate-comp map-inv-compute-fiber-transfinite-iterate-comp
  is-retraction-map-inv-compute-fiber-transfinite-iterate-comp (a , refl) = refl

  abstract
    is-equiv-map-compute-fiber-transfinite-iterate-comp :
      is-equiv map-compute-fiber-transfinite-iterate-comp
    is-equiv-map-compute-fiber-transfinite-iterate-comp =
      is-equiv-is-invertible
        ( map-inv-compute-fiber-transfinite-iterate-comp)
        ( is-section-map-inv-compute-fiber-transfinite-iterate-comp)
        ( is-retraction-map-inv-compute-fiber-transfinite-iterate-comp)

  compute-fiber-transfinite-iterate-comp :
    fiber-transfinite-iterate (g ∘ h) x ≃ Σ (fiber-transfinite-iterate g x) (λ t → fiber-transfinite-iterate h (pr1 t))
  pr1 compute-fiber-transfinite-iterate-comp = map-compute-fiber-transfinite-iterate-comp
  pr2 compute-fiber-transfinite-iterate-comp = is-equiv-map-compute-fiber-transfinite-iterate-comp

  abstract
    is-equiv-map-inv-compute-fiber-transfinite-iterate-comp :
      is-equiv map-inv-compute-fiber-transfinite-iterate-comp
    is-equiv-map-inv-compute-fiber-transfinite-iterate-comp =
        is-equiv-is-invertible
          ( map-compute-fiber-transfinite-iterate-comp)
          ( is-retraction-map-inv-compute-fiber-transfinite-iterate-comp)
          ( is-section-map-inv-compute-fiber-transfinite-iterate-comp)

  inv-compute-fiber-transfinite-iterate-comp :
    Σ (fiber-transfinite-iterate g x) (λ t → fiber-transfinite-iterate h (pr1 t)) ≃ fiber-transfinite-iterate (g ∘ h) x
  pr1 inv-compute-fiber-transfinite-iterate-comp = map-inv-compute-fiber-transfinite-iterate-comp
  pr2 inv-compute-fiber-transfinite-iterate-comp = is-equiv-map-inv-compute-fiber-transfinite-iterate-comp
```

### Fibers of homotopic maps are equivalent

```text
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f g : A → B} (H : g ~ f) (y : B)
  where

  map-equiv-fiber-transfinite-iterate-htpy : fiber-transfinite-iterate f y → fiber-transfinite-iterate g y
  map-equiv-fiber-transfinite-iterate-htpy (x , p) = x , H x ∙ᵣ p

  map-inv-equiv-fiber-transfinite-iterate-htpy : fiber-transfinite-iterate g y → fiber-transfinite-iterate f y
  map-inv-equiv-fiber-transfinite-iterate-htpy (x , p) = x , inv (H x) ∙ᵣ p

  is-section-map-inv-equiv-fiber-transfinite-iterate-htpy :
    is-section map-equiv-fiber-transfinite-iterate-htpy map-inv-equiv-fiber-transfinite-iterate-htpy
  is-section-map-inv-equiv-fiber-transfinite-iterate-htpy (x , refl) =
    eq-Eq-fiber-transfinite-iterate g (g x) refl (inv (right-inv-right-strict-concat (H x)))

  is-retraction-map-inv-equiv-fiber-transfinite-iterate-htpy :
    is-retraction map-equiv-fiber-transfinite-iterate-htpy map-inv-equiv-fiber-transfinite-iterate-htpy
  is-retraction-map-inv-equiv-fiber-transfinite-iterate-htpy (x , refl) =
    eq-Eq-fiber-transfinite-iterate f (f x) refl (inv (left-inv-right-strict-concat (H x)))

  is-equiv-map-equiv-fiber-transfinite-iterate-htpy : is-equiv map-equiv-fiber-transfinite-iterate-htpy
  is-equiv-map-equiv-fiber-transfinite-iterate-htpy =
    is-equiv-is-invertible
      map-inv-equiv-fiber-transfinite-iterate-htpy
      is-section-map-inv-equiv-fiber-transfinite-iterate-htpy
      is-retraction-map-inv-equiv-fiber-transfinite-iterate-htpy

  equiv-fiber-transfinite-iterate-htpy : fiber-transfinite-iterate f y ≃ fiber-transfinite-iterate g y
  equiv-fiber-transfinite-iterate-htpy = map-equiv-fiber-transfinite-iterate-htpy , is-equiv-map-equiv-fiber-transfinite-iterate-htpy
```

We repeat the construction for `fiber-transfinite-iterate'`.

```text
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f g : A → B} (H : g ~ f) (y : B)
  where

  map-equiv-fiber-transfinite-iterate-htpy' : fiber-transfinite-iterate' f y → fiber-transfinite-iterate' g y
  map-equiv-fiber-transfinite-iterate-htpy' (x , p) = (x , p ∙ inv (H x))

  map-inv-equiv-fiber-transfinite-iterate-htpy' : fiber-transfinite-iterate' g y → fiber-transfinite-iterate' f y
  map-inv-equiv-fiber-transfinite-iterate-htpy' (x , p) = (x , p ∙ H x)

  is-section-map-inv-equiv-fiber-transfinite-iterate-htpy' :
    is-section map-equiv-fiber-transfinite-iterate-htpy' map-inv-equiv-fiber-transfinite-iterate-htpy'
  is-section-map-inv-equiv-fiber-transfinite-iterate-htpy' (x , p) =
    ap (pair x) (is-retraction-inv-concat' (H x) p)

  is-retraction-map-inv-equiv-fiber-transfinite-iterate-htpy' :
    is-retraction map-equiv-fiber-transfinite-iterate-htpy' map-inv-equiv-fiber-transfinite-iterate-htpy'
  is-retraction-map-inv-equiv-fiber-transfinite-iterate-htpy' (x , p) =
    ap (pair x) (is-section-inv-concat' (H x) p)

  is-equiv-map-equiv-fiber-transfinite-iterate-htpy' : is-equiv map-equiv-fiber-transfinite-iterate-htpy'
  is-equiv-map-equiv-fiber-transfinite-iterate-htpy' =
    is-equiv-is-invertible
      map-inv-equiv-fiber-transfinite-iterate-htpy'
      is-section-map-inv-equiv-fiber-transfinite-iterate-htpy'
      is-retraction-map-inv-equiv-fiber-transfinite-iterate-htpy'

  equiv-fiber-transfinite-iterate-htpy' : fiber-transfinite-iterate' f y ≃ fiber-transfinite-iterate' g y
  equiv-fiber-transfinite-iterate-htpy' = map-equiv-fiber-transfinite-iterate-htpy' , is-equiv-map-equiv-fiber-transfinite-iterate-htpy'
```

## Table of files about fibers of maps

The following table lists files that are about fibers of maps as a general
concept.

{{#include tables/fibers-of-maps.md}}
