# Perfect images

```agda
module foundation.perfect-images where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.connected-maps
open import foundation.coproduct-types
open import foundation.decidable-dependent-function-types
open import foundation.decidable-embeddings
open import foundation.decidable-maps
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.double-negation-stable-propositions
open import foundation.functoriality-dependent-function-types
open import foundation.inhabited-types
open import foundation.iterated-dependent-product-types
open import foundation.iterating-functions
open import foundation.law-of-excluded-middle
open import foundation.mere-equality
open import foundation.negated-equality
open import foundation.negation
open import foundation.pi-0-trivial-maps
open import foundation.propositional-truncations
open import foundation.type-arithmetic-dependent-function-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels
open import foundation.weak-limited-principle-of-omniscience

open import foundation-core.cartesian-product-types
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.transport-along-identifications

open import logic.double-negation-eliminating-maps
open import logic.double-negation-elimination
open import logic.double-negation-stable-embeddings
open import logic.propositionally-decidable-maps
open import logic.propositionally-double-negation-eliminating-maps
```

</details>

## Idea

Consider two maps `f : A → B` and `g : B → A`. For `(g ◦ f)ⁿ(a₀) ＝ a`, consider
also the following chain

```text
      f          g            f               g       g
  a₀ --> f (a₀) --> g(f(a₀)) --> f(g(f(a₀))) --> ... --> (g ◦ f)ⁿ(a₀) ＝ a
```

We say `a₀` is an {{#concept "origin" Disambiguation="perfect image"}} for `a`,
and `a` is a {{#concept "perfect image" Agda=is-perfect-image}} for `g`
_relative to `f`_ if any origin of `a` is in the [image](foundation.images.md)
of `g`.

## Definitions

### Perfect images

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  is-perfect-image : (a : A) → UU (l1 ⊔ l2)
  is-perfect-image a =
    (a₀ : A) (n : ℕ) → iterate n (g ∘ f) a₀ ＝ a → fiber g a₀
```

An alternative but equivalent definition.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  is-perfect-image-at' : A → ℕ → UU (l1 ⊔ l2)
  is-perfect-image-at' a n = (p : fiber (iterate n (g ∘ f)) a) → fiber g (pr1 p)

  is-perfect-image' : (a : A) → UU (l1 ⊔ l2)
  is-perfect-image' a = (n : ℕ) → is-perfect-image-at' a n

  compute-is-perfect-image :
    (a : A) → is-perfect-image' a ≃ is-perfect-image f g a
  compute-is-perfect-image a =
    equivalence-reasoning
    ((n : ℕ) (p : fiber (iterate n (g ∘ f)) a) → fiber g (pr1 p))
    ≃ ((n : ℕ) (a₀ : A) → iterate n (g ∘ f) a₀ ＝ a → fiber g a₀)
    by equiv-Π-equiv-family (λ n → equiv-ev-pair)
    ≃ ((a₀ : A) (n : ℕ) → iterate n (g ∘ f) a₀ ＝ a → fiber g a₀)
    by equiv-swap-Π
```

### Nonperfect images

We can talk about origins of `a` which are not perfect images of `g` relative to
`f`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  is-nonperfect-image : (a : A) → UU (l1 ⊔ l2)
  is-nonperfect-image a =
    Σ A (λ a₀ → Σ ℕ (λ n → (iterate n (g ∘ f) a₀ ＝ a) × ¬ (fiber g a₀)))
```

### Nonperfect fibers over an element

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) (g : B → A)
  where

  has-nonperfect-fiber : (b : B) → UU (l1 ⊔ l2)
  has-nonperfect-fiber b =
    Σ (fiber f b) (λ s → ¬ (is-perfect-image f g (pr1 s)))

  is-prop-has-nonperfect-fiber' :
    is-prop-map f → (b : B) → is-prop (has-nonperfect-fiber b)
  is-prop-has-nonperfect-fiber' F b = is-prop-Σ (F b) (λ _ → is-prop-neg)

  is-prop-has-nonperfect-fiber :
    is-emb f → (b : B) → is-prop (has-nonperfect-fiber b)
  is-prop-has-nonperfect-fiber F =
    is-prop-has-nonperfect-fiber' (is-prop-map-is-emb F)

  has-nonperfect-fiber-Prop' :
    is-prop-map f → (b : B) → Prop (l1 ⊔ l2)
  has-nonperfect-fiber-Prop' F b =
    ( has-nonperfect-fiber b , is-prop-has-nonperfect-fiber' F b)

  has-nonperfect-fiber-Prop :
    is-emb f → (b : B) → Prop (l1 ⊔ l2)
  has-nonperfect-fiber-Prop F b =
    ( has-nonperfect-fiber b , is-prop-has-nonperfect-fiber F b)
```

## Properties

### If `g` is an embedding then being a perfect image for `g` is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  is-prop-is-perfect-image-is-emb :
    is-emb g → (a : A) → is-prop (is-perfect-image f g a)
  is-prop-is-perfect-image-is-emb G a =
    is-prop-iterated-Π 3 (λ a₀ n p → is-prop-map-is-emb G a₀)

  is-perfect-image-Prop : is-emb g → A → Prop (l1 ⊔ l2)
  pr1 (is-perfect-image-Prop G a) = is-perfect-image f g a
  pr2 (is-perfect-image-Prop G a) = is-prop-is-perfect-image-is-emb G a
```

### Fibers over perfect images

If `a` is a perfect image for `g`, then `a` has a preimage under `g`. Just take
`n = zero` in the definition.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  fiber-is-perfect-image : (a : A) → is-perfect-image f g a → fiber g a
  fiber-is-perfect-image a ρ = ρ a 0 refl
```

One can define a map from `A` to `B` restricting the domain to the perfect
images of `g`. This gives a kind of [section](foundation-core.sections.md) of
`g`. When `g` is also an embedding, the map gives a kind of
[retraction](foundation-core.retractions.md) of `g`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  inverse-of-perfect-image : (a : A) → is-perfect-image f g a → B
  inverse-of-perfect-image a ρ = pr1 (fiber-is-perfect-image a ρ)

  is-section-inverse-of-perfect-image :
    (a : A) (ρ : is-perfect-image f g a) → g (inverse-of-perfect-image a ρ) ＝ a
  is-section-inverse-of-perfect-image a ρ = pr2 (fiber-is-perfect-image a ρ)
```

When `g` is also injective, the map gives a kind of
[retraction](foundation-core.retractions.md) of `g`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  is-retraction-inverse-of-perfect-image :
    is-injective g →
    (b : B) (ρ : is-perfect-image f g (g b)) →
    inverse-of-perfect-image (g b) ρ ＝ b
  is-retraction-inverse-of-perfect-image G b ρ =
    G (is-section-inverse-of-perfect-image (g b) ρ)
```

If `g(f(a))` is a perfect image for `g`, so is `a`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  previous-perfect-image-at' :
    (a : A) (n : ℕ) →
    is-perfect-image-at' f g (g (f a)) (succ-ℕ n) → is-perfect-image-at' f g a n
  previous-perfect-image-at' a n γ (a₀ , p) = γ (a₀ , ap (g ∘ f) p)

  previous-perfect-image' :
    (a : A) → is-perfect-image' f g (g (f a)) → is-perfect-image' f g a
  previous-perfect-image' a γ n = previous-perfect-image-at' a n (γ (succ-ℕ n))

  previous-perfect-image :
    (a : A) → is-perfect-image f g (g (f a)) → is-perfect-image f g a
  previous-perfect-image a γ a₀ n p = γ a₀ (succ-ℕ n) (ap (g ∘ f) p)
```

Perfect images of `g` relative to `f` not mapped to the image of `f` under
`inverse-of-perfect-image`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  perfect-image-has-distinct-image :
    (a a₀ : A) →
    ¬ (is-perfect-image f g a) →
    (ρ : is-perfect-image f g a₀) →
    f a ≠ inverse-of-perfect-image a₀ ρ
  perfect-image-has-distinct-image a a₀ nρ ρ p =
    v ρ
    where
    q : g (f a) ＝ a₀
    q = ap g p ∙ is-section-inverse-of-perfect-image a₀ ρ

    s : ¬ (is-perfect-image f g (g (f a)))
    s = λ η → nρ (previous-perfect-image a η)

    v : ¬ (is-perfect-image f g a₀)
    v = tr (λ a' → ¬ (is-perfect-image f g a')) q s
```

### Decidability of perfect images

Assuming `g` and `f` are decidable embedding, then for every natural number
`n : ℕ` and every element `a : A` it is decidable whether `a` is a perfect image
of `g` relative to `f` after `n` iterations. In fact, the map `f` need only be
propositionally decidable and π₀-trivial.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  is-decidable-prop-is-perfect-image-at'' :
    is-decidable-emb g → is-inhabited-or-empty-map f → is-π₀-trivial-map' f →
    (a : A) (n : ℕ) → is-decidable-prop (is-perfect-image-at' f g a n)
  is-decidable-prop-is-perfect-image-at'' G F F' a n =
    is-decidable-prop-Π-all-elements-merely-equal-base'
    ( λ x → fiber g (pr1 x) , is-decidable-prop-map-is-decidable-emb G (pr1 x))
    ( is-π₀-trivial-map'-iterate
      ( is-π₀-trivial-map'-comp
        ( is-π₀-trivial-map'-is-emb (is-emb-is-decidable-emb G))
        ( F'))
      ( n)
      ( a))
    ( is-inhabited-or-empty-map-iterate-is-π₀-trivial-map'
      ( is-inhabited-or-empty-map-comp-is-π₀-trivial-map'
        ( is-π₀-trivial-map'-is-emb (is-emb-is-decidable-emb G))
        ( is-inhabited-or-empty-map-is-decidable-map
          ( is-decidable-map-is-decidable-emb G))
        ( F))
      ( is-π₀-trivial-map'-comp
        ( is-π₀-trivial-map'-is-emb (is-emb-is-decidable-emb G))
        ( F'))
      ( n)
      ( a))

  is-decidable-prop-is-perfect-image-at' :
    is-decidable-emb g → is-decidable-map f → is-π₀-trivial-map' f →
    (a : A) (n : ℕ) → is-decidable-prop (is-perfect-image-at' f g a n)
  is-decidable-prop-is-perfect-image-at' G F =
    is-decidable-prop-is-perfect-image-at'' G
      ( is-inhabited-or-empty-map-is-decidable-map F)
```

### Double negation elimination on nonperfect fibers

If we assume that `g` is a double negation eliminating map, we can prove that if
`is-nonperfect-image a` does not hold, then we have `is-perfect-image a`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  double-negation-elim-is-perfect-image :
    is-double-negation-eliminating-map g →
    (a : A) → ¬ (is-nonperfect-image a) → is-perfect-image f g a
  double-negation-elim-is-perfect-image G a nρ a₀ n p =
    G a₀ (λ a₁ → nρ (a₀ , n , p , a₁))
```

If `g(b)` is not a perfect image, then `b` has an `f`-fiber `a` that is not a
perfect image for `g`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  is-irrefutable-is-nonperfect-image-is-not-perfect-image :
    (G : is-double-negation-eliminating-map g)
    (b : B) (nρ : ¬ (is-perfect-image f g (g b))) →
    ¬¬ (is-nonperfect-image {f = f} (g b))
  is-irrefutable-is-nonperfect-image-is-not-perfect-image G b nρ nμ =
    nρ (double-negation-elim-is-perfect-image G (g b) nμ)

  has-nonperfect-fiber-is-nonperfect-image :
    is-injective g → (b : B) →
    is-nonperfect-image {f = f} (g b) → has-nonperfect-fiber f g b
  has-nonperfect-fiber-is-nonperfect-image G b (x₀ , zero-ℕ , u) =
    ex-falso (pr2 u (b , inv (pr1 u)))
  has-nonperfect-fiber-is-nonperfect-image G b (x₀ , succ-ℕ n , u) =
    ( iterate n (g ∘ f) x₀ , G (pr1 u)) ,
    ( λ s → pr2 u (s x₀ n refl))

  is-irrefutable-has-nonperfect-fiber-is-not-perfect-image :
    is-double-negation-eliminating-map g → is-injective g →
    (b : B) (nρ : ¬ (is-perfect-image f g (g b))) →
    ¬¬ (has-nonperfect-fiber f g b)
  is-irrefutable-has-nonperfect-fiber-is-not-perfect-image G G' b nρ t =
    is-irrefutable-is-nonperfect-image-is-not-perfect-image G b nρ
      ( λ s → t (has-nonperfect-fiber-is-nonperfect-image G' b s))
```

If `f` is π₀-trivial and has double negation elimination, then

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  double-negation-elim-has-nonperfect-fiber :
    is-double-negation-eliminating-map f →
    is-π₀-trivial-map' f →
    (b : B) → has-double-negation-elim (has-nonperfect-fiber f g b)
  double-negation-elim-has-nonperfect-fiber F F' b =
    double-negation-elim-Σ-all-elements-merely-equal-base (F' b) (F b)
      ( λ p → double-negation-elim-neg (is-perfect-image f g (pr1 p)))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  (is-double-negation-eliminating-g : is-double-negation-eliminating-map g)
  (is-injective-g : is-injective g)
  (is-double-negation-eliminating-f : is-double-negation-eliminating-map f)
  (is-π₀-trivial-f : is-π₀-trivial-map' f)
  (b : B) (nρ : ¬ (is-perfect-image f g (g b)))
  where

  has-nonperfect-fiber-is-not-perfect-image :
    has-nonperfect-fiber f g b
  has-nonperfect-fiber-is-not-perfect-image =
    double-negation-elim-has-nonperfect-fiber
      ( is-double-negation-eliminating-f)
      ( is-π₀-trivial-f)
      ( b)
      ( is-irrefutable-has-nonperfect-fiber-is-not-perfect-image
        ( is-double-negation-eliminating-g)
        ( is-injective-g)
        ( b)
        ( nρ))

  fiber-has-nonperfect-fiber-is-not-perfect-image : fiber f b
  fiber-has-nonperfect-fiber-is-not-perfect-image =
    pr1 has-nonperfect-fiber-is-not-perfect-image

  element-has-nonperfect-fiber-is-not-perfect-image : A
  element-has-nonperfect-fiber-is-not-perfect-image =
    pr1 fiber-has-nonperfect-fiber-is-not-perfect-image

  is-in-fiber-element-has-nonperfect-fiber-is-not-perfect-image :
    f element-has-nonperfect-fiber-is-not-perfect-image ＝ b
  is-in-fiber-element-has-nonperfect-fiber-is-not-perfect-image =
    pr2 fiber-has-nonperfect-fiber-is-not-perfect-image

  is-not-perfect-image-has-nonperfect-fiber-is-not-perfect-image :
    ¬ (is-perfect-image f g element-has-nonperfect-fiber-is-not-perfect-image)
  is-not-perfect-image-has-nonperfect-fiber-is-not-perfect-image =
    pr2 has-nonperfect-fiber-is-not-perfect-image
```
