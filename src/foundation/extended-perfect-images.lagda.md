# Extended perfect images

```agda
-- {-# OPTIONS --allow-unsolved-metas #-}

module foundation.extended-perfect-images where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.connected-maps
open import foundation.coproduct-types
open import foundation.decidable-dependent-function-types
open import foundation.decidable-embeddings
open import foundation.fibers-of-extended-iterated-maps
open import foundation.decidable-maps
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.fibers-of-extended-iterated-maps
open import set-theory.bounded-increasing-binary-sequences
open import set-theory.increasing-binary-sequences
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.double-negation-stable-propositions
open import foundation.functoriality-dependent-function-types
open import foundation.inhabited-types
open import foundation.iterated-dependent-product-types
open import foundation.iterating-functions
open import foundation.law-of-excluded-middle
open import foundation.mere-equality
open import foundation.irrefutable-equality
open import foundation.negated-equality
open import foundation.negation
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
also the following extended chain

```text
      f          g            f               g       g
  a₀ --> f (a₀) --> g(f(a₀)) --> f(g(f(a₀))) --> ... --> (g ◦ f)ⁿ(a₀) ＝ a
```

We say `a₀` is an
{{#concept "extended origin" Disambiguation="extended perfect image"}} for `a`,
and `a` is an
{{#concept "extended perfect image" Agda=is-extended-perfect-image}} for `g`
_relative to `f`_ if any origin of `a` is in the [image](foundation.images.md)
of `g`.

## Definitions

### Extended perfect images

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  is-extended-perfect-image-at : A → ℕ∞↑ → UU (l1 ⊔ l2)
  is-extended-perfect-image-at a n =
    (p : fiber-extended-iterate n (g ∘ f) a) →
    fiber g (inclusion-fiber-extended-iterate n (g ∘ f) p)

  is-extended-perfect-image : (a : A) → UU (l1 ⊔ l2)
  is-extended-perfect-image a = (n : ℕ∞↑) → is-extended-perfect-image-at a n
```

### Extended Nonperfect images

We can talk about origins of `a` which are not perfect images of `g` relative to
`f`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  is-extended-nonperfect-image : (a : A) → UU (l1 ⊔ l2)
  is-extended-nonperfect-image a =
   Σ ℕ∞↑ -- TODO: does it suffice to consider finite `n` here?
    ( λ n →
      Σ ( fiber-extended-iterate n (g ∘ f) a)
        ( λ p → ¬ (fiber g (inclusion-fiber-extended-iterate n (g ∘ f) p))))
```

### Extended nonperfect fibers over an element

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) (g : B → A)
  where

  has-extended-nonperfect-fiber : (b : B) → UU (l1 ⊔ l2)
  has-extended-nonperfect-fiber b =
    Σ (fiber f b) (λ s → ¬ (is-extended-perfect-image f g (pr1 s)))

  is-prop-has-extended-nonperfect-fiber' :
    is-prop-map f → (b : B) → is-prop (has-extended-nonperfect-fiber b)
  is-prop-has-extended-nonperfect-fiber' F b =
    is-prop-Σ (F b) (λ _ → is-prop-neg)

  is-prop-has-extended-nonperfect-fiber :
    is-emb f → (b : B) → is-prop (has-extended-nonperfect-fiber b)
  is-prop-has-extended-nonperfect-fiber F =
    is-prop-has-extended-nonperfect-fiber' (is-prop-map-is-emb F)

  has-extended-nonperfect-fiber-Prop' :
    is-prop-map f → (b : B) → Prop (l1 ⊔ l2)
  has-extended-nonperfect-fiber-Prop' F b =
    ( has-extended-nonperfect-fiber b ,
      is-prop-has-extended-nonperfect-fiber' F b)

  has-extended-nonperfect-fiber-Prop :
    is-emb f → (b : B) → Prop (l1 ⊔ l2)
  has-extended-nonperfect-fiber-Prop F b =
    ( has-extended-nonperfect-fiber b ,
      is-prop-has-extended-nonperfect-fiber F b)
```

## Properties

### If `g` is an embedding then being a perfect image for `g` is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  is-prop-is-extended-perfect-image-is-emb :
    is-emb g → (a : A) → is-prop (is-extended-perfect-image f g a)
  is-prop-is-extended-perfect-image-is-emb G a =
    is-prop-Π
      ( λ n →
        is-prop-Π
          ( λ p →
            is-prop-map-is-emb G
              ( inclusion-fiber-extended-iterate n (g ∘ f) p)))

  is-extended-perfect-image-Prop : is-emb g → A → Prop (l1 ⊔ l2)
  is-extended-perfect-image-Prop G a =
    ( is-extended-perfect-image f g a ,
      is-prop-is-extended-perfect-image-is-emb G a)
```

### Fibers over perfect images

If `a` is a perfect image for `g`, then `a` has a preimage under `g`. Just take
`n = zero` in the definition.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  fiber-is-extended-perfect-image :
    (a : A) → is-extended-perfect-image f g a → fiber g a
  fiber-is-extended-perfect-image a ρ =
    ρ zero-ℕ∞↑ (fiber-extended-iterate-zero (g ∘ f) a)
```

One can define a map from `A` to `B` restricting the domain to the perfect
images of `g`. This gives a kind of [section](foundation-core.sections.md) of
`g`. When `g` is also an embedding, the map gives a kind of
[retraction](foundation-core.retractions.md) of `g`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  inverse-of-extended-perfect-image :
    (a : A) → is-extended-perfect-image f g a → B
  inverse-of-extended-perfect-image a ρ =
    inclusion-fiber g (fiber-is-extended-perfect-image f g a ρ)

  is-section-inverse-of-extended-perfect-image :
    (a : A) (ρ : is-extended-perfect-image f g a) →
    g (inverse-of-extended-perfect-image a ρ) ＝ a
  is-section-inverse-of-extended-perfect-image a ρ =
    compute-value-inclusion-fiber g (fiber-is-extended-perfect-image f g a ρ)
```

When `g` is also injective, the map gives a kind of
[retraction](foundation-core.retractions.md) of `g`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  is-retraction-inverse-of-extended-perfect-image :
    is-injective g →
    (b : B) (ρ : is-extended-perfect-image f g (g b)) →
    inverse-of-extended-perfect-image f g (g b) ρ ＝ b
  is-retraction-inverse-of-extended-perfect-image G b ρ =
    G (is-section-inverse-of-extended-perfect-image f g (g b) ρ)
```

If `g(f(a))` is a perfect image for `g`, so is `a`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  previous-extended-perfect-image-at :
    (a : A) (n : ℕ∞↑) →
    is-extended-perfect-image-at f g (g (f a)) (succ-ℕ∞↑ n) →
    is-extended-perfect-image-at f g a n
  previous-extended-perfect-image-at a n γ p =
    tr
      ( fiber g)
      ( compute-ap-fiber-extended-iterate' n (g ∘ f) a p) -- TODO: when the dependency has been fixed and this is `refl`, remove `tr`
      ( γ (ap-fiber-extended-iterate' n (g ∘ f) a p))

  previous-extended-perfect-image :
    (a : A) → is-extended-perfect-image f g (g (f a)) → is-extended-perfect-image f g a
  previous-extended-perfect-image a γ n = previous-extended-perfect-image-at a n (γ (succ-ℕ∞↑ n))
    -- previous-extended-perfect-image-at a n (γ (succ-ℕ∞↑ n))
```

Extended perfect images of `g` relative to `f` not mapped to the image of `f`
under `inverse-of-extended-perfect-image`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  extended-perfect-image-has-distinct-image :
    (a a₀ : A) →
    ¬ (is-extended-perfect-image f g a) →
    (ρ : is-extended-perfect-image f g a₀) →
    f a ≠ inverse-of-extended-perfect-image f g a₀ ρ
  extended-perfect-image-has-distinct-image a a₀ nρ ρ p =
    v ρ
    where
    q : g (f a) ＝ a₀
    q = ap g p ∙ is-section-inverse-of-extended-perfect-image f g a₀ ρ

    s : ¬ (is-extended-perfect-image f g (g (f a)))
    s = λ η → nρ (previous-extended-perfect-image f g a η)

    v : ¬ (is-extended-perfect-image f g a₀)
    v = tr (λ a' → ¬ (is-extended-perfect-image f g a')) q s
```

### Double negation elimination on extended nonperfect fibers

If we assume that `g` is a double negation eliminating map, we can prove that if
`is-extended-nonperfect-image a` does not hold, then we have
`is-extended-perfect-image a`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  double-negation-elim-is-extended-perfect-image :
    is-double-negation-eliminating-map g →
    (a : A) →
     ¬ (is-extended-nonperfect-image f g a) → is-extended-perfect-image f g a
  double-negation-elim-is-extended-perfect-image G a nρ n q =
    G (inclusion-fiber-extended-iterate n (g ∘ f) q) (λ ng → nρ (n , q , ng))
```

If `g(b)` is not a perfect image, then `b` has an `f`-fiber `a` that is not a
perfect image for `g`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  is-irrefutable-is-extended-nonperfect-image-is-not-extended-perfect-image :
    (G : is-double-negation-eliminating-map g)
    (b : B) (nρ : ¬ (is-extended-perfect-image f g (g b))) →
    ¬¬ (is-extended-nonperfect-image f g (g b))
  is-irrefutable-is-extended-nonperfect-image-is-not-extended-perfect-image
    G b nρ nμ =
    nρ (double-negation-elim-is-extended-perfect-image f g G (g b) nμ)

  has-extended-nonperfect-fiber-is-extended-nonperfect-image :
    is-injective g → (b : B) →
    is-extended-nonperfect-image f g (g b) → has-extended-nonperfect-fiber f g b
  has-extended-nonperfect-fiber-is-extended-nonperfect-image G b (n , p , ng) =
    ( (g ∘ f) (sequence-fiber-extended-iterate n (g ∘ f) p (self-bounded-ℕ∞↑ n)) ,
      G {!   !}) , {! ng  !}
  -- TODO: gotta find a way to show this by coinduction... 👀
  -- TODO: this lemma is only used to prove a negative result, so it might be possible to case analyze at infinity mayhaps?

  -- (x₀ , zero-ℕ∞↑ , u) =
  --   ex-falso (pr2 u (b , inv (pr1 u)))
  -- has-extended-nonperfect-fiber-is-extended-nonperfect-image G b (x₀ , succ-ℕ∞↑ n , u) =
  --   ( iterate n (g ∘ f) x₀ , G (pr1 u)) ,
  --   ( λ s → pr2 u (s x₀ n refl))




  is-irrefutable-has-extended-nonperfect-fiber-is-not-extended-perfect-image :
    is-double-negation-eliminating-map g → is-injective g →
    (b : B) → ¬ (is-extended-perfect-image f g (g b)) →
    ¬¬ (has-extended-nonperfect-fiber f g b)
  is-irrefutable-has-extended-nonperfect-fiber-is-not-extended-perfect-image G G' b nρ t =
    is-irrefutable-is-extended-nonperfect-image-is-not-extended-perfect-image G b nρ
      ( λ s → t (has-extended-nonperfect-fiber-is-extended-nonperfect-image G' b s))
```

If `f` has double negation elimination and dense equality on fibers, then

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  double-negation-elim-has-extended-nonperfect-fiber :
    is-double-negation-eliminating-map f →
    ((y : B) → all-elements-irrefutably-equal (fiber f y)) →
    (b : B) → has-double-negation-elim (has-extended-nonperfect-fiber f g b)
  double-negation-elim-has-extended-nonperfect-fiber F F' b =
    double-negation-elim-Σ-all-elements-irrefutably-equal-base (F' b) (F b)
      ( λ p → double-negation-elim-neg (is-extended-perfect-image f g (pr1 p)))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  (is-double-negation-eliminating-g : is-double-negation-eliminating-map g)
  (is-injective-g : is-injective g)
  (is-double-negation-eliminating-f : is-double-negation-eliminating-map f)
  (is-π₀-trivial-f : (y : B) → all-elements-irrefutably-equal (fiber f y))
  (b : B) (nρ : ¬ (is-extended-perfect-image f g (g b)))
  where

  has-extended-nonperfect-fiber-is-not-extended-perfect-image :
    has-extended-nonperfect-fiber f g b
  has-extended-nonperfect-fiber-is-not-extended-perfect-image =
    double-negation-elim-has-extended-nonperfect-fiber
      ( is-double-negation-eliminating-f)
      ( is-π₀-trivial-f)
      ( b)
      ( is-irrefutable-has-extended-nonperfect-fiber-is-not-extended-perfect-image
        ( is-double-negation-eliminating-g)
        ( is-injective-g)
        ( b)
        ( nρ))

  fiber-has-extended-nonperfect-fiber-is-not-extended-perfect-image : fiber f b
  fiber-has-extended-nonperfect-fiber-is-not-extended-perfect-image =
    pr1 has-extended-nonperfect-fiber-is-not-extended-perfect-image

  element-has-extended-nonperfect-fiber-is-not-extended-perfect-image : A
  element-has-extended-nonperfect-fiber-is-not-extended-perfect-image =
    pr1 fiber-has-extended-nonperfect-fiber-is-not-extended-perfect-image

  is-in-fiber-element-has-extended-nonperfect-fiber-is-not-extended-perfect-image :
    f element-has-extended-nonperfect-fiber-is-not-extended-perfect-image ＝ b
  is-in-fiber-element-has-extended-nonperfect-fiber-is-not-extended-perfect-image =
    pr2 fiber-has-extended-nonperfect-fiber-is-not-extended-perfect-image

  is-not-extended-perfect-image-has-extended-nonperfect-fiber-is-not-extended-perfect-image :
    ¬ (is-extended-perfect-image f g element-has-extended-nonperfect-fiber-is-not-extended-perfect-image)
  is-not-extended-perfect-image-has-extended-nonperfect-fiber-is-not-extended-perfect-image =
    pr2 has-extended-nonperfect-fiber-is-not-extended-perfect-image
```

### Decidability of perfect images

Assuming `g` and `f` are decidable embedding, then for every natural number
`n : ℕ∞↑` and every element `a : A` it is decidable whether `a` is a perfect
image of `g` relative to `f` after `n` iterations. In fact, the map `f` need
only be propositionally decidable and π₀-trivial.

```text
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  is-decidable-prop-is-extended-perfect-image-at' :
    is-decidable-emb g → is-inhabited-or-empty-map f → is-π₀-trivial-map' f →
    (a : A) (n : ℕ∞↑) → is-decidable-prop (is-extended-perfect-image-at f g a n)
  is-decidable-prop-is-extended-perfect-image-at' G F F' a n =
    is-decidable-prop-Π-all-elements-irrefutably-equal-base'
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

  is-decidable-prop-is-extended-perfect-image-at :
    is-decidable-emb g → is-decidable-map f → is-π₀-trivial-map' f →
    (a : A) (n : ℕ∞↑) → is-decidable-prop (is-extended-perfect-image-at f g a n)
  is-decidable-prop-is-extended-perfect-image-at G F =
    is-decidable-prop-is-extended-perfect-image-at G
      ( is-inhabited-or-empty-map-is-decidable-map F)
```
