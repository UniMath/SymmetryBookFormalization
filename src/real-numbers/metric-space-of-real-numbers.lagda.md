# The metric space of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.metric-space-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-cartesian-products-of-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.extensional-premetric-structures
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-in-premetric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.metric-structures
open import metric-spaces.monotonic-premetric-structures
open import metric-spaces.premetric-spaces
open import metric-spaces.premetric-structures
open import metric-spaces.pseudometric-structures
open import metric-spaces.reflexive-premetric-structures
open import metric-spaces.saturated-metric-spaces
open import metric-spaces.symmetric-premetric-structures
open import metric-spaces.triangular-premetric-structures

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

The type of [real numbers](real-numbers.dedekind-real-numbers.md) equipped with
the [premetric](metric-spaces.premetric-structures.md) where `x y : ℝ` are
`d`-neighbors when for any `r : ℚ` the following two conditions hold:

- if `r + d` is in the lower cut of `y`, `r` is in the lower cut of `x`
- if `r + d` is in the lower cut of `x`, `r` is in the lower cut of `y`

is a [saturated metric space](metric-spaces.saturated-metric-spaces.md). It is
the
{{#concept "standard metric space of real numbers" Agda=metric-space-leq-ℝ}}.

## Definitions

### The standard premetric on the real numbers

```agda
module _
  {l : Level} (d : ℚ⁺) (x y : ℝ l)
  where

  is-in-lower-neighborhood-leq-prop-ℝ : Prop l
  is-in-lower-neighborhood-leq-prop-ℝ =
    Π-Prop
      ( ℚ)
      ( λ r →
        hom-Prop
          ( lower-cut-ℝ y (r +ℚ (rational-ℚ⁺ d)))
            ( lower-cut-ℝ x r))

  is-in-lower-neighborhood-leq-ℝ : UU l
  is-in-lower-neighborhood-leq-ℝ =
    type-Prop is-in-lower-neighborhood-leq-prop-ℝ

premetric-leq-ℝ : (l : Level) → Premetric l (ℝ l)
premetric-leq-ℝ l d x y =
  product-Prop
    ( is-in-lower-neighborhood-leq-prop-ℝ d x y)
    ( is-in-lower-neighborhood-leq-prop-ℝ d y x)
```

## Properties

### `x` is in a neighborhood `d` of `y` if `x - d ≤ y ≤ x + d`

```agda
is-in-lower-neighborhood-real-bound-leq-ℝ :
  {l : Level} → (d : ℚ⁺) (x y : ℝ l) →
  leq-ℝ y (x +ℝ real-ℚ (rational-ℚ⁺ d)) →
  is-in-lower-neighborhood-leq-ℝ d x y
is-in-lower-neighborhood-real-bound-leq-ℝ d⁺@(d , _) x y y≤x+d q q+d<y =
  lower-cut-real-le-ℚ
    ( q)
    ( x)
    ( concatenate-le-leq-ℝ
      ( real-ℚ q)
      ( y -ℝ real-ℚ d)
      ( x)
      ( forward-implication
        ( iff-diff-right-le-ℝ
          ( real-ℚ q)
          ( real-ℚ d)
          ( y))
        ( inv-tr
          ( λ z → le-ℝ z y)
          ( add-real-ℚ q d)
          ( le-lower-cut-real-ℚ (q +ℚ d) y q+d<y)))
      ( backward-implication (iff-add-right-leq-ℝ y (real-ℚ d) x) y≤x+d))

neighborhood-±-bound-leq-ℝ :
  {l : Level} → (d : ℚ⁺) (x y : ℝ l) →
  leq-ℝ x (y +ℝ real-ℚ (rational-ℚ⁺ d)) →
  leq-ℝ y (x +ℝ real-ℚ (rational-ℚ⁺ d)) →
  type-Prop (premetric-leq-ℝ l d x y)
neighborhood-±-bound-leq-ℝ d x y x≤y+d y≤x+d =
  is-in-lower-neighborhood-real-bound-leq-ℝ d x y y≤x+d ,
  is-in-lower-neighborhood-real-bound-leq-ℝ d y x x≤y+d
```

### The standard premetric on the real numbers is a metric structure

The triangle inequality is the [91st](literature.100-theorems.md#91) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

```agda
is-reflexive-premetric-leq-ℝ :
  {l : Level} → is-reflexive-Premetric (premetric-leq-ℝ l)
is-reflexive-premetric-leq-ℝ d x =
  diagonal-product
    ( (r : ℚ) →
      is-in-lower-cut-ℝ x (r +ℚ (rational-ℚ⁺ d)) → is-in-lower-cut-ℝ x r)
    ( λ r →
      le-lower-cut-ℝ x r (r +ℚ rational-ℚ⁺ d) (le-right-add-rational-ℚ⁺ r d))

is-symmetric-premetric-leq-ℝ :
  {l : Level} → is-symmetric-Premetric (premetric-leq-ℝ l)
is-symmetric-premetric-leq-ℝ d x y (H , K) = (K , H)

is-tight-premetric-leq-ℝ : {l : Level} → is-tight-Premetric (premetric-leq-ℝ l)
is-tight-premetric-leq-ℝ x y H =
  eq-eq-lower-cut-ℝ
    ( x)
    ( y)
    ( antisymmetric-leq-subtype
      ( lower-cut-ℝ x)
      ( lower-cut-ℝ y)
      ( λ r Lxr →
        elim-exists
          ( lower-cut-ℝ y r)
          ( λ s (r<s , Lxs) →
            pr2
              ( H (positive-diff-le-ℚ r s r<s))
              ( r)
              ( inv-tr
                ( λ u → is-in-lower-cut-ℝ x u)
                ( right-law-positive-diff-le-ℚ r s r<s)
                ( Lxs)))
          ( forward-implication (is-rounded-lower-cut-ℝ x r) Lxr))
      ( λ r Lyr →
        elim-exists
          ( lower-cut-ℝ x r)
          ( λ s (r<s , Lys) →
            pr1
              ( H (positive-diff-le-ℚ r s r<s))
              ( r)
              ( inv-tr
                ( λ u → is-in-lower-cut-ℝ y u)
                ( right-law-positive-diff-le-ℚ r s r<s)
                ( Lys)))
          ( forward-implication (is-rounded-lower-cut-ℝ y r) Lyr)))

is-local-premetric-leq-ℝ : {l : Level} → is-local-Premetric (premetric-leq-ℝ l)
is-local-premetric-leq-ℝ {l} =
  is-local-is-tight-Premetric
    ( premetric-leq-ℝ l)
    ( is-tight-premetric-leq-ℝ)

is-triangular-premetric-leq-ℝ :
  {l : Level} → is-triangular-Premetric (premetric-leq-ℝ l)
pr1 (is-triangular-premetric-leq-ℝ x y z dxy dyz Hyz Hxy) r =
  pr1 Hxy r ∘
  pr1 Hyz (r +ℚ rational-ℚ⁺ dxy) ∘
  inv-tr
    ( is-in-lower-cut-ℝ z)
    ( associative-add-ℚ r (rational-ℚ⁺ dxy) (rational-ℚ⁺ dyz))
pr2 (is-triangular-premetric-leq-ℝ x y z dxy dyz Hyz Hxy) r =
  pr2 Hyz r ∘
  pr2 Hxy (r +ℚ rational-ℚ⁺ dyz) ∘
  inv-tr
    ( is-in-lower-cut-ℝ x)
    ( associative-add-ℚ r (rational-ℚ⁺ dyz) (rational-ℚ⁺ dxy) ∙
      ap (add-ℚ r) (commutative-add-ℚ (rational-ℚ⁺ dyz) (rational-ℚ⁺ dxy)))

is-pseudometric-premetric-leq-ℝ :
  {l : Level} → is-pseudometric-Premetric (premetric-leq-ℝ l)
is-pseudometric-premetric-leq-ℝ =
  is-reflexive-premetric-leq-ℝ ,
  is-symmetric-premetric-leq-ℝ ,
  is-triangular-premetric-leq-ℝ

is-metric-premetric-leq-ℝ :
  {l : Level} → is-metric-Premetric (premetric-leq-ℝ l)
pr1 is-metric-premetric-leq-ℝ = is-pseudometric-premetric-leq-ℝ
pr2 is-metric-premetric-leq-ℝ = is-local-premetric-leq-ℝ
```

### The standard saturated metric space of real numbers

```agda
module _
  (l : Level)
  where

  premetric-space-leq-ℝ : Premetric-Space (lsuc l) l
  premetric-space-leq-ℝ = ℝ l , premetric-leq-ℝ l

  metric-space-leq-ℝ : Metric-Space (lsuc l) l
  pr1 metric-space-leq-ℝ = premetric-space-leq-ℝ
  pr2 metric-space-leq-ℝ = is-metric-premetric-leq-ℝ
```

## Properties

### The standard metric space of real numbers is saturated

```agda
module _
  {l : Level} (x y : ℝ l) (ε : ℚ⁺)
  (H : (δ : ℚ⁺) → is-in-lower-neighborhood-leq-ℝ (ε +ℚ⁺ δ) x y)
  where

  is-closed-lower-neighborhood-leq-ℝ :
    is-in-lower-neighborhood-leq-ℝ ε x y
  is-closed-lower-neighborhood-leq-ℝ r I =
    elim-exists
      ( lower-cut-ℝ x r)
      ( λ r' (K , I') →
        H ( positive-diff-le-ℚ (r +ℚ rational-ℚ⁺ ε) r' K)
          ( r)
          ( tr
            ( is-in-lower-cut-ℝ y)
            ( ( inv
                ( right-law-positive-diff-le-ℚ
                  ( r +ℚ rational-ℚ⁺ ε)
                  ( r')
                  ( K))) ∙
              ( associative-add-ℚ
                ( r)
                ( rational-ℚ⁺ ε)
                    ( r' -ℚ (r +ℚ rational-ℚ⁺ ε))))
            ( I')))
      ( forward-implication
        ( is-rounded-lower-cut-ℝ y (r +ℚ rational-ℚ⁺ ε)) I)
```

```agda
module _
  {l : Level}
  where

  is-saturated-metric-space-leq-ℝ :
    is-saturated-Metric-Space (metric-space-leq-ℝ l)
  is-saturated-metric-space-leq-ℝ ε x y H =
    ( is-closed-lower-neighborhood-leq-ℝ x y ε (pr1 ∘ H)) ,
    ( is-closed-lower-neighborhood-leq-ℝ y x ε (pr2 ∘ H))
```

### The canonical embedding from rational to real numbers is an isometry between metric spaces

```agda
is-isometry-metric-space-leq-real-ℚ :
  is-isometry-Metric-Space
    ( metric-space-leq-ℚ)
    ( metric-space-leq-ℝ lzero)
    ( real-ℚ)
is-isometry-metric-space-leq-real-ℚ d x y =
  pair
    ( map-product
      ( le-le-add-positive-leq-add-positive-ℚ x y d)
      ( le-le-add-positive-leq-add-positive-ℚ y x d))
    ( map-product
      ( leq-add-positive-le-le-add-positive-ℚ x y d)
      ( leq-add-positive-le-le-add-positive-ℚ y x d))
```

## Completeness of the real numbers

### Cauchy approximations in the real numbers

```agda
cauchy-approximation-leq-ℝ : (l : Level) → UU (lsuc l)
cauchy-approximation-leq-ℝ l =
  cauchy-approximation-Metric-Space (metric-space-leq-ℝ l)

map-cauchy-approximation-leq-ℝ :
  {l : Level} → (x : cauchy-approximation-leq-ℝ l) → ℚ⁺ → ℝ l
map-cauchy-approximation-leq-ℝ {l} =
  map-cauchy-approximation-Metric-Space (metric-space-leq-ℝ l)

is-cauchy-map-cauchy-approximation-leq-ℝ :
  {l : Level} → (x : cauchy-approximation-leq-ℝ l) →
  (ε δ : ℚ⁺) →
  neighborhood-Metric-Space
    ( metric-space-leq-ℝ l)
    ( ε +ℚ⁺ δ)
    ( map-cauchy-approximation-leq-ℝ x ε)
    ( map-cauchy-approximation-leq-ℝ x δ)
is-cauchy-map-cauchy-approximation-leq-ℝ {l} x =
  is-cauchy-approximation-map-cauchy-approximation-Metric-Space
    ( metric-space-leq-ℝ l)
    ( x)
```

### Cauchy approximations in the real numbers are convergent

#### The limit of a Cauchy sequence

```agda
module _
  {l : Level} (x : cauchy-approximation-leq-ℝ l)
  where

  lower-cut-lim-cauchy-approximation-leq-ℝ : subtype l ℚ
  lower-cut-lim-cauchy-approximation-leq-ℝ q =
    ∃
      ( ℚ⁺ × ℚ⁺)
      ( λ (ε , θ) →
        lower-cut-ℝ
          ( map-cauchy-approximation-leq-ℝ x ε)
          ( q +ℚ rational-ℚ⁺ (ε +ℚ⁺ θ)))

  upper-cut-lim-cauchy-approximation-leq-ℝ : subtype l ℚ
  upper-cut-lim-cauchy-approximation-leq-ℝ q =
    ∃
      ( ℚ⁺ × ℚ⁺)
      ( λ (ε , θ) →
        upper-cut-ℝ
          ( map-cauchy-approximation-leq-ℝ x ε)
          ( q -ℚ (rational-ℚ⁺ (ε +ℚ⁺ θ))))

  abstract
    is-inhabited-lower-cut-lim-cauchy-approximation-leq-ℝ :
      exists ℚ lower-cut-lim-cauchy-approximation-leq-ℝ
    is-inhabited-lower-cut-lim-cauchy-approximation-leq-ℝ =
      do
        let
          x1 = map-cauchy-approximation-leq-ℝ x one-ℚ⁺
          two-ℚ = one-ℚ +ℚ one-ℚ
        p , p<x1 ← is-inhabited-lower-cut-ℝ x1
        intro-exists
          ( p -ℚ two-ℚ)
          ( intro-exists
            ( one-ℚ⁺ , one-ℚ⁺)
            ( inv-tr
              ( is-in-lower-cut-ℝ x1)
              ( is-section-right-div-Group group-add-ℚ two-ℚ p)
              ( p<x1)))
      where
        open do-syntax-trunc-Prop (∃ ℚ lower-cut-lim-cauchy-approximation-leq-ℝ)

    is-inhabited-upper-cut-lim-cauchy-approximation-leq-ℝ :
      exists ℚ upper-cut-lim-cauchy-approximation-leq-ℝ
    is-inhabited-upper-cut-lim-cauchy-approximation-leq-ℝ =
      do
        let
          x1 = map-cauchy-approximation-leq-ℝ x one-ℚ⁺
          two-ℚ = one-ℚ +ℚ one-ℚ
        q , x1<q ← is-inhabited-upper-cut-ℝ x1
        intro-exists
          ( q +ℚ two-ℚ)
          ( intro-exists
            ( one-ℚ⁺ , one-ℚ⁺)
            ( inv-tr
              ( is-in-upper-cut-ℝ x1)
              ( is-retraction-right-div-Group group-add-ℚ two-ℚ q)
              ( x1<q)))
      where
        open do-syntax-trunc-Prop (∃ ℚ upper-cut-lim-cauchy-approximation-leq-ℝ)

    is-rounded-lower-cut-lim-cauchy-approximation-leq-ℝ :
      (q : ℚ) →
      is-in-subtype lower-cut-lim-cauchy-approximation-leq-ℝ q ↔
      exists
        ( ℚ)
        ( λ r → le-ℚ-Prop q r ∧ lower-cut-lim-cauchy-approximation-leq-ℝ r)
    pr1 (is-rounded-lower-cut-lim-cauchy-approximation-leq-ℝ q) q<lim =
      do
        (ε⁺@(ε , _) , θ⁺@(θ , _)) , q+ε+θ<xε ← q<lim
        let xε = map-cauchy-approximation-leq-ℝ x ε⁺
        r , q+ε+θ<r , r<xε ←
          forward-implication
            ( is-rounded-lower-cut-ℝ
              ( map-cauchy-approximation-leq-ℝ x ε⁺)
              ( q +ℚ (ε +ℚ θ)))
            ( q+ε+θ<xε)
        intro-exists
          ( r -ℚ (ε +ℚ θ))
          ( tr
            ( λ s → le-ℚ s (r -ℚ (ε +ℚ θ)))
            ( is-retraction-right-div-Group group-add-ℚ (ε +ℚ θ) q)
            ( preserves-le-left-add-ℚ
              ( neg-ℚ (ε +ℚ θ))
              ( q +ℚ (ε +ℚ θ))
              ( r)
              ( q+ε+θ<r)) ,
            intro-exists
              ( ε⁺ , θ⁺)
              ( inv-tr
                ( is-in-lower-cut-ℝ xε)
                ( is-section-right-div-Group group-add-ℚ (ε +ℚ θ) r)
                ( r<xε)))
      where
        open
          do-syntax-trunc-Prop
            ( ∃
              ( ℚ)
              ( λ r →
                le-ℚ-Prop q r ∧ lower-cut-lim-cauchy-approximation-leq-ℝ r))
    pr2 (is-rounded-lower-cut-lim-cauchy-approximation-leq-ℝ q) ∃r =
      do
        r , q<r , r<lim ← ∃r
        (ε⁺@(ε , _) , θ⁺@(θ , _)) , r+ε+θ<xε ← r<lim
        let xε = map-cauchy-approximation-leq-ℝ x ε⁺
        intro-exists
          ( ε⁺ , θ⁺)
          ( le-lower-cut-ℝ
            ( xε)
            ( q +ℚ (ε +ℚ θ))
            ( r +ℚ (ε +ℚ θ))
            ( preserves-le-left-add-ℚ (ε +ℚ θ) q r q<r)
            ( r+ε+θ<xε))
      where
        open do-syntax-trunc-Prop (lower-cut-lim-cauchy-approximation-leq-ℝ q)

    is-rounded-upper-cut-lim-cauchy-approximation-leq-ℝ :
      (q : ℚ) →
      is-in-subtype upper-cut-lim-cauchy-approximation-leq-ℝ q ↔
      exists
        ( ℚ)
        ( λ p → le-ℚ-Prop p q ∧ upper-cut-lim-cauchy-approximation-leq-ℝ p)
    pr1 (is-rounded-upper-cut-lim-cauchy-approximation-leq-ℝ q) lim<q =
      do
        (ε⁺@(ε , _) , θ⁺@(θ , _)) , xε<q-ε-θ ← lim<q
        let xε = map-cauchy-approximation-leq-ℝ x ε⁺
        p , p<q-ε-θ , xε<p ←
          forward-implication
            ( is-rounded-upper-cut-ℝ xε (q -ℚ (ε +ℚ θ)))
            ( xε<q-ε-θ)
        intro-exists
          ( p +ℚ (ε +ℚ θ))
          ( tr
              ( le-ℚ (p +ℚ (ε +ℚ θ)))
              ( is-section-right-div-Group group-add-ℚ (ε +ℚ θ) q)
              ( preserves-le-left-add-ℚ (ε +ℚ θ) p (q -ℚ (ε +ℚ θ)) p<q-ε-θ) ,
            intro-exists
              ( ε⁺ , θ⁺)
              ( inv-tr
                ( is-in-upper-cut-ℝ xε)
                ( is-retraction-right-div-Group group-add-ℚ (ε +ℚ θ) p)
                ( xε<p)))
      where
        open
          do-syntax-trunc-Prop
            ( ∃
              ( ℚ)
              ( λ p →
                le-ℚ-Prop p q ∧ upper-cut-lim-cauchy-approximation-leq-ℝ p))
    pr2 (is-rounded-upper-cut-lim-cauchy-approximation-leq-ℝ q) ∃p =
      do
        p , p<q , lim<p ← ∃p
        (ε⁺@(ε , _) , θ⁺@(θ , _)) , xε<p-ε-θ ← lim<p
        let xε = map-cauchy-approximation-leq-ℝ x ε⁺
        intro-exists
          ( ε⁺ , θ⁺)
          ( le-upper-cut-ℝ
            ( xε)
            ( p -ℚ (ε +ℚ θ))
            ( q -ℚ (ε +ℚ θ))
            ( preserves-le-left-add-ℚ (neg-ℚ (ε +ℚ θ)) p q p<q)
            ( xε<p-ε-θ))
      where
        open do-syntax-trunc-Prop (upper-cut-lim-cauchy-approximation-leq-ℝ q)

  lower-real-lim-cauchy-approximation-leq-ℝ : lower-ℝ l
  lower-real-lim-cauchy-approximation-leq-ℝ =
    lower-cut-lim-cauchy-approximation-leq-ℝ ,
    is-inhabited-lower-cut-lim-cauchy-approximation-leq-ℝ ,
    is-rounded-lower-cut-lim-cauchy-approximation-leq-ℝ

  upper-real-lim-cauchy-approximation-leq-ℝ : upper-ℝ l
  upper-real-lim-cauchy-approximation-leq-ℝ =
    upper-cut-lim-cauchy-approximation-leq-ℝ ,
    is-inhabited-upper-cut-lim-cauchy-approximation-leq-ℝ ,
    is-rounded-upper-cut-lim-cauchy-approximation-leq-ℝ

  abstract
    is-disjoint-cut-lim-cauchy-approximation-leq-ℝ :
      (q : ℚ) →
      ¬
        ( is-in-subtype lower-cut-lim-cauchy-approximation-leq-ℝ q ×
          is-in-subtype upper-cut-lim-cauchy-approximation-leq-ℝ q)
    is-disjoint-cut-lim-cauchy-approximation-leq-ℝ q (q<lim , lim<q) =
      do
        (εl⁺@(εl , _) , θl⁺@(θl , _)) , q+εl+θl<xεl ← q<lim
        (εu⁺@(εu , _) , θu⁺@(θu , _)) , xεu<q-εu-θu ← lim<q
        let xεl = map-cauchy-approximation-leq-ℝ x εl⁺
            xεu = map-cauchy-approximation-leq-ℝ x εu⁺
            q-εu+θl<xεu : is-in-lower-cut-ℝ xεu ((q -ℚ εu) +ℚ θl)
            q-εu+θl<xεu =
              pr2
                ( is-cauchy-map-cauchy-approximation-leq-ℝ x εl⁺ εu⁺)
                ( (q -ℚ εu) +ℚ θl)
                ( inv-tr
                  ( is-in-lower-cut-ℝ xεl)
                  ( equational-reasoning
                      ((q -ℚ εu) +ℚ θl) +ℚ (εl +ℚ εu)
                      ＝ ((q +ℚ θl) -ℚ εu) +ℚ (εu +ℚ εl)
                        by
                          ap-add-ℚ
                            ( right-swap-add-ℚ q (neg-ℚ εu) θl)
                            ( commutative-add-ℚ εl εu)
                      ＝ ((q +ℚ θl) -ℚ εu) +ℚ εu +ℚ εl
                        by inv (associative-add-ℚ _ _ _)
                      ＝ (q +ℚ θl) +ℚ εl by ap (_+ℚ εl) (is-section-diff-ℚ _ _)
                      ＝ q +ℚ (θl +ℚ εl) by associative-add-ℚ _ _ _
                      ＝ q +ℚ (εl +ℚ θl) by ap (q +ℚ_) (commutative-add-ℚ _ _))
                  ( q+εl+θl<xεl))
            q-εu<xεu : is-in-lower-cut-ℝ xεu (q -ℚ εu)
            q-εu<xεu =
              le-lower-cut-ℝ
                ( xεu)
                ( q -ℚ εu)
                ( (q -ℚ εu) +ℚ θl)
                ( le-right-add-rational-ℚ⁺ (q -ℚ εu) θl⁺)
                ( q-εu+θl<xεu)
            xεu<q-εu : is-in-upper-cut-ℝ xεu (q -ℚ εu)
            xεu<q-εu =
              tr
                ( is-in-upper-cut-ℝ xεu)
                ( equational-reasoning
                  (q -ℚ (εu +ℚ θu)) +ℚ θu
                  ＝ (q +ℚ (neg-ℚ εu +ℚ neg-ℚ θu)) +ℚ θu
                    by ap (λ r → (q +ℚ r) +ℚ θu) (distributive-neg-add-ℚ εu θu)
                  ＝ ((q -ℚ εu) -ℚ θu) +ℚ θu
                    by ap (_+ℚ θu) (inv (associative-add-ℚ _ _ _))
                  ＝ q -ℚ εu by is-section-diff-ℚ θu _)
                (le-upper-cut-ℝ
                  ( xεu)
                  ( q -ℚ (εu +ℚ θu))
                  ( (q -ℚ (εu +ℚ θu)) +ℚ θu)
                  ( le-right-add-rational-ℚ⁺ (q -ℚ (εu +ℚ θu)) θu⁺)
                  ( xεu<q-εu-θu))
        is-disjoint-cut-ℝ xεu (q -ℚ εu) (q-εu<xεu , xεu<q-εu)
      where open do-syntax-trunc-Prop empty-Prop

    is-located-lower-upper-cut-lim-cauchy-approximation-leq-ℝ :
      is-located-lower-upper-ℝ
        ( lower-real-lim-cauchy-approximation-leq-ℝ)
        ( upper-real-lim-cauchy-approximation-leq-ℝ)
    is-located-lower-upper-cut-lim-cauchy-approximation-leq-ℝ p q p<q =
      do
        ε'⁺@(ε' , _) , 2ε'⁺<q-p ← double-le-ℚ⁺ (positive-diff-le-ℚ p q p<q)
        ε⁺@(ε , _) , 2ε⁺<ε'⁺ ← double-le-ℚ⁺ ε'⁺
        let
          2ε' = ε' +ℚ ε'
          2ε = ε +ℚ ε
          4ε = 2ε +ℚ 2ε
          4ε<q-p : le-ℚ ((ε +ℚ ε) +ℚ (ε +ℚ ε)) (q -ℚ p)
          4ε<q-p =
            transitive-le-ℚ
              ( 4ε)
              ( 2ε')
              ( q -ℚ p)
              ( 2ε'⁺<q-p)
              ( preserves-le-add-ℚ {2ε} {ε'} {2ε} {ε'} 2ε⁺<ε'⁺ 2ε⁺<ε'⁺)
          p+2ε<q-2ε : le-ℚ (p +ℚ 2ε) (q -ℚ 2ε)
          p+2ε<q-2ε =
            le-transpose-left-add-ℚ
              ( p +ℚ 2ε)
              ( 2ε)
              ( q)
              ( inv-tr
                ( λ r → le-ℚ r q)
                ( associative-add-ℚ p 2ε 2ε ∙ commutative-add-ℚ p 4ε)
                ( le-transpose-right-diff-ℚ 4ε q p 4ε<q-p))
        elim-disjunction
          claim
          ( λ p+2ε<xε → inl-disjunction (intro-exists (ε⁺ , ε⁺) p+2ε<xε))
          ( λ xε<q-2ε → inr-disjunction (intro-exists (ε⁺ , ε⁺) xε<q-2ε))
          ( is-located-lower-upper-cut-ℝ
            ( map-cauchy-approximation-leq-ℝ x ε⁺)
            ( p +ℚ 2ε)
            ( q -ℚ 2ε)
            ( p+2ε<q-2ε))
      where
        claim : Prop l
        claim =
          lower-cut-lim-cauchy-approximation-leq-ℝ p ∨
          upper-cut-lim-cauchy-approximation-leq-ℝ q
        open do-syntax-trunc-Prop claim

  lim-cauchy-approximation-leq-ℝ : ℝ l
  lim-cauchy-approximation-leq-ℝ =
    real-lower-upper-ℝ
      ( lower-real-lim-cauchy-approximation-leq-ℝ)
      ( upper-real-lim-cauchy-approximation-leq-ℝ)
      ( is-disjoint-cut-lim-cauchy-approximation-leq-ℝ)
      ( is-located-lower-upper-cut-lim-cauchy-approximation-leq-ℝ)
```

#### The limit satisfies the definition of a limit of a Cauchy approximation

```agda
module _
  {l : Level} (x : cauchy-approximation-leq-ℝ l)
  where

  is-limit-lim-cauchy-approximation-leq-ℝ :
    is-limit-cauchy-approximation-Premetric-Space
      ( premetric-space-leq-ℝ l)
      ( x)
      ( lim-cauchy-approximation-leq-ℝ x)
  is-limit-lim-cauchy-approximation-leq-ℝ ε⁺@(ε , _) θ⁺@(θ , _) =
    do
      let
        lim = lim-cauchy-approximation-leq-ℝ x
        xε = map-cauchy-approximation-leq-ℝ x ε⁺
        θ'⁺@(θ' , _) = left-summand-split-ℚ⁺ θ⁺
        θ''⁺@(θ'' , _) = right-summand-split-ℚ⁺ θ⁺
      ( r , xε+ε+θ'<r , r<xε+ε+θ) ←
        tr
          ( le-ℝ (xε +ℝ real-ℚ (ε +ℚ θ')))
          ( equational-reasoning
            xε +ℝ real-ℚ (ε +ℚ θ') +ℝ real-ℚ θ''
            ＝ xε +ℝ (real-ℚ (ε +ℚ θ') +ℝ real-ℚ θ'') by associative-add-ℝ _ _ _
            ＝ xε +ℝ real-ℚ (ε +ℚ θ' +ℚ θ'') by ap (xε +ℝ_) (add-real-ℚ _ _)
            ＝ xε +ℝ real-ℚ (ε +ℚ (θ' +ℚ θ''))
              by ap (λ a → xε +ℝ real-ℚ a) (associative-add-ℚ ε θ' θ'')
            ＝ xε +ℝ real-ℚ (ε +ℚ θ)
              by
                ap
                  ( λ a → xε +ℝ real-ℚ (ε +ℚ rational-ℚ⁺ a))
                  ( eq-add-split-ℚ⁺ θ⁺))
          ( le-left-add-real-ℝ⁺
            ( xε +ℝ (real-ℚ (ε +ℚ θ')))
            ( positive-real-ℚ⁺ θ''⁺))
      ( q , xε-ε-θ<q , q<xε-ε-θ') ←
        tr
          ( λ y → le-ℝ y (xε -ℝ real-ℚ (ε +ℚ θ')))
          ( equational-reasoning
            xε -ℝ real-ℚ (ε +ℚ θ') -ℝ real-ℚ θ''
            ＝ xε +ℝ (neg-ℝ (real-ℚ (ε +ℚ θ')) +ℝ neg-ℝ (real-ℚ θ''))
              by associative-add-ℝ _ _ _
            ＝ xε -ℝ (real-ℚ (ε +ℚ θ') +ℝ real-ℚ θ'')
              by
                ap
                  ( xε +ℝ_)
                  ( inv
                    ( distributive-neg-add-ℝ (real-ℚ (ε +ℚ θ')) (real-ℚ θ'')))
            ＝ xε -ℝ real-ℚ (ε +ℚ θ' +ℚ θ'') by ap (xε -ℝ_) (add-real-ℚ _ _)
            ＝ xε -ℝ real-ℚ (ε +ℚ (θ' +ℚ θ''))
              by ap (λ a → xε -ℝ real-ℚ a) (associative-add-ℚ _ _ _)
            ＝ xε -ℝ real-ℚ (ε +ℚ θ)
              by
                ap
                  ( λ a → xε -ℝ real-ℚ (ε +ℚ rational-ℚ⁺ a))
                  ( eq-add-split-ℚ⁺ θ⁺))
          ( le-diff-real-ℝ⁺ (xε -ℝ real-ℚ (ε +ℚ θ')) (positive-real-ℚ⁺ θ''⁺))
      let
        xε<r-ε-θ' : is-in-upper-cut-ℝ xε (r -ℚ (ε +ℚ θ'))
        xε<r-ε-θ' =
          upper-cut-real-le-ℚ
            ( r -ℚ (ε +ℚ θ'))
            ( xε)
            ( tr
              ( le-ℝ xε)
              ( equational-reasoning
                real-ℚ r -ℝ real-ℚ (ε +ℚ θ')
                ＝ real-ℚ r +ℝ real-ℚ (neg-ℚ (ε +ℚ θ'))
                  by ap (real-ℚ r +ℝ_) (neg-real-ℚ _)
                ＝ real-ℚ (r -ℚ (ε +ℚ θ')) by add-real-ℚ _ _)
              ( forward-implication
                ( iff-diff-right-le-ℝ xε (real-ℚ (ε +ℚ θ')) (real-ℚ r))
                ( le-upper-cut-real-ℚ r (xε +ℝ real-ℚ (ε +ℚ θ')) xε+ε+θ'<r)))
        lim<r : is-in-upper-cut-ℝ lim r
        lim<r = intro-exists (ε⁺ , θ'⁺) xε<r-ε-θ'
        q+ε+θ'<xε : is-in-lower-cut-ℝ xε (q +ℚ (ε +ℚ θ'))
        q+ε+θ'<xε =
          lower-cut-real-le-ℚ
            ( q +ℚ (ε +ℚ θ'))
            ( xε)
            ( tr
              ( λ y → le-ℝ y xε)
              ( add-real-ℚ _ _)
              ( backward-implication
                ( iff-diff-right-le-ℝ (real-ℚ q) (real-ℚ (ε +ℚ θ')) xε)
                ( le-lower-cut-real-ℚ q (xε -ℝ real-ℚ (ε +ℚ θ')) q<xε-ε-θ')))
        q<lim : is-in-lower-cut-ℝ lim q
        q<lim = intro-exists (ε⁺ , θ'⁺) q+ε+θ'<xε
      neighborhood-±-bound-leq-ℝ
        ( ε⁺ +ℚ⁺ θ⁺)
        ( xε)
        ( lim)
        ( leq-le-ℝ
          ( xε)
          ( lim +ℝ real-ℚ (ε +ℚ θ))
          ( forward-implication
            ( iff-add-right-le-ℝ
              ( xε)
              ( real-ℚ (ε +ℚ θ))
              ( lim))
            ( transitive-le-ℝ
              ( xε -ℝ real-ℚ (ε +ℚ θ))
              ( real-ℚ q)
              ( lim)
              ( le-lower-cut-real-ℚ q lim q<lim)
              ( le-upper-cut-real-ℚ q (xε -ℝ real-ℚ (ε +ℚ θ)) xε-ε-θ<q))))
        ( leq-le-ℝ
          ( lim)
          ( xε +ℝ real-ℚ (ε +ℚ θ))
          ( transitive-le-ℝ
            ( lim)
            ( real-ℚ r)
            ( xε +ℝ real-ℚ (ε +ℚ θ))
            ( le-lower-cut-real-ℚ r (xε +ℝ real-ℚ (ε +ℚ θ)) r<xε+ε+θ)
            ( le-upper-cut-real-ℚ r lim lim<r)))
    where
      open
        do-syntax-trunc-Prop
          ( premetric-leq-ℝ
            ( l)
            ( ε⁺ +ℚ⁺ θ⁺)
            ( map-cauchy-approximation-leq-ℝ x ε⁺)
            ( lim-cauchy-approximation-leq-ℝ x))

  is-convergent-cauchy-approximation-leq-ℝ :
    is-convergent-cauchy-approximation-Metric-Space
      ( metric-space-leq-ℝ l)
      ( x)
  is-convergent-cauchy-approximation-leq-ℝ =
    lim-cauchy-approximation-leq-ℝ x ,
    is-limit-lim-cauchy-approximation-leq-ℝ
```

### The standard metric space of real numbers is complete

```agda
is-complete-metric-space-leq-ℝ :
  (l : Level) → is-complete-Metric-Space (metric-space-leq-ℝ l)
is-complete-metric-space-leq-ℝ _ = is-convergent-cauchy-approximation-leq-ℝ

complete-metric-space-leq-ℝ :
  (l : Level) → Complete-Metric-Space (lsuc l) l
pr1 (complete-metric-space-leq-ℝ l) = metric-space-leq-ℝ l
pr2 (complete-metric-space-leq-ℝ l) = is-complete-metric-space-leq-ℝ l
```

## References

{{#bibliography}}
