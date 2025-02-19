# The standard metric structure on the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.metric-space-of-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-cartesian-products-of-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.extensional-premetric-structures
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-in-premetric-spaces
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
```

</details>

## Idea

[Inequality](elementary-number-theory.inequality-rational-numbers.md) on the
[rational numbers](elementary-number-theory.rational-numbers.md) induces a
[premetric](metric-spaces.premetric-structures.md) on `ℚ` where `x y : ℚ` are in
a `d`-neighborhood when `y ≤ x + d` and `x ≤ y + d`, i.e. upper bounds on the
distance between `x` and `y` are upper bounds of both `y - x` and `x - y`. This
is a [metric structure](metric-spaces.metric-structures.md) on `ℚ` that defines
the
{{#concept "standard metric space of rational numbers" Agda=metric-space-leq-ℚ}}.

## Definitions

### The standard saturated premetric on the rational numbers

```agda
lower-neighborhood-leq-prop-ℚ : (d : ℚ⁺) (x y : ℚ) → Prop lzero
lower-neighborhood-leq-prop-ℚ d x y =
  leq-ℚ-Prop y (x +ℚ (rational-ℚ⁺ d))

lower-neighborhood-leq-ℚ : (d : ℚ⁺) (x y : ℚ) → UU lzero
lower-neighborhood-leq-ℚ d x y = type-Prop (lower-neighborhood-leq-prop-ℚ d x y)

is-prop-lower-neighborhood-leq-ℚ :
  (d : ℚ⁺) (x y : ℚ) → is-prop (lower-neighborhood-leq-ℚ d x y)
is-prop-lower-neighborhood-leq-ℚ d x y =
  is-prop-type-Prop (lower-neighborhood-leq-prop-ℚ d x y)

premetric-leq-ℚ : Premetric lzero ℚ
premetric-leq-ℚ d x y =
  product-Prop
    ( lower-neighborhood-leq-prop-ℚ d x y)
    ( lower-neighborhood-leq-prop-ℚ d y x)
```

## Properties

### The standard premetric on the rational numbers is a metric

```agda
is-reflexive-premetric-leq-ℚ : is-reflexive-Premetric premetric-leq-ℚ
is-reflexive-premetric-leq-ℚ d x =
  diagonal-product
    ( leq-ℚ x (x +ℚ (rational-ℚ⁺ d)))
    ( leq-le-ℚ {x} {x +ℚ (rational-ℚ⁺ d)} (le-right-add-rational-ℚ⁺ x d))

is-symmetric-premetric-leq-ℚ : is-symmetric-Premetric premetric-leq-ℚ
is-symmetric-premetric-leq-ℚ d x y (H , K) = (K , H)

is-tight-premetric-leq-ℚ : is-tight-Premetric premetric-leq-ℚ
is-tight-premetric-leq-ℚ x y H =
  antisymmetric-leq-ℚ
    ( x)
    ( y)
    ( map-inv-equiv (equiv-leq-leq-add-positive-ℚ x y) (pr2 ∘ H))
    ( map-inv-equiv (equiv-leq-leq-add-positive-ℚ y x) (pr1 ∘ H))

is-local-premetric-leq-ℚ : is-local-Premetric premetric-leq-ℚ
is-local-premetric-leq-ℚ =
  is-local-is-tight-Premetric
    premetric-leq-ℚ
    is-tight-premetric-leq-ℚ

is-triangular-premetric-leq-ℚ :
  is-triangular-Premetric premetric-leq-ℚ
pr1 (is-triangular-premetric-leq-ℚ x y z d₁ d₂ Hyz Hxy) =
  tr
    ( leq-ℚ z)
    ( associative-add-ℚ x (rational-ℚ⁺ d₁) (rational-ℚ⁺ d₂))
    ( transitive-leq-ℚ
      ( z)
      ( y +ℚ ( rational-ℚ⁺ d₂))
      ( x +ℚ (rational-ℚ⁺ d₁) +ℚ (rational-ℚ⁺ d₂))
      ( preserves-leq-left-add-ℚ
        ( rational-ℚ⁺ d₂)
        ( y)
        ( x +ℚ (rational-ℚ⁺ d₁))
        ( pr1 Hxy))
      ( pr1 Hyz))
pr2 (is-triangular-premetric-leq-ℚ x y z d₁ d₂ Hyz Hxy) =
  tr
    ( leq-ℚ x)
    ( ap (z +ℚ_) (commutative-add-ℚ (rational-ℚ⁺ d₂) (rational-ℚ⁺ d₁)))
    ( tr
      ( leq-ℚ x)
      ( associative-add-ℚ z (rational-ℚ⁺ d₂) (rational-ℚ⁺ d₁))
      ( transitive-leq-ℚ
        ( x)
        ( y +ℚ (rational-ℚ⁺ d₁))
        ( z +ℚ (rational-ℚ⁺ d₂) +ℚ (rational-ℚ⁺ d₁))
        ( ( preserves-leq-left-add-ℚ
          ( rational-ℚ⁺ d₁)
          ( y)
          ( z +ℚ (rational-ℚ⁺ d₂))
          ( pr2 Hyz)))
        ( pr2 Hxy)))

is-pseudometric-premetric-leq-ℚ : is-pseudometric-Premetric premetric-leq-ℚ
is-pseudometric-premetric-leq-ℚ =
  is-reflexive-premetric-leq-ℚ ,
  is-symmetric-premetric-leq-ℚ ,
  is-triangular-premetric-leq-ℚ

is-metric-premetric-leq-ℚ : is-metric-Premetric premetric-leq-ℚ
pr1 is-metric-premetric-leq-ℚ = is-pseudometric-premetric-leq-ℚ
pr2 is-metric-premetric-leq-ℚ = is-local-premetric-leq-ℚ
```

### The standard metric space of rational numbers

```agda
premetric-space-leq-ℚ : Premetric-Space lzero lzero
premetric-space-leq-ℚ = ℚ , premetric-leq-ℚ

metric-space-leq-ℚ : Metric-Space lzero lzero
pr1 metric-space-leq-ℚ = premetric-space-leq-ℚ
pr2 metric-space-leq-ℚ = is-metric-premetric-leq-ℚ
```

## Properties

### The standard saturated metric space of rationa numbers is saturated

```agda
is-saturated-metric-space-leq-ℚ :
  is-saturated-Metric-Space metric-space-leq-ℚ
is-saturated-metric-space-leq-ℚ ε x y H =
  map-inv-equiv
    ( equiv-leq-leq-add-positive-ℚ y (x +ℚ rational-ℚ⁺ ε))
    ( λ δ →
      inv-tr
        ( leq-ℚ y)
        ( associative-add-ℚ x (rational-ℚ⁺ ε) (rational-ℚ⁺ δ))
        ( pr1 (H δ))) ,
  map-inv-equiv
    ( equiv-leq-leq-add-positive-ℚ x (y +ℚ rational-ℚ⁺ ε))
    ( λ δ →
      inv-tr
        ( leq-ℚ x)
        ( associative-add-ℚ y (rational-ℚ⁺ ε) (rational-ℚ⁺ δ))
        ( pr2 (H δ)))
```

### Addition of rational numbers is an isometry

```agda
module _
  (x u v : ℚ) (d : ℚ⁺)
  where

  preserves-lower-neighborhood-leq-add-ℚ :
    lower-neighborhood-leq-ℚ d u v →
    lower-neighborhood-leq-ℚ d (x +ℚ u) (x +ℚ v)
  preserves-lower-neighborhood-leq-add-ℚ H =
    inv-tr
      ( leq-ℚ (x +ℚ v))
      ( associative-add-ℚ x u (rational-ℚ⁺ d))
      ( preserves-leq-right-add-ℚ
        ( x)
        ( v)
        ( u +ℚ rational-ℚ⁺ d)
        ( H))

  reflects-lower-neighborhood-leq-add-ℚ :
    lower-neighborhood-leq-ℚ d (x +ℚ u) (x +ℚ v) →
    lower-neighborhood-leq-ℚ d u v
  reflects-lower-neighborhood-leq-add-ℚ =
    ( reflects-order-right-add-ℚ x v (u +ℚ rational-ℚ⁺ d)) ∘
    ( tr (leq-ℚ (x +ℚ v)) (associative-add-ℚ x u (rational-ℚ⁺ d)))
```

```agda
module _
  (x : ℚ)
  where

  is-isometry-add-ℚ :
    is-isometry-Metric-Space
      ( metric-space-leq-ℚ)
      ( metric-space-leq-ℚ)
      ( add-ℚ x)
  is-isometry-add-ℚ d y z =
    pair
      ( map-product
        ( preserves-lower-neighborhood-leq-add-ℚ x y z d)
        ( preserves-lower-neighborhood-leq-add-ℚ x z y d))
      ( map-product
        ( reflects-lower-neighborhood-leq-add-ℚ x y z d)
        ( reflects-lower-neighborhood-leq-add-ℚ x z y d))

  is-isometry-add-ℚ' :
    is-isometry-Metric-Space
      ( metric-space-leq-ℚ)
      ( metric-space-leq-ℚ)
      ( add-ℚ' x)
  is-isometry-add-ℚ' d y z =
    binary-tr
      ( λ u v → type-iff-Prop (premetric-leq-ℚ d y z) (premetric-leq-ℚ d u v))
      ( commutative-add-ℚ x y)
      ( commutative-add-ℚ x z)
      ( is-isometry-add-ℚ d y z)
```

### The convergent cauchy approximation of the canonical inclusion of positive rational numbers into the rational numbers

```agda
is-cauchy-approximation-rational-ℚ⁺ :
  is-cauchy-approximation-Metric-Space
    metric-space-leq-ℚ
    rational-ℚ⁺
is-cauchy-approximation-rational-ℚ⁺ ε δ =
  ( leq-le-ℚ
    { rational-ℚ⁺ δ}
    { rational-ℚ⁺ ε +ℚ (rational-ℚ⁺ (ε +ℚ⁺ δ))}
    ( transitive-le-ℚ
      ( rational-ℚ⁺ δ)
      ( rational-ℚ⁺ (ε +ℚ⁺ δ))
      ( rational-ℚ⁺ ε +ℚ (rational-ℚ⁺ (ε +ℚ⁺ δ)))
      ( le-right-add-ℚ⁺
        ( ε)
        ( ε +ℚ⁺ δ))
      ( le-right-add-ℚ⁺ ε δ))) ,
  ( leq-le-ℚ
    { rational-ℚ⁺ ε}
    { rational-ℚ⁺ δ +ℚ (rational-ℚ⁺ (ε +ℚ⁺ δ))}
    ( transitive-le-ℚ
      ( rational-ℚ⁺ ε)
      ( rational-ℚ⁺ (ε +ℚ⁺ δ))
      ( rational-ℚ⁺ δ +ℚ (rational-ℚ⁺ (ε +ℚ⁺ δ)))
      ( le-right-add-ℚ⁺
        ( δ)
        ( ε +ℚ⁺ δ))
      ( le-left-add-ℚ⁺ ε δ)))

cauchy-approximation-rational-ℚ⁺ :
  cauchy-approximation-Metric-Space metric-space-leq-ℚ
cauchy-approximation-rational-ℚ⁺ =
  rational-ℚ⁺ , is-cauchy-approximation-rational-ℚ⁺

is-zero-limit-rational-ℚ⁺ :
  is-limit-cauchy-approximation-Premetric-Space
    ( premetric-Metric-Space metric-space-leq-ℚ)
    ( cauchy-approximation-rational-ℚ⁺)
    ( zero-ℚ)
is-zero-limit-rational-ℚ⁺ ε δ =
  ( leq-le-ℚ
    { zero-ℚ}
    { rational-ℚ⁺ (ε +ℚ⁺ (ε +ℚ⁺ δ))}
    ( le-zero-is-positive-ℚ
      ( rational-ℚ⁺ (ε +ℚ⁺ (ε +ℚ⁺ δ)))
      ( is-positive-rational-ℚ⁺
        (ε +ℚ⁺ (ε +ℚ⁺ δ))))) ,
  ( leq-le-ℚ
    { rational-ℚ⁺ ε}
    { zero-ℚ +ℚ rational-ℚ⁺ (ε +ℚ⁺ δ)}
    ( inv-tr
      ( le-ℚ (rational-ℚ⁺ ε))
      ( left-unit-law-add-ℚ (rational-ℚ⁺ (ε +ℚ⁺ δ)))
      ( le-left-add-ℚ⁺ ε δ)))

convergent-rational-ℚ⁺ :
  convergent-cauchy-approximation-Metric-Space metric-space-leq-ℚ
convergent-rational-ℚ⁺ =
  cauchy-approximation-rational-ℚ⁺ ,
  zero-ℚ ,
  is-zero-limit-rational-ℚ⁺
```

## See also

- The
  [metric space of rational numbers with open neighborhoods](metric-spaces.metric-space-of-rational-numbers-with-open-neighborhoods.md)
