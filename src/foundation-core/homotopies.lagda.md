# Homotopies

```agda
module foundation-core.homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.universe-levels

open import foundation-core.dependent-identifications
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

A **homotopy** between dependent functions `f` and `g` is a pointwise equality
between them.

## Definitions

### The type family of identifications between values of two dependent functions

```agda
module _
  {l1 l2 : Level} {X : UU l1} {P : X → UU l2} (f g : (x : X) → P x)
  where

  eq-value : X → UU l2
  eq-value x = (f x ＝ g x)

  {-# INLINE eq-value #-}

  map-compute-dependent-identification-eq-value :
    {x y : X} (p : x ＝ y) (q : eq-value x) (r : eq-value y) →
    apd f p ∙ r ＝ ap (tr P p) q ∙ apd g p →
    dependent-identification eq-value p q r
  map-compute-dependent-identification-eq-value refl q r =
    inv ∘ (concat' r (right-unit ∙ ap-id q))
```

### The type family of identifications between values of two ordinary functions

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f g : X → Y)
  where

  eq-value-function : X → UU l2
  eq-value-function = eq-value f g

  {-# INLINE eq-value-function #-}

  map-compute-dependent-identification-eq-value-function :
    {x y : X} (p : x ＝ y) (q : eq-value f g x) (r : eq-value f g y) →
    ap f p ∙ r ＝ q ∙ ap g p →
    dependent-identification eq-value-function p q r
  map-compute-dependent-identification-eq-value-function refl q r =
    inv ∘ concat' r right-unit

map-compute-dependent-identification-eq-value-id-id :
  {l1 : Level} {A : UU l1} {a b : A} (p : a ＝ b) (q : a ＝ a) (r : b ＝ b) →
  p ∙ r ＝ q ∙ p → dependent-identification (eq-value id id) p q r
map-compute-dependent-identification-eq-value-id-id refl q r s =
  inv (s ∙ right-unit)

map-compute-dependent-identification-eq-value-comp-id :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (g : B → A) (f : A → B) {a b : A}
  (p : a ＝ b) (q : eq-value (g ∘ f) id a) (r : eq-value (g ∘ f) id b) →
  ap g (ap f p) ∙ r ＝ q ∙ p →
  dependent-identification (eq-value (g ∘ f) id) p q r
map-compute-dependent-identification-eq-value-comp-id g f refl q r s =
  inv (s ∙ right-unit)
```

### Homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  infix 6 _~_
  _~_ : (f g : (x : A) → B x) → UU (l1 ⊔ l2)
  f ~ g = (x : A) → eq-value f g x
```

## Properties

### Reflexivity

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  refl-htpy : {f : (x : A) → B x} → f ~ f
  refl-htpy x = refl

  refl-htpy' : (f : (x : A) → B x) → f ~ f
  refl-htpy' f = refl-htpy
```

### Inverting homotopies

```agda
  inv-htpy : {f g : (x : A) → B x} → f ~ g → g ~ f
  inv-htpy H x = inv (H x)
```

### Concatenating homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  infixl 15 _∙h_
  _∙h_ : {f g h : (x : A) → B x} → f ~ g → g ~ h → f ~ h
  (H ∙h K) x = (H x) ∙ (K x)

  concat-htpy :
    {f g : (x : A) → B x} →
    f ~ g → (h : (x : A) → B x) → g ~ h → f ~ h
  concat-htpy H h K x = concat (H x) (h x) (K x)

  concat-htpy' :
    (f : (x : A) → B x) {g h : (x : A) → B x} →
    g ~ h → f ~ g → f ~ h
  concat-htpy' f K H = H ∙h K

  concat-inv-htpy :
    {f g : (x : A) → B x} →
    f ~ g → (h : (x : A) → B x) → f ~ h → g ~ h
  concat-inv-htpy = concat-htpy ∘ inv-htpy

  concat-inv-htpy' :
    (f : (x : A) → B x) {g h : (x : A) → B x} →
    g ~ h → f ~ h → f ~ g
  concat-inv-htpy' f K = concat-htpy' f (inv-htpy K)
```

### Transposition of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  (H : f ~ g) (K : g ~ h) (L : f ~ h) (M : H ∙h K ~ L)
  where

  left-transpose-htpy-concat : K ~ inv-htpy H ∙h L
  left-transpose-htpy-concat x =
    left-transpose-eq-concat (H x) (K x) (L x) (M x)

  inv-htpy-left-transpose-htpy-concat : inv-htpy H ∙h L ~ K
  inv-htpy-left-transpose-htpy-concat = inv-htpy left-transpose-htpy-concat

  right-transpose-htpy-concat : H ~ L ∙h inv-htpy K
  right-transpose-htpy-concat x =
    right-transpose-eq-concat (H x) (K x) (L x) (M x)

  inv-htpy-right-transpose-htpy-concat : L ∙h inv-htpy K ~ H
  inv-htpy-right-transpose-htpy-concat = inv-htpy right-transpose-htpy-concat
```

### Associativity of concatenation of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h k : (x : A) → B x}
  (H : f ~ g) (K : g ~ h) (L : h ~ k)
  where

  assoc-htpy : (H ∙h K) ∙h L ~ H ∙h (K ∙h L)
  assoc-htpy x = assoc (H x) (K x) (L x)

  inv-htpy-assoc-htpy : H ∙h (K ∙h L) ~ (H ∙h K) ∙h L
  inv-htpy-assoc-htpy = inv-htpy assoc-htpy
```

### Unit laws for homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (x : A) → B x} {H : f ~ g}
  where

  left-unit-htpy : refl-htpy ∙h H ~ H
  left-unit-htpy x = left-unit

  inv-htpy-left-unit-htpy : H ~ refl-htpy ∙h H
  inv-htpy-left-unit-htpy = inv-htpy left-unit-htpy

  right-unit-htpy : H ∙h refl-htpy ~ H
  right-unit-htpy x = right-unit

  inv-htpy-right-unit-htpy : H ~ H ∙h refl-htpy
  inv-htpy-right-unit-htpy = inv-htpy right-unit-htpy
```

### Inverse laws for homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (x : A) → B x} (H : f ~ g)
  where

  left-inv-htpy : inv-htpy H ∙h H ~ refl-htpy
  left-inv-htpy = left-inv ∘ H

  inv-htpy-left-inv-htpy : refl-htpy ~ inv-htpy H ∙h H
  inv-htpy-left-inv-htpy = inv-htpy left-inv-htpy

  right-inv-htpy : H ∙h inv-htpy H ~ refl-htpy
  right-inv-htpy = right-inv ∘ H

  inv-htpy-right-inv-htpy : refl-htpy ~ H ∙h inv-htpy H
  inv-htpy-right-inv-htpy = inv-htpy right-inv-htpy
```

### Inverting homotopies is an involution

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (x : A) → B x} (H : f ~ g)
  where

  inv-inv-htpy : inv-htpy (inv-htpy H) ~ H
  inv-inv-htpy = inv-inv ∘ H
```

### Distributivity of `inv` over `concat` for homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  (H : f ~ g) (K : g ~ h)
  where

  distributive-inv-concat-htpy :
    inv-htpy (H ∙h K) ~ inv-htpy K ∙h inv-htpy H
  distributive-inv-concat-htpy x = distributive-inv-concat (H x) (K x)

  inv-htpy-distributive-inv-concat-htpy :
    inv-htpy K ∙h inv-htpy H ~ inv-htpy (H ∙h K)
  inv-htpy-distributive-inv-concat-htpy =
    inv-htpy distributive-inv-concat-htpy
```

### Naturality of homotopies with respect to identifications

Given two maps `f g : A → B` and a homotopy `H : f ~ g`, then for every
identification `p : x ＝ y` in `A`, we have a
[commuting square of identifications](foundation-core.commuting-squares-of-identifications.md)

```text
          ap f p
     f x -------> f y
      |            |
  H x |            | H y
      ∨            ∨
     g x -------> g y.
          ap g p
```

```agda
nat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  {x y : A} (p : x ＝ y) →
  H x ∙ ap g p ＝ ap f p ∙ H y
nat-htpy H refl = right-unit

inv-nat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  {x y : A} (p : x ＝ y) →
  ap f p ∙ H y ＝ H x ∙ ap g p
inv-nat-htpy H p = inv (nat-htpy H p)

nat-refl-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  {x y : A} (p : x ＝ y) →
  nat-htpy (refl-htpy' f) p ＝ inv right-unit
nat-refl-htpy f refl = refl

inv-nat-refl-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  {x y : A} (p : x ＝ y) →
  inv-nat-htpy (refl-htpy' f) p ＝ right-unit
inv-nat-refl-htpy f refl = refl

nat-htpy-id :
  {l : Level} {A : UU l} {f : A → A} (H : f ~ id)
  {x y : A} (p : x ＝ y) → H x ∙ p ＝ ap f p ∙ H y
nat-htpy-id H refl = right-unit

inv-nat-htpy-id :
  {l : Level} {A : UU l} {f : A → A} (H : f ~ id)
  {x y : A} (p : x ＝ y) → ap f p ∙ H y ＝ H x ∙ p
inv-nat-htpy-id H p = inv (nat-htpy-id H p)
```

### Conjugation by homotopies

Given a homotopy `H : f ~ g` we obtain a natural map `f x ＝ f y → g x ＝ g y`
given by conjugation by `H`.

```agda
conjugate-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B}
  (H : f ~ g) {x y : A} → f x ＝ f y → g x ＝ g y
conjugate-htpy H {x} {y} p = inv (H x) ∙ (p ∙ H y)
```

### Homotopies preserve the laws of the action on identity types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  ap-concat-htpy :
    (H : f ~ g) {K K' : g ~ h} → K ~ K' → H ∙h K ~ H ∙h K'
  ap-concat-htpy H L x = ap (concat (H x) (h x)) (L x)

  ap-concat-htpy' :
    {H H' : f ~ g} (K : g ~ h) → H ~ H' → H ∙h K ~ H' ∙h K
  ap-concat-htpy' K L x =
    ap (concat' (f x) (K x)) (L x)

  ap-binary-concat-htpy :
    {H H' : f ~ g} {K K' : g ~ h} → H ~ H' → K ~ K' → H ∙h K ~ H' ∙h K'
  ap-binary-concat-htpy {H} {H'} {K} {K'} HH KK =
    ap-concat-htpy H KK ∙h ap-concat-htpy' K' HH

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  {H H' : f ~ g}
  where

  ap-inv-htpy : H ~ H' → inv-htpy H ~ inv-htpy H'
  ap-inv-htpy K x = ap inv (K x)
```

### Concatenating with an inverse homotopy is inverse to concatenating

We show that the operation `K ↦ inv-htpy H ∙h K` is inverse to the operation
`K ↦ H ∙h K` by constructing homotopies

```text
  inv-htpy H ∙h (H ∙h K) ~ K
  H ∙h (inv H ∙h K) ~ K.
```

Similarly, we show that the operation `H ↦ H ∙h inv-htpy K` is inverse to the
operation `H ↦ H ∙h K` by constructing homotopies

```text
  (H ∙h K) ∙h inv-htpy K ~ H
  (H ∙h inv-htpy K) ∙h K ~ H.
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  is-retraction-inv-concat-htpy :
    (H : f ~ g) (K : g ~ h) → inv-htpy H ∙h (H ∙h K) ~ K
  is-retraction-inv-concat-htpy H K x = is-retraction-inv-concat (H x) (K x)

  is-section-inv-concat-htpy :
    (H : f ~ g) (L : f ~ h) → H ∙h (inv-htpy H ∙h L) ~ L
  is-section-inv-concat-htpy H L x = is-section-inv-concat (H x) (L x)

  is-retraction-inv-concat-htpy' :
    (K : g ~ h) (H : f ~ g) → (H ∙h K) ∙h inv-htpy K ~ H
  is-retraction-inv-concat-htpy' K H x = is-retraction-inv-concat' (K x) (H x)

  is-section-inv-concat-htpy' :
    (K : g ~ h) (L : f ~ h) → (L ∙h inv-htpy K) ∙h K ~ L
  is-section-inv-concat-htpy' K L x = is-section-inv-concat' (K x) (L x)
```

## Reasoning with homotopies

Homotopies can be constructed by equational reasoning in the following way:

```text
homotopy-reasoning
  f ~ g by htpy-1
    ~ h by htpy-2
    ~ i by htpy-3
```

The homotopy obtained in this way is `htpy-1 ∙h (htpy-2 ∙h htpy-3)`, i.e., it is
associated fully to the right.

```agda
infixl 1 homotopy-reasoning_
infixl 0 step-homotopy-reasoning

homotopy-reasoning_ :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2}
  (f : (x : X) → Y x) → f ~ f
homotopy-reasoning f = refl-htpy

step-homotopy-reasoning :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2}
  {f g : (x : X) → Y x} → f ~ g →
  (h : (x : X) → Y x) → g ~ h → f ~ h
step-homotopy-reasoning p h q = p ∙h q

syntax step-homotopy-reasoning p h q = p ~ h by q
```

## See also

- We postulate that homotopies characterize identifications of (dependent)
  functions in the file
  [`foundation.function-extensionality`](foundation.function-extensionality.md).
- [Multivariable homotopies](foundation.multivariable-homotopies.md).
- The [whiskering operations](foundation.whiskering-homotopies-composition.md)
  on homotopies.
