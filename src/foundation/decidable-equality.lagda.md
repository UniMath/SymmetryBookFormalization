# Decidable equality

```agda
module foundation.decidable-equality where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.equivalences
open import foundation.injective-maps
open import foundation.negation
open import foundation.sections
open import foundation.sets
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.empty-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.retracts-of-types
open import foundation-core.transport-along-identifications
```

</details>

## Definition

A type `A` is said to have
{{#concept "decidable equality" Disambiguation="type" Agda=has-decidable-equality}}
if `x ＝ y` is a [decidable type](foundation.decidable-types.md) for every
`x y : A`.

```agda
has-decidable-equality : {l : Level} → UU l → UU l
has-decidable-equality A = (x y : A) → is-decidable (x ＝ y)
```

## Examples

### Any proposition has decidable equality

```agda
abstract
  has-decidable-equality-is-prop :
    {l1 : Level} {A : UU l1} → is-prop A → has-decidable-equality A
  has-decidable-equality-is-prop H x y = inl (eq-is-prop H)
```

### The empty type has decidable equality

```agda
has-decidable-equality-empty : has-decidable-equality empty
has-decidable-equality-empty ()
```

### The unit type has decidable equality

```agda
has-decidable-equality-unit : has-decidable-equality unit
has-decidable-equality-unit star star = inl refl
```

## Properties

### Types with decidable equality are closed under injections

```agda
abstract
  has-decidable-equality-injection :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    injection A B →
    has-decidable-equality B →
    has-decidable-equality A
  has-decidable-equality-injection (f , H) d x y =
    is-decidable-iff H (ap f) (d (f x) (f y))
```

### Types with decidable equality are closed under retracts

```agda
abstract
  has-decidable-equality-retract-of :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    A retract-of B →
    has-decidable-equality B →
    has-decidable-equality A
  has-decidable-equality-retract-of (i , r , R) =
    has-decidable-equality-injection
      ( i , is-injective-has-retraction i r R)
```

### Types with decidable equality are closed under equivalences

```agda
abstract
  has-decidable-equality-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    has-decidable-equality B →
    has-decidable-equality A
  has-decidable-equality-equiv e =
    has-decidable-equality-retract-of (retract-equiv e)

abstract
  has-decidable-equality-equiv' :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    has-decidable-equality A →
    has-decidable-equality B
  has-decidable-equality-equiv' e =
    has-decidable-equality-retract-of (retract-inv-equiv e)
```

### Characterizing equality in a type with decidable equality

The identity types of a type with decidable equality are necessarily also
propositions, hence, they are either the unit or empty type.

```agda
module _
  {l : Level} {A : UU l}
  where

  Eq-has-decidable-equality' :
    (x y : A) → is-decidable (x ＝ y) → UU lzero
  Eq-has-decidable-equality' x y (inl p) = unit
  Eq-has-decidable-equality' x y (inr f) = empty

  Eq-has-decidable-equality :
    (d : has-decidable-equality A) → A → A → UU lzero
  Eq-has-decidable-equality d x y = Eq-has-decidable-equality' x y (d x y)

  is-prop-Eq-has-decidable-equality' :
    (x y : A) (t : is-decidable (x ＝ y)) →
    is-prop (Eq-has-decidable-equality' x y t)
  is-prop-Eq-has-decidable-equality' x y (inl p) = is-prop-unit
  is-prop-Eq-has-decidable-equality' x y (inr f) = is-prop-empty

  is-prop-Eq-has-decidable-equality :
    (d : has-decidable-equality A)
    {x y : A} → is-prop (Eq-has-decidable-equality d x y)
  is-prop-Eq-has-decidable-equality d {x} {y} =
    is-prop-Eq-has-decidable-equality' x y (d x y)

  refl-Eq-has-decidable-equality :
    (d : has-decidable-equality A) (x : A) →
    Eq-has-decidable-equality d x x
  refl-Eq-has-decidable-equality d x with d x x
  ... | inl α = star
  ... | inr f = f refl

  Eq-has-decidable-equality-eq :
    (d : has-decidable-equality A) {x y : A} →
    x ＝ y → Eq-has-decidable-equality d x y
  Eq-has-decidable-equality-eq d {x} {.x} refl =
    refl-Eq-has-decidable-equality d x

  eq-Eq-has-decidable-equality' :
    (x y : A) (t : is-decidable (x ＝ y)) →
    Eq-has-decidable-equality' x y t → x ＝ y
  eq-Eq-has-decidable-equality' x y (inl p) t = p
  eq-Eq-has-decidable-equality' x y (inr f) t = ex-falso t

  eq-Eq-has-decidable-equality :
    (d : has-decidable-equality A) {x y : A} →
    Eq-has-decidable-equality d x y → x ＝ y
  eq-Eq-has-decidable-equality d {x} {y} =
    eq-Eq-has-decidable-equality' x y (d x y)
```

### Types with decidable equality are sets

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-set-has-decidable-equality : has-decidable-equality A → is-set A
    is-set-has-decidable-equality d =
      is-set-prop-in-id
        ( λ x y → Eq-has-decidable-equality d x y)
        ( λ x y → is-prop-Eq-has-decidable-equality d)
        ( λ x → refl-Eq-has-decidable-equality d x)
        ( λ x y → eq-Eq-has-decidable-equality d)
```

### Having decidable equality is a property

```agda
abstract
  is-prop-has-decidable-equality :
    {l1 : Level} {X : UU l1} → is-prop (has-decidable-equality X)
  is-prop-has-decidable-equality {l1} {X} =
    is-prop-has-element
      ( λ d →
        is-prop-Π
        ( λ x →
          is-prop-Π
          ( λ y →
            is-prop-coproduct
            ( intro-double-negation)
            ( is-set-has-decidable-equality d x y)
            ( is-prop-neg))))

has-decidable-equality-Prop :
  {l1 : Level} (X : UU l1) → Prop l1
pr1 (has-decidable-equality-Prop X) = has-decidable-equality X
pr2 (has-decidable-equality-Prop X) = is-prop-has-decidable-equality
```

### A product of types with decidable equality has decidable equality

```agda
has-decidable-equality-product' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (f : B → has-decidable-equality A) (g : A → has-decidable-equality B) →
  has-decidable-equality (A × B)
has-decidable-equality-product' f g (x , y) (x' , y') with
  f y x x' | g x y y'
... | inl refl | inl refl = inl refl
... | inl refl | inr nq = inr (λ r → nq (ap pr2 r))
... | inr np | inl refl = inr (λ r → np (ap pr1 r))
... | inr np | inr nq = inr (λ r → np (ap pr1 r))

has-decidable-equality-product :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality A → has-decidable-equality B →
  has-decidable-equality (A × B)
has-decidable-equality-product d e =
  has-decidable-equality-product' (λ _ → d) (λ _ → e)
```

### Decidability of equality of the factors of a cartesian product

If `A × B` has decidable equality and `B` has an element, then `A` has decidable
equality; and vice versa.

```agda
has-decidable-equality-left-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality (A × B) → B → has-decidable-equality A
has-decidable-equality-left-factor d b x y with d (x , b) (y , b)
... | inl p = inl (ap pr1 p)
... | inr np = inr (λ q → np (ap (λ z → z , b) q))

has-decidable-equality-right-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-equality (A × B) → A → has-decidable-equality B
has-decidable-equality-right-factor d a x y with d (a , x) (a , y)
... | inl p = inl (ap pr2 p)
... | inr np = inr (λ q → np (eq-pair-eq-fiber q))
```

### Types with decidable equality are closed under dependent pair types

```agda
abstract
  has-decidable-equality-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    has-decidable-equality A → ((x : A) → has-decidable-equality (B x)) →
    has-decidable-equality (Σ A B)
  has-decidable-equality-Σ {B = B} dA dB (x , y) (x' , y') with dA x x'
  ... | inr np = inr (λ r → np (ap pr1 r))
  ... | inl p =
    is-decidable-iff eq-pair-Σ' pair-eq-Σ
      ( is-decidable-equiv
        ( left-unit-law-Σ-is-contr
          ( is-proof-irrelevant-is-prop
            ( is-set-has-decidable-equality dA x x') p)
          ( p))
        ( dB x' (tr _ p y) y'))
```

### A family of types over a type with decidable equality and decidable total space is a family of types with decidable equality

```agda
abstract
  has-decidable-equality-fiber-has-decidable-equality-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    has-decidable-equality A → has-decidable-equality (Σ A B) →
    (x : A) → has-decidable-equality (B x)
  has-decidable-equality-fiber-has-decidable-equality-Σ {B = B} dA dΣ x =
    has-decidable-equality-equiv'
      ( equiv-fiber-pr1 B x)
      ( has-decidable-equality-Σ dΣ
        ( λ t →
          has-decidable-equality-is-prop
            ( is-set-has-decidable-equality dA (pr1 t) x)))
```

### If `B` is a family of types with decidable equality, the total space has decidable equality, and `B` has a section, then the base type has decidable equality

```agda
abstract
  has-decidable-equality-base-has-decidable-equality-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
    has-decidable-equality (Σ A B) → ((x : A) → has-decidable-equality (B x)) →
    has-decidable-equality A
  has-decidable-equality-base-has-decidable-equality-Σ b dΣ dB =
    has-decidable-equality-equiv'
      ( equiv-total-fiber (map-section-family b))
      ( has-decidable-equality-Σ dΣ
        ( λ t →
          has-decidable-equality-is-prop
            ( is-prop-map-is-injective
              ( is-set-has-decidable-equality dΣ)
              ( is-injective-map-section-family b)
              ( t))))
```

### If `A` and `B` have decidable equality, then so does their coproduct

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  has-decidable-equality-coproduct :
    has-decidable-equality A → has-decidable-equality B →
    has-decidable-equality (A + B)
  has-decidable-equality-coproduct d e (inl x) (inl y) =
    is-decidable-iff (ap inl) is-injective-inl (d x y)
  has-decidable-equality-coproduct d e (inl x) (inr y) =
    inr neq-inl-inr
  has-decidable-equality-coproduct d e (inr x) (inl y) =
    inr neq-inr-inl
  has-decidable-equality-coproduct d e (inr x) (inr y) =
    is-decidable-iff (ap inr) is-injective-inr (e x y)

  has-decidable-equality-left-summand :
    has-decidable-equality (A + B) → has-decidable-equality A
  has-decidable-equality-left-summand d x y =
    is-decidable-iff is-injective-inl (ap inl) (d (inl x) (inl y))

  has-decidable-equality-right-summand :
    has-decidable-equality (A + B) → has-decidable-equality B
  has-decidable-equality-right-summand d x y =
    is-decidable-iff is-injective-inr (ap inr) (d (inr x) (inr y))
```

## See also

- An element `x` is [isolated](foundation.isolated-elements.md) if `A` has
  decidable equality locally at `x`.

## External links

- [decidable equality](https://ncatlab.org/nlab/show/decidable+equality) at
  $n$Lab
