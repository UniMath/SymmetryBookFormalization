# Double negation stable equality

```agda
module foundation-core.double-negation-stable-equality where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.injective-maps
open import foundation.irrefutable-equality
open import foundation.negation
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.empty-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.retracts-of-types

open import logic.double-negation-elimination
```

</details>

## Idea

A type `A` is said to have
{{#concept "double negation stable equality" Disambiguation="type" Agda=has-double-negation-stable-equality}}
if `x ＝ y` has
[double negation elimination](logic.double-negation-elimination.md) for every
`x y : A`. By the
[fundamental theorem of identity types](foundation.fundamental-theorem-of-identity-types.md),
types with double negation stable equality are [sets](foundation-core.sets.md).

## Definitions

```agda
has-based-double-negation-stable-equality : {l : Level} (A : UU l) → A → UU l
has-based-double-negation-stable-equality A x =
  (y : A) → has-double-negation-elim (x ＝ y)

has-based-double-negation-stable-equality' : {l : Level} (A : UU l) → A → UU l
has-based-double-negation-stable-equality' A x =
  (y : A) → has-double-negation-elim (y ＝ x)

has-double-negation-stable-equality : {l : Level} → UU l → UU l
has-double-negation-stable-equality A =
  (x : A) → has-based-double-negation-stable-equality A x
```

## Examples

### Propositions have double negation stable equality

```agda
abstract
  has-double-negation-stable-equality-is-prop :
    {l1 : Level} {A : UU l1} → is-prop A → has-double-negation-stable-equality A
  has-double-negation-stable-equality-is-prop H x y =
    double-negation-elim-is-contr (H x y)
```

### The empty type has double negation stable equality

```agda
has-double-negation-stable-equality-empty :
  has-double-negation-stable-equality empty
has-double-negation-stable-equality-empty ()
```

### The unit type has double negation stable equality

```agda
has-double-negation-stable-equality-unit :
  has-double-negation-stable-equality unit
has-double-negation-stable-equality-unit _ _ _ = refl
```

## Properties

### Types with double negation stable equality are sets

```agda
module _
  {l : Level} {A : UU l}
  where

  is-prop-based-Id-has-based-double-negation-stable-equality :
    {x : A} →
    has-based-double-negation-stable-equality A x → (y : A) → is-prop (x ＝ y)
  is-prop-based-Id-has-based-double-negation-stable-equality {x} =
    is-prop-based-Id-prop-in-based-id x
      ( λ y → ¬¬ (x ＝ y))
      ( λ y → is-prop-neg)
      ( intro-double-negation refl)

  is-set-has-double-negation-stable-equality :
    has-double-negation-stable-equality A → is-set A
  is-set-has-double-negation-stable-equality H x =
    is-prop-based-Id-has-based-double-negation-stable-equality (H x)
```

### Types with double negation stable equality are closed under injections

```agda
abstract
  has-double-negation-stable-equality-injection :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    injection A B →
    has-double-negation-stable-equality B →
    has-double-negation-stable-equality A
  has-double-negation-stable-equality-injection (f , H) d x y =
    has-double-negation-elim-iff (ap f , H) (d (f x) (f y))
```

### Types with double negation stable equality are closed under retracts

```agda
abstract
  has-double-negation-stable-equality-retract-of :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    A retract-of B →
    has-double-negation-stable-equality B →
    has-double-negation-stable-equality A
  has-double-negation-stable-equality-retract-of (i , r , R) =
    has-double-negation-stable-equality-injection
      ( i , is-injective-has-retraction i r R)
```

### Types with double negation stable equality are closed under equivalences

```agda
abstract
  has-double-negation-stable-equality-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    has-double-negation-stable-equality B →
    has-double-negation-stable-equality A
  has-double-negation-stable-equality-equiv e =
    has-double-negation-stable-equality-retract-of (retract-equiv e)

abstract
  has-double-negation-stable-equality-equiv' :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    has-double-negation-stable-equality A →
    has-double-negation-stable-equality B
  has-double-negation-stable-equality-equiv' e =
    has-double-negation-stable-equality-retract-of (retract-inv-equiv e)
```

### Having double negation stable equality is a property

```agda
abstract
  is-prop-has-based-double-negation-stable-equality :
    {l1 : Level} {X : UU l1} (x : X) →
    is-prop (has-based-double-negation-stable-equality X x)
  is-prop-has-based-double-negation-stable-equality x =
    is-prop-has-element
      ( λ d →
        is-prop-Π
        ( λ y →
          is-prop-function-type
            ( is-prop-based-Id-has-based-double-negation-stable-equality d y)))

abstract
  is-prop-has-double-negation-stable-equality :
    {l1 : Level} {X : UU l1} → is-prop (has-double-negation-stable-equality X)
  is-prop-has-double-negation-stable-equality =
    is-prop-Π is-prop-has-based-double-negation-stable-equality

has-double-negation-stable-equality-Prop : {l1 : Level} → UU l1 → Prop l1
has-double-negation-stable-equality-Prop X =
  ( has-double-negation-stable-equality X ,
    is-prop-has-double-negation-stable-equality)
```

### Any map into a type with double negation stable equality reflects irrefutable equality

```agda
module _
  {l1 l2 : Level} {A : UU l1} {X : UU l2}
  (H : has-double-negation-stable-equality X) (f : A → X)
  where

  reflects-irrefutable-eq :
    reflects-equivalence-relation (irrefutable-eq-equivalence-relation A) f
  reflects-irrefutable-eq {x} {y} r =
    H (f x) (f y) (map-double-negation (ap f) r)

  reflecting-map-irrefutable-eq :
    reflecting-map-equivalence-relation
      ( irrefutable-eq-equivalence-relation A)
      ( X)
  reflecting-map-irrefutable-eq = (f , reflects-irrefutable-eq)
```

### A product of types with double negation stable equality has double negation stable equality

```agda
has-double-negation-stable-equality-product :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-double-negation-stable-equality A →
  has-double-negation-stable-equality B →
  has-double-negation-stable-equality (A × B)
has-double-negation-stable-equality-product d e x y p =
  eq-pair
    ( d (pr1 x) (pr1 y) (map-double-negation (ap pr1) p))
    ( e (pr2 x) (pr2 y) (map-double-negation (ap pr2) p))
```

### Double negation stability of equality of the factors of a cartesian product

If `A × B` has double negation stable equality and `B` has an element, then `A`
has double negation stable equality; and vice versa.

```agda
has-double-negation-stable-equality-left-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-double-negation-stable-equality (A × B) →
  B →
  has-double-negation-stable-equality A
has-double-negation-stable-equality-left-factor d b x y p =
  ap pr1 (d (x , b) (y , b) (map-double-negation (λ q → eq-pair q refl) p))

has-double-negation-stable-equality-right-factor :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-double-negation-stable-equality (A × B) →
  A → has-double-negation-stable-equality B
has-double-negation-stable-equality-right-factor d a x y p =
  ap pr2 (d (a , x) (a , y) (map-double-negation (eq-pair refl) p))
```

### If the total space has double negation stable equality, and `B` has a section, then the base type has double negation stable equality

```agda
abstract
  has-double-negation-stable-equality-base-has-double-negation-stable-equality-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
    has-double-negation-stable-equality (Σ A B) →
    has-double-negation-stable-equality A
  has-double-negation-stable-equality-base-has-double-negation-stable-equality-Σ
    b dΣ x y nnp =
    ap
      ( pr1)
      ( dΣ
        ( x , b x)
        ( y , b y)
        ( map-double-negation (λ p → eq-pair-Σ p (apd b p)) nnp))
```

### If `A` and `B` have double negation stable equality, then so does their coproduct

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  has-double-negation-stable-equality-coproduct :
    has-double-negation-stable-equality A →
    has-double-negation-stable-equality B →
    has-double-negation-stable-equality (A + B)
  has-double-negation-stable-equality-coproduct dA dB (inl x) (inl y) =
    has-double-negation-elim-iff (is-injective-inl , ap inl) (dA x y)
  has-double-negation-stable-equality-coproduct dA dB (inl x) (inr y) p =
    ex-falso (p neq-inl-inr)
  has-double-negation-stable-equality-coproduct dA dB (inr x) (inl y) p =
    ex-falso (p neq-inr-inl)
  has-double-negation-stable-equality-coproduct dA dB (inr x) (inr y) =
    has-double-negation-elim-iff (is-injective-inr , ap inr) (dB x y)

  has-double-negation-stable-equality-left-summand :
    has-double-negation-stable-equality (A + B) →
    has-double-negation-stable-equality A
  has-double-negation-stable-equality-left-summand d x y =
    has-double-negation-elim-iff (ap inl , is-injective-inl) (d (inl x) (inl y))

  has-double-negation-stable-equality-right-summand :
    has-double-negation-stable-equality (A + B) →
    has-double-negation-stable-equality B
  has-double-negation-stable-equality-right-summand d x y =
    has-double-negation-elim-iff (ap inr , is-injective-inr) (d (inr x) (inr y))
```

## See also

- Every type with a
  [tight apartness relation](foundation.tight-apartness-relations.md) has double
  negation stable equality. Conversely, every type with double negation stable
  equality has a tight, symmetric, antireflexive relation. However, this
  relation need not be cotransitive.

## External links

- [double negation stable equality](https://ncatlab.org/nlab/show/decidable+equality)
  at $n$Lab
