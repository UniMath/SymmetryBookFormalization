# Countable sets

```agda
module set-theory.countable-sets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.type-arithmetic-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-coproduct-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.maybe
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.retracts-of-types
open import foundation.sets
open import foundation.shifting-sequences
open import foundation.surjective-maps
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A [set](foundation-core.sets.md) `X` is said to be
{{#concept "countable" Disambiguation="set" Agda=is-countable WD="countable set" WDID=Q66707394}}
if there is a [surjective map](foundation.surjective-maps.md) `f : ℕ → X + 1`.
Equivalently, a set `X` is countable if there is a surjective map `f : P → X`
for some [decidable subset](foundation.decidable-subtypes.md) `P` of `X`.

## Definition

### First definition of countable sets

```agda
module _
  {l : Level} (X : Set l)
  where

  enumeration : UU l
  enumeration = Σ (ℕ → Maybe (type-Set X)) is-surjective

  map-enumeration : enumeration → (ℕ → Maybe (type-Set X))
  map-enumeration E = pr1 E

  is-surjective-map-enumeration :
    (E : enumeration) → is-surjective (map-enumeration E)
  is-surjective-map-enumeration E = pr2 E

  is-countable-Prop : Prop l
  is-countable-Prop =
    ∃ (ℕ → Maybe (type-Set X)) (is-surjective-Prop)

  is-countable : UU l
  is-countable = type-Prop (is-countable-Prop)

  is-prop-is-countable : is-prop is-countable
  is-prop-is-countable = is-prop-type-Prop is-countable-Prop
```

### Second definition of countable sets

```agda
module _
  {l : Level} (X : Set l)
  where

  decidable-subprojection-ℕ : UU (lsuc l ⊔ l)
  decidable-subprojection-ℕ =
    Σ ( decidable-subtype l ℕ)
      ( λ P → type-decidable-subtype P ↠ type-Set X)

  is-countable-Prop' : Prop (lsuc l ⊔ l)
  is-countable-Prop' =
    exists-structure-Prop
      ( decidable-subtype l ℕ)
      ( λ P → type-decidable-subtype P ↠ type-Set X)

  is-countable' : UU (lsuc l ⊔ l)
  is-countable' = type-Prop is-countable-Prop'

  is-prop-is-countable' : is-prop is-countable'
  is-prop-is-countable' = is-prop-type-Prop is-countable-Prop'
```

### Third definition of countable sets

If a set `X` is inhabited, then it is countable if and only if there is a
surjective map `f : ℕ → X`. Let us call the latter as "directly countable".

```agda
is-directly-countable-Prop : {l : Level} → Set l → Prop l
is-directly-countable-Prop X =
  ∃ (ℕ → type-Set X) (is-surjective-Prop)

is-directly-countable : {l : Level} → Set l → UU l
is-directly-countable X = type-Prop (is-directly-countable-Prop X)

is-prop-is-directly-countable :
  {l : Level} (X : Set l) → is-prop (is-directly-countable X)
is-prop-is-directly-countable X = is-prop-type-Prop
  (is-directly-countable-Prop X)

module _
  {l : Level} (X : Set l) (a : type-Set X)
  where

  is-directly-countable-is-countable :
    is-countable X → is-directly-countable X
  is-directly-countable-is-countable H =
    apply-universal-property-trunc-Prop H
      ( is-directly-countable-Prop X)
      ( λ P →
        unit-trunc-Prop
          ( pair
            ( f ∘ (pr1 P))
            ( is-surjective-comp is-surjective-f (pr2 P))))
    where
    f : Maybe (type-Set X) → type-Set X
    f (inl x) = x
    f (inr star) = a

    is-surjective-f : is-surjective f
    is-surjective-f x = unit-trunc-Prop (pair (inl x) refl)

  abstract
    is-countable-is-directly-countable :
      is-directly-countable X → is-countable X
    is-countable-is-directly-countable H =
      apply-universal-property-trunc-Prop H
        ( is-countable-Prop X)
        ( λ P →
          unit-trunc-Prop
            ( ( λ where
                zero-ℕ → inr star
                (succ-ℕ n) → inl ((shift-ℕ a (pr1 P)) n)) ,
              ( λ where
                ( inl x) →
                  apply-universal-property-trunc-Prop (pr2 P x)
                    ( trunc-Prop (fiber _ (inl x)))
                    ( λ (n , p) →
                      unit-trunc-Prop
                        ( succ-ℕ (succ-ℕ n) , ap inl p))
                ( inr star) → unit-trunc-Prop (zero-ℕ , refl))))
```

## Properties

### The two definitions of countability are equivalent

First, we will prove `is-countable X → is-countable' X`.

```agda
module _
  {l : Level} (X : Set l)
  where

  decidable-subprojection-ℕ-enumeration :
    enumeration X → decidable-subprojection-ℕ X
  pr1 (pr1 (decidable-subprojection-ℕ-enumeration (f , H)) n) =
    f n ≠ inr star
  pr1 (pr2 (pr1 (decidable-subprojection-ℕ-enumeration (f , H)) n)) =
    is-prop-neg
  pr2 (pr2 (pr1 (decidable-subprojection-ℕ-enumeration (f , H)) n)) =
    is-decidable-is-not-exception-Maybe (f n)
  pr1 (pr2 (decidable-subprojection-ℕ-enumeration (f , H))) (n , p) =
    value-is-not-exception-Maybe (f n) p
  pr2 (pr2 (decidable-subprojection-ℕ-enumeration (f , H))) x =
    apply-universal-property-trunc-Prop (H (inl x))
      ( trunc-Prop (fiber _ x))
      ( λ (n , p) →
        unit-trunc-Prop
          ( ( n , is-not-exception-is-value-Maybe (f n) (x , inv p)) ,
            ( is-injective-inl
              ( ( eq-is-not-exception-Maybe
                ( f n)
                ( is-not-exception-is-value-Maybe
                  ( f n) (x , inv p))) ∙
              ( p)))))

  is-countable'-is-countable :
    is-countable X → is-countable' X
  is-countable'-is-countable H =
    apply-universal-property-trunc-Prop H
      ( is-countable-Prop' X)
      ( λ E → unit-trunc-Prop (decidable-subprojection-ℕ-enumeration E))
```

Second, we will prove `is-countable' X → is-countable X`.

```agda
cases-map-decidable-subtype-ℕ :
  {l : Level} (X : Set l) →
  ( P : decidable-subtype l ℕ) →
  ( f : type-decidable-subtype P → type-Set X) →
  ( (n : ℕ) → is-decidable (pr1 (P n)) -> Maybe (type-Set X))
cases-map-decidable-subtype-ℕ X P f n (inl x) = inl (f (n , x))
cases-map-decidable-subtype-ℕ X P f n (inr x) = inr star

module _
  {l : Level} (X : Set l)
  ( P : decidable-subtype l ℕ)
  ( f : type-decidable-subtype P → type-Set X)
  where

  shift-decidable-subtype-ℕ : decidable-subtype l ℕ
  shift-decidable-subtype-ℕ zero-ℕ =
    ( raise-empty l) ,
    ( is-prop-raise-empty ,
      ( inr (is-empty-raise-empty)))
  shift-decidable-subtype-ℕ (succ-ℕ n) = P n

  map-shift-decidable-subtype-ℕ :
    type-decidable-subtype shift-decidable-subtype-ℕ → type-Set X
  map-shift-decidable-subtype-ℕ (zero-ℕ , map-raise ())
  map-shift-decidable-subtype-ℕ (succ-ℕ n , p) = f (n , p)

  map-enumeration-decidable-subprojection-ℕ : ℕ → Maybe (type-Set X)
  map-enumeration-decidable-subprojection-ℕ n =
    cases-map-decidable-subtype-ℕ
      ( X)
      ( shift-decidable-subtype-ℕ)
      ( map-shift-decidable-subtype-ℕ)
      ( n)
      (pr2 (pr2 (shift-decidable-subtype-ℕ n)))

  abstract
    is-surjective-map-enumeration-decidable-subprojection-ℕ :
      ( is-surjective f) →
      ( is-surjective map-enumeration-decidable-subprojection-ℕ)
    is-surjective-map-enumeration-decidable-subprojection-ℕ H (inl x) =
      ( apply-universal-property-trunc-Prop (H x)
        ( trunc-Prop (fiber map-enumeration-decidable-subprojection-ℕ (inl x)))
        ( λ where
          ( ( n , s) , refl) →
            unit-trunc-Prop
              ( ( succ-ℕ n) ,
                ( ap
                  ( cases-map-decidable-subtype-ℕ X
                    ( shift-decidable-subtype-ℕ)
                    ( map-shift-decidable-subtype-ℕ)
                    (succ-ℕ n))
                  ( pr1
                    ( is-prop-is-decidable (pr1 (pr2 (P n)))
                      ( pr2 (pr2 (P n)))
                      ( inl s)))))))
    is-surjective-map-enumeration-decidable-subprojection-ℕ H (inr star) =
      ( unit-trunc-Prop (0 , refl))

module _
  {l : Level} (X : Set l)
  where

  enumeration-decidable-subprojection-ℕ :
    decidable-subprojection-ℕ X → enumeration X
  enumeration-decidable-subprojection-ℕ (P , (f , H)) =
    ( map-enumeration-decidable-subprojection-ℕ X P f) ,
    ( is-surjective-map-enumeration-decidable-subprojection-ℕ X P f H)

  is-countable-is-countable' :
    is-countable' X → is-countable X
  is-countable-is-countable' H =
    apply-universal-property-trunc-Prop H
      ( is-countable-Prop X)
      ( λ D →
        ( unit-trunc-Prop (enumeration-decidable-subprojection-ℕ D)))
```

### If a countable set surjects onto a set, then the set is countable

```agda
module _
  {l1 l2 : Level} (A : Set l1) (B : Set l2)
  where

  is-directly-countable-is-directly-countably-indexed' :
    {f : type-Set A → type-Set B} → is-surjective f →
    is-directly-countable A → is-directly-countable B
  is-directly-countable-is-directly-countably-indexed' {f} F =
    elim-exists
      ( is-directly-countable-Prop B)
      ( λ g G → intro-exists (f ∘ g) (is-surjective-comp F G))

  is-directly-countable-is-directly-countably-indexed :
    (type-Set A ↠ type-Set B) →
    is-directly-countable A →
    is-directly-countable B
  is-directly-countable-is-directly-countably-indexed (f , F) =
    is-directly-countable-is-directly-countably-indexed' F

  is-countable-is-countably-indexed' :
    {f : type-Set A → type-Set B} →
    is-surjective f →
    is-countable A →
    is-countable B
  is-countable-is-countably-indexed' {f} F =
    elim-exists
      ( is-countable-Prop B)
      ( λ g G →
        intro-exists
          ( map-Maybe f ∘ g)
          ( is-surjective-comp (is-surjective-map-is-surjective-Maybe F) G))

  is-countable-is-countably-indexed :
    (type-Set A ↠ type-Set B) →
    is-countable A →
    is-countable B
  is-countable-is-countably-indexed (f , F) =
    is-countable-is-countably-indexed' F
```

### Retracts of countable sets are countable

```agda
module _
  {l1 l2 : Level} (A : Set l1) (B : Set l2)
  (R : (type-Set B) retract-of (type-Set A))
  where

  is-directly-countable-retract-of :
    is-directly-countable A → is-directly-countable B
  is-directly-countable-retract-of =
    is-directly-countable-is-directly-countably-indexed' A B
      { map-retraction-retract R}
      ( is-surjective-has-section
        ( inclusion-retract R , is-retraction-map-retraction-retract R))

  is-countable-retract-of :
    is-countable A → is-countable B
  is-countable-retract-of =
    is-countable-is-countably-indexed' A B
      { map-retraction-retract R}
      ( is-surjective-has-section
        ( inclusion-retract R , is-retraction-map-retraction-retract R))
```

### Countable sets are closed under equivalences

```agda
module _
  {l1 l2 : Level} (A : Set l1) (B : Set l2) (e : type-Set B ≃ type-Set A)
  where

  is-directly-countable-equiv :
    is-directly-countable A → is-directly-countable B
  is-directly-countable-equiv =
    is-directly-countable-retract-of A B (retract-equiv e)

  is-countable-equiv :
    is-countable A → is-countable B
  is-countable-equiv =
    is-countable-retract-of A B (retract-equiv e)
```

### The set of natural numbers ℕ is itself countable

```agda
abstract
  is-countable-ℕ : is-countable ℕ-Set
  is-countable-ℕ =
    unit-trunc-Prop
      ( ( λ where
          zero-ℕ → inr star
          (succ-ℕ n) → inl n) ,
        ( λ where
          ( inl n) → unit-trunc-Prop (succ-ℕ n , refl)
          ( inr star) → unit-trunc-Prop (zero-ℕ , refl)))
```

### The empty set is countable

```agda
is-countable-empty : is-countable empty-Set
is-countable-empty =
  is-countable-is-countable'
    ( empty-Set)
    ( unit-trunc-Prop ((λ _ → empty-Decidable-Prop) , (λ ()) , (λ ())))
```

### The unit set is countable

```agda
abstract
  is-countable-unit : is-countable unit-Set
  is-countable-unit =
    unit-trunc-Prop
      ( ( λ where
          zero-ℕ → inl star
          (succ-ℕ x) → inr star) ,
        ( λ where
          ( inl star) → unit-trunc-Prop (0 , refl)
          ( inr star) → unit-trunc-Prop (1 , refl)))
```

### If `X` and `Y` are countable sets, then so is their coproduct `X + Y`

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  is-countable-coproduct :
    is-countable X → is-countable Y → is-countable (coproduct-Set X Y)
  is-countable-coproduct H H' =
    apply-twice-universal-property-trunc-Prop H' H
      ( is-countable-Prop (coproduct-Set X Y))
      ( λ h' h →
        ( unit-trunc-Prop
          ( pair
            ( map-maybe-coproduct ∘
              ( map-coproduct (pr1 h) (pr1 h') ∘ map-ℕ-to-ℕ+ℕ))
            ( is-surjective-comp
              ( is-surjective-map-maybe-coproduct)
              ( is-surjective-comp
                ( is-surjective-map-coproduct (pr2 h) (pr2 h'))
                ( is-surjective-is-equiv (is-equiv-map-ℕ-to-ℕ+ℕ)))))))
```

### If `X` and `Y` are countable sets, then so is their coproduct `X × Y`

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  is-countable-product :
    is-countable X → is-countable Y → is-countable (product-Set X Y)
  is-countable-product H H' =
    apply-twice-universal-property-trunc-Prop H' H
      ( is-countable-Prop (product-Set X Y))
      ( λ h' h →
        ( unit-trunc-Prop
          ( pair
            ( map-maybe-product ∘
              ( map-product (pr1 h) (pr1 h') ∘ map-inv-pairing-equiv-ℕ))
            ( is-surjective-comp
              ( is-surjective-map-maybe-product)
              ( is-surjective-comp
                ( is-surjective-map-product (pr2 h) (pr2 h'))
                ( is-surjective-is-equiv (is-equiv-map-inv-pairing-equiv-ℕ)))))))
```

In particular, the sets ℕ + ℕ, ℕ × ℕ, and ℤ are countable.

```agda
is-countable-ℕ+ℕ : is-countable (coproduct-Set ℕ-Set ℕ-Set)
is-countable-ℕ+ℕ =
  is-countable-coproduct ℕ-Set ℕ-Set is-countable-ℕ is-countable-ℕ

is-countable-ℕ×ℕ : is-countable (product-Set ℕ-Set ℕ-Set)
is-countable-ℕ×ℕ =
  is-countable-product ℕ-Set ℕ-Set is-countable-ℕ is-countable-ℕ

is-countable-ℤ : is-countable (ℤ-Set)
is-countable-ℤ =
  is-countable-coproduct (ℕ-Set) (coproduct-Set unit-Set ℕ-Set)
    ( is-countable-ℕ)
    ( is-countable-coproduct (unit-Set) (ℕ-Set)
      ( is-countable-unit) (is-countable-ℕ))
```

### All standard finite sets are countable

```agda
is-countable-Fin-Set : (n : ℕ) → is-countable (Fin-Set n)
is-countable-Fin-Set zero-ℕ = is-countable-empty
is-countable-Fin-Set (succ-ℕ n) =
  is-countable-coproduct (Fin-Set n) (unit-Set)
    ( is-countable-Fin-Set n) (is-countable-unit)
```

## See also

- [Infinite sets](set-theory.infinite-sets.md)
- [Uncountable sets](set-theory.uncountable-sets.md)

## External links

- [countable set](https://ncatlab.org/nlab/show/countable+set) at $n$Lab
- [Countable set](https://en.wikipedia.org/wiki/Countable_set) at Wikipedia
