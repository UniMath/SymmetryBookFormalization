# Decidable propositions

```agda
module foundation.decidable-propositions where

open import foundation-core.decidable-propositions public
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retracts-of-types
open import foundation-core.sets
open import foundation-core.small-types
open import foundation-core.subtypes
open import foundation-core.transport-along-identifications

open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-types
```

</details>

## Idea

A **decidable proposition** is a [proposition](foundation-core.propositions.md)
that has a [decidable](foundation.decidable-types.md) underlying type.

## Properties

### The forgetful map from decidable propositions to propositions is an embedding

```agda
is-emb-prop-Decidable-Prop : {l : Level} → is-emb (prop-Decidable-Prop {l})
is-emb-prop-Decidable-Prop =
  is-emb-tot
    ( λ X →
      is-emb-inclusion-subtype
        ( λ H → pair (is-decidable X) (is-prop-is-decidable H)))

emb-prop-Decidable-Prop : {l : Level} → Decidable-Prop l ↪ Prop l
pr1 emb-prop-Decidable-Prop = prop-Decidable-Prop
pr2 emb-prop-Decidable-Prop = is-emb-prop-Decidable-Prop
```

### The type of decidable propositions in universe level `l` is equivalent to the type of booleans

```agda
module _
  {l : Level}
  where

  split-Decidable-Prop :
    Decidable-Prop l ≃
    ((Σ (Prop l) type-Prop) + (Σ (Prop l) (λ Q → ¬ (type-Prop Q))))
  split-Decidable-Prop =
    ( left-distributive-Σ-coproduct (Prop l) (λ Q → pr1 Q) (λ Q → ¬ (pr1 Q))) ∘e
    ( inv-associative-Σ (UU l) is-prop (λ X → is-decidable (pr1 X)))

  map-equiv-bool-Decidable-Prop' :
    (Σ (Prop l) type-Prop) + (Σ (Prop l) (λ Q → ¬ (type-Prop Q))) →
    bool
  map-equiv-bool-Decidable-Prop' (inl x) = true
  map-equiv-bool-Decidable-Prop' (inr x) = false

  map-inv-equiv-bool-Decidable-Prop' :
    bool →
    (Σ (Prop l) type-Prop) + (Σ (Prop l) (λ Q → ¬ (type-Prop Q)))
  map-inv-equiv-bool-Decidable-Prop' true =
    inl (pair (raise-unit-Prop l) raise-star)
  map-inv-equiv-bool-Decidable-Prop' false =
    inr (pair (raise-empty-Prop l) is-empty-raise-empty)

  is-section-map-inv-equiv-bool-Decidable-Prop' :
    (map-equiv-bool-Decidable-Prop' ∘ map-inv-equiv-bool-Decidable-Prop') ~ id
  is-section-map-inv-equiv-bool-Decidable-Prop' true = refl
  is-section-map-inv-equiv-bool-Decidable-Prop' false = refl

  is-retraction-map-inv-equiv-bool-Decidable-Prop' :
    (map-inv-equiv-bool-Decidable-Prop' ∘ map-equiv-bool-Decidable-Prop') ~ id
  is-retraction-map-inv-equiv-bool-Decidable-Prop' (inl x) =
    ap inl (eq-is-contr is-torsorial-true-Prop)
  is-retraction-map-inv-equiv-bool-Decidable-Prop' (inr x) =
    ap inr (eq-is-contr is-torsorial-false-Prop)

  is-equiv-map-equiv-bool-Decidable-Prop' :
    is-equiv map-equiv-bool-Decidable-Prop'
  is-equiv-map-equiv-bool-Decidable-Prop' =
    is-equiv-is-invertible
      map-inv-equiv-bool-Decidable-Prop'
      is-section-map-inv-equiv-bool-Decidable-Prop'
      is-retraction-map-inv-equiv-bool-Decidable-Prop'

  equiv-bool-Decidable-Prop' :
    ((Σ (Prop l) type-Prop) + (Σ (Prop l) (λ Q → ¬ (type-Prop Q)))) ≃ bool
  pr1 equiv-bool-Decidable-Prop' = map-equiv-bool-Decidable-Prop'
  pr2 equiv-bool-Decidable-Prop' = is-equiv-map-equiv-bool-Decidable-Prop'

  equiv-bool-Decidable-Prop : Decidable-Prop l ≃ bool
  equiv-bool-Decidable-Prop = equiv-bool-Decidable-Prop' ∘e split-Decidable-Prop

  abstract
    compute-equiv-bool-Decidable-Prop :
      (P : Decidable-Prop l) →
      type-Decidable-Prop P ≃ (map-equiv equiv-bool-Decidable-Prop P ＝ true)
    compute-equiv-bool-Decidable-Prop (pair P (pair H (inl p))) =
      equiv-is-contr
        ( is-proof-irrelevant-is-prop H p)
        ( is-proof-irrelevant-is-prop (is-set-bool true true) refl)
    compute-equiv-bool-Decidable-Prop (pair P (pair H (inr np))) =
      equiv-is-empty np neq-false-true-bool
```

### Types of decidable propositions of any universe level are equivalent

```agda
equiv-universes-Decidable-Prop :
  (l l' : Level) → Decidable-Prop l ≃ Decidable-Prop l'
equiv-universes-Decidable-Prop l l' =
  inv-equiv equiv-bool-Decidable-Prop ∘e equiv-bool-Decidable-Prop

iff-universes-Decidable-Prop :
  (l l' : Level) (P : Decidable-Prop l) →
  ( type-Decidable-Prop P) ↔
  ( type-Decidable-Prop (map-equiv (equiv-universes-Decidable-Prop l l') P))
pr1 (iff-universes-Decidable-Prop l l' P) p =
  map-inv-equiv
    ( compute-equiv-bool-Decidable-Prop
      ( map-equiv (equiv-universes-Decidable-Prop l l') P))
    ( tr
      ( λ e → map-equiv e (map-equiv equiv-bool-Decidable-Prop P) ＝ true)
      ( inv (right-inverse-law-equiv equiv-bool-Decidable-Prop))
      ( map-equiv (compute-equiv-bool-Decidable-Prop P) p))
pr2 (iff-universes-Decidable-Prop l l' P) p =
  map-inv-equiv
    ( compute-equiv-bool-Decidable-Prop P)
    ( tr
      ( λ e → map-equiv e (map-equiv equiv-bool-Decidable-Prop P) ＝ true)
      ( right-inverse-law-equiv equiv-bool-Decidable-Prop)
      ( map-equiv
        ( compute-equiv-bool-Decidable-Prop
          ( map-equiv (equiv-universes-Decidable-Prop l l') P))
        ( p)))
```

### The type of decidable propositions in any universe is a set

```agda
is-set-Decidable-Prop : {l : Level} → is-set (Decidable-Prop l)
is-set-Decidable-Prop {l} =
  is-set-equiv bool equiv-bool-Decidable-Prop is-set-bool

Decidable-Prop-Set : (l : Level) → Set (lsuc l)
pr1 (Decidable-Prop-Set l) = Decidable-Prop l
pr2 (Decidable-Prop-Set l) = is-set-Decidable-Prop
```

### Extensionality of decidable propositions

```agda
module _
  {l : Level} (P Q : Decidable-Prop l)
  where

  extensionality-Decidable-Prop :
    (P ＝ Q) ≃ (type-Decidable-Prop P ↔ type-Decidable-Prop Q)
  extensionality-Decidable-Prop =
    ( propositional-extensionality
      ( prop-Decidable-Prop P)
      ( prop-Decidable-Prop Q)) ∘e
    ( equiv-ap-emb emb-prop-Decidable-Prop)

  iff-eq-Decidable-Prop :
    P ＝ Q → type-Decidable-Prop P ↔ type-Decidable-Prop Q
  iff-eq-Decidable-Prop = map-equiv extensionality-Decidable-Prop

  eq-iff-Decidable-Prop :
    (type-Decidable-Prop P → type-Decidable-Prop Q) →
    (type-Decidable-Prop Q → type-Decidable-Prop P) → P ＝ Q
  eq-iff-Decidable-Prop f g =
    map-inv-equiv extensionality-Decidable-Prop (pair f g)
```

### The type of decidable propositions in any universe is small

```agda
abstract
  is-small-Decidable-Prop :
    (l1 l2 : Level) → is-small l2 (Decidable-Prop l1)
  pr1 (is-small-Decidable-Prop l1 l2) = raise l2 bool
  pr2 (is-small-Decidable-Prop l1 l2) =
    compute-raise l2 bool ∘e equiv-bool-Decidable-Prop
```

### Decidable propositions have a count

```agda
count-is-decidable-Prop :
    {l : Level} (P : Prop l) →
    is-decidable (type-Prop P) → count (type-Prop P)
count-is-decidable-Prop P (inl x) =
  count-is-contr (is-proof-irrelevant-is-prop (is-prop-type-Prop P) x)
count-is-decidable-Prop P (inr x) =
  count-is-empty x
```

### Decidable propositions are finite

```agda
abstract
  is-finite-is-decidable-Prop :
    {l : Level} (P : Prop l) →
    is-decidable (type-Prop P) → is-finite (type-Prop P)
  is-finite-is-decidable-Prop P x =
    is-finite-count (count-is-decidable-Prop P x)

is-finite-type-Decidable-Prop :
  {l : Level} (P : Decidable-Prop l) → is-finite (type-Decidable-Prop P)
is-finite-type-Decidable-Prop P =
  is-finite-is-decidable-Prop
    ( prop-Decidable-Prop P)
    ( is-decidable-Decidable-Prop P)
```

### The type of decidable propositions of any universe level is finite

```agda
count-Decidable-Prop :
  {l : Level} → count (Decidable-Prop l)
pr1 count-Decidable-Prop = 2
pr2 count-Decidable-Prop =
  inv-equiv equiv-bool-Decidable-Prop ∘e equiv-bool-Fin-two-ℕ

is-finite-Decidable-Prop : {l : Level} → is-finite (Decidable-Prop l)
is-finite-Decidable-Prop {l} = unit-trunc-Prop count-Decidable-Prop

number-of-elements-Decidable-Prop :
  {l : Level} → number-of-elements-is-finite (is-finite-Decidable-Prop {l}) ＝ 2
number-of-elements-Decidable-Prop =
  inv
    ( compute-number-of-elements-is-finite
      ( count-Decidable-Prop)
      ( is-finite-Decidable-Prop))

decidable-Prop-𝔽 : (l : Level) → 𝔽 (lsuc l)
pr1 (decidable-Prop-𝔽 l) = Decidable-Prop l
pr2 (decidable-Prop-𝔽 l) = is-finite-Decidable-Prop
```

### Decidable propositions are closed under retracts

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-prop-retract-of :
    A retract-of B → is-decidable-prop B → is-decidable-prop A
  is-decidable-prop-retract-of R (p , d) =
    ( is-prop-retract-of R p , is-decidable-retract-of R d)
```

### Decidable propositions are closed under equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-prop-equiv :
    A ≃ B → is-decidable-prop B → is-decidable-prop A
  is-decidable-prop-equiv e =
    is-decidable-prop-retract-of (retract-equiv e)

  is-decidable-prop-equiv' :
    B ≃ A → is-decidable-prop B → is-decidable-prop A
  is-decidable-prop-equiv' e =
    is-decidable-prop-retract-of (retract-inv-equiv e)
```

### Negation has no fixed points on decidable propositions

```agda
abstract
  no-fixed-points-neg-Decidable-Prop :
    {l : Level} (P : Decidable-Prop l) →
    ¬ (type-Decidable-Prop P ↔ ¬ (type-Decidable-Prop P))
  no-fixed-points-neg-Decidable-Prop P =
    no-fixed-points-neg (type-Decidable-Prop P)
```
