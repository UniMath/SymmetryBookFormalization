# Tight apartness relations

```agda
module foundation.tight-apartness-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.embeddings
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.double-negation-stable-equality
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.sets
open import foundation-core.subtypes
```

</details>

## Idea

A [relation](foundation.binary-relations.md) `R` is said to be
{{#concept "tight" Disambiguation="binary relation" Agda=is-tight}} if for every
`x y : A` we have `¬ (R x y) → (x ＝ y)`.

## Definitions

### The tightness predicate

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : A → A → Prop l2)
  where

  is-tight : UU (l1 ⊔ l2)
  is-tight = (x y : A) → ¬ (type-Prop (R x y)) → x ＝ y

  is-tight-apartness-relation : UU (l1 ⊔ l2)
  is-tight-apartness-relation =
    is-apartness-relation R × is-tight

is-tight-Apartness-Relation :
  {l1 l2 : Level} {A : UU l1} (R : Apartness-Relation l2 A) → UU (l1 ⊔ l2)
is-tight-Apartness-Relation R = is-tight (rel-Apartness-Relation R)

Tight-Apartness-Relation :
  {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
Tight-Apartness-Relation l2 A =
  Σ (Apartness-Relation l2 A) (is-tight-Apartness-Relation)

module _
  {l1 l2 : Level} {A : UU l1} (R : Tight-Apartness-Relation l2 A)
  where

  apartness-relation-Tight-Apartness-Relation :
    Apartness-Relation l2 A
  apartness-relation-Tight-Apartness-Relation = pr1 R

  rel-Tight-Apartness-Relation : Relation-Prop l2 A
  rel-Tight-Apartness-Relation =
    rel-Apartness-Relation apartness-relation-Tight-Apartness-Relation

  apart-Tight-Apartness-Relation : Relation l2 A
  apart-Tight-Apartness-Relation =
    apart-Apartness-Relation apartness-relation-Tight-Apartness-Relation

  is-tight-apartness-relation-Tight-Apartness-Relation :
    is-tight-Apartness-Relation apartness-relation-Tight-Apartness-Relation
  is-tight-apartness-relation-Tight-Apartness-Relation = pr2 R
```

### Types with tight apartness

```agda
Type-With-Tight-Apartness : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Type-With-Tight-Apartness l1 l2 =
  Σ ( Type-With-Apartness l1 l2)
    ( λ X → is-tight (rel-apart-Type-With-Apartness X))

make-Type-With-Tight-Apartness :
  {l1 l2 : Level} {X : UU l1} →
  Tight-Apartness-Relation l2 X →
  Type-With-Tight-Apartness l1 l2
make-Type-With-Tight-Apartness {X = X} (R , t) = ((X , R) , t)

module _
  {l1 l2 : Level} (X : Type-With-Tight-Apartness l1 l2)
  where

  type-with-apartness-Type-With-Tight-Apartness : Type-With-Apartness l1 l2
  type-with-apartness-Type-With-Tight-Apartness = pr1 X

  type-Type-With-Tight-Apartness : UU l1
  type-Type-With-Tight-Apartness =
    type-Type-With-Apartness type-with-apartness-Type-With-Tight-Apartness

  apartness-relation-Type-With-Tight-Apartness :
    Apartness-Relation l2 type-Type-With-Tight-Apartness
  apartness-relation-Type-With-Tight-Apartness =
    apartness-relation-Type-With-Apartness
      ( type-with-apartness-Type-With-Tight-Apartness)

  rel-apart-Type-With-Tight-Apartness :
    Relation-Prop l2 type-Type-With-Tight-Apartness
  rel-apart-Type-With-Tight-Apartness =
    rel-apart-Type-With-Apartness type-with-apartness-Type-With-Tight-Apartness

  apart-Type-With-Tight-Apartness :
    Relation l2 type-Type-With-Tight-Apartness
  apart-Type-With-Tight-Apartness =
    apart-Type-With-Apartness type-with-apartness-Type-With-Tight-Apartness

  antirefl-apart-Type-With-Tight-Apartness :
    is-antireflexive rel-apart-Type-With-Tight-Apartness
  antirefl-apart-Type-With-Tight-Apartness =
    antirefl-apart-Type-With-Apartness
      type-with-apartness-Type-With-Tight-Apartness

  consistent-apart-Type-With-Tight-Apartness :
    is-consistent rel-apart-Type-With-Tight-Apartness
  consistent-apart-Type-With-Tight-Apartness =
    consistent-apart-Type-With-Apartness
      type-with-apartness-Type-With-Tight-Apartness

  symmetric-apart-Type-With-Tight-Apartness :
    is-symmetric apart-Type-With-Tight-Apartness
  symmetric-apart-Type-With-Tight-Apartness =
    symmetric-apart-Type-With-Apartness
      type-with-apartness-Type-With-Tight-Apartness

  cotransitive-apart-Type-With-Tight-Apartness :
    is-cotransitive rel-apart-Type-With-Tight-Apartness
  cotransitive-apart-Type-With-Tight-Apartness =
    cotransitive-apart-Type-With-Apartness
      type-with-apartness-Type-With-Tight-Apartness

  is-tight-apart-Type-With-Tight-Apartness :
    is-tight rel-apart-Type-With-Tight-Apartness
  is-tight-apart-Type-With-Tight-Apartness = pr2 X

  tight-apartness-relation-Type-With-Tight-Apartness :
    Tight-Apartness-Relation l2 type-Type-With-Tight-Apartness
  tight-apartness-relation-Type-With-Tight-Apartness =
    ( apartness-relation-Type-With-Tight-Apartness ,
      is-tight-apart-Type-With-Tight-Apartness)
```

## Properties

### Restricting tight apartness along injections

```agda
is-tight-restriction-Relation-Prop :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
  (f : injection X Y)
  (R : Relation-Prop l3 Y) → is-tight R →
  is-tight (restriction-Relation-Prop (map-injection f) R)
is-tight-restriction-Relation-Prop f R H x x' np =
  is-injective-injection f (H (map-injection f x) (map-injection f x') np)

restriction-Tight-Apartness-Relation :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  injection X Y → Tight-Apartness-Relation l3 Y → Tight-Apartness-Relation l3 X
restriction-Tight-Apartness-Relation f R =
  ( restriction-Apartness-Relation
    ( map-injection f)
    ( apartness-relation-Tight-Apartness-Relation R)) ,
  ( is-tight-restriction-Relation-Prop f
    ( rel-Tight-Apartness-Relation R)
    ( is-tight-apartness-relation-Tight-Apartness-Relation R))
```

### Restricting tight apartness along embeddings

```agda
restriction-emb-Tight-Apartness-Relation :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  X ↪ Y → Tight-Apartness-Relation l3 Y → Tight-Apartness-Relation l3 X
restriction-emb-Tight-Apartness-Relation f =
  restriction-Tight-Apartness-Relation (injection-emb f)
```

### Restricting tight apartness along retracts

```agda
restriction-retract-Tight-Apartness-Relation :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  X retract-of Y → Tight-Apartness-Relation l3 Y → Tight-Apartness-Relation l3 X
restriction-retract-Tight-Apartness-Relation R =
  restriction-Tight-Apartness-Relation (injection-retract R)
```

### Tight apartness on subtypes

```agda
type-subtype-Tight-Apartness-Relation :
  {l1 l2 l3 : Level} {X : UU l1} (P : subtype l2 X) →
  Tight-Apartness-Relation l3 X → Tight-Apartness-Relation l3 (type-subtype P)
type-subtype-Tight-Apartness-Relation P R =
  restriction-Tight-Apartness-Relation (injection-subtype P) R

subtype-Type-With-Tight-Apartness :
  {l1 l2 l3 : Level}
  ( X : Type-With-Tight-Apartness l1 l2)
  ( P : subtype l3 (type-Type-With-Tight-Apartness X)) →
  Type-With-Tight-Apartness (l1 ⊔ l3) l2
subtype-Type-With-Tight-Apartness X P =
  make-Type-With-Tight-Apartness
    ( type-subtype-Tight-Apartness-Relation P
      ( tight-apartness-relation-Type-With-Tight-Apartness X))
```

### Tight apartness on the type of dependent functions into a family of types with tight apartness

```agda
module _
  {l1 l2 l3 : Level} (X : UU l1) (Y : X → Type-With-Tight-Apartness l2 l3)
  where

  rel-apart-Π-Type-With-Tight-Apartness :
    Relation-Prop (l1 ⊔ l3) ((x : X) → type-Type-With-Tight-Apartness (Y x))
  rel-apart-Π-Type-With-Tight-Apartness =
    rel-apart-Π-Type-With-Apartness X
      ( type-with-apartness-Type-With-Tight-Apartness ∘ Y)

  apart-Π-Type-With-Tight-Apartness :
    Relation (l1 ⊔ l3) ((x : X) → type-Type-With-Tight-Apartness (Y x))
  apart-Π-Type-With-Tight-Apartness =
    apart-Π-Type-With-Apartness X
      ( type-with-apartness-Type-With-Tight-Apartness ∘ Y)

  is-prop-apart-Π-Type-With-Tight-Apartness :
    (f g : (x : X) → type-Type-With-Tight-Apartness (Y x)) →
    is-prop (apart-Π-Type-With-Tight-Apartness f g)
  is-prop-apart-Π-Type-With-Tight-Apartness =
    is-prop-apart-Π-Type-With-Apartness X
      ( type-with-apartness-Type-With-Tight-Apartness ∘ Y)

  is-antireflexive-apart-Π-Type-With-Tight-Apartness :
    is-antireflexive rel-apart-Π-Type-With-Tight-Apartness
  is-antireflexive-apart-Π-Type-With-Tight-Apartness =
    is-antireflexive-apart-Π-Type-With-Apartness X
      ( type-with-apartness-Type-With-Tight-Apartness ∘ Y)

  is-symmetric-apart-Π-Type-With-Tight-Apartness :
    is-symmetric apart-Π-Type-With-Tight-Apartness
  is-symmetric-apart-Π-Type-With-Tight-Apartness =
    is-symmetric-apart-Π-Type-With-Apartness X
      ( type-with-apartness-Type-With-Tight-Apartness ∘ Y)

  is-cotransitive-apart-Π-Type-With-Tight-Apartness :
    is-cotransitive rel-apart-Π-Type-With-Tight-Apartness
  is-cotransitive-apart-Π-Type-With-Tight-Apartness =
    is-cotransitive-apart-Π-Type-With-Apartness X
      ( type-with-apartness-Type-With-Tight-Apartness ∘ Y)

  is-apartness-relation-apart-Π-Type-With-Tight-Apartness :
    is-apartness-relation rel-apart-Π-Type-With-Tight-Apartness
  is-apartness-relation-apart-Π-Type-With-Tight-Apartness =
    is-apartness-relation-apart-Π-Type-With-Apartness X
      ( type-with-apartness-Type-With-Tight-Apartness ∘ Y)

  apartness-relation-Π-Type-With-Tight-Apartness :
    Apartness-Relation
      ( l1 ⊔ l3)
      ( (x : X) → type-Type-With-Tight-Apartness (Y x))
  apartness-relation-Π-Type-With-Tight-Apartness =
    apartness-relation-Π-Type-With-Apartness X
      ( type-with-apartness-Type-With-Tight-Apartness ∘ Y)

  is-tight-apart-Π-Type-With-Tight-Apartness :
    is-tight rel-apart-Π-Type-With-Tight-Apartness
  is-tight-apart-Π-Type-With-Tight-Apartness f g H =
    eq-htpy
      ( λ x →
        is-tight-apart-Type-With-Tight-Apartness
          ( Y x)
          ( f x)
          ( g x)
          ( λ u → H (unit-trunc-Prop (x , u))))

  tight-apartness-relation-Π-Type-With-Tight-Apartness :
    Tight-Apartness-Relation (l1 ⊔ l3)
      ( (x : X) → type-Type-With-Tight-Apartness (Y x))
  tight-apartness-relation-Π-Type-With-Tight-Apartness =
    apartness-relation-Π-Type-With-Apartness X
      ( type-with-apartness-Type-With-Tight-Apartness ∘ Y) ,
    is-tight-apart-Π-Type-With-Tight-Apartness

  Π-Type-With-Tight-Apartness : Type-With-Tight-Apartness (l1 ⊔ l2) (l1 ⊔ l3)
  Π-Type-With-Tight-Apartness =
    Π-Type-With-Apartness X
      ( type-with-apartness-Type-With-Tight-Apartness ∘ Y) ,
    is-tight-apart-Π-Type-With-Tight-Apartness
```

### Tight apartness on the type of functions into a type with tight apartness

```agda
module _
  {l1 l2 l3 : Level} (X : UU l1) (Y : Type-With-Tight-Apartness l2 l3)
  where

  rel-apart-function-into-Type-With-Tight-Apartness :
    Relation-Prop (l1 ⊔ l3) (X → type-Type-With-Tight-Apartness Y)
  rel-apart-function-into-Type-With-Tight-Apartness =
    rel-apart-Π-Type-With-Tight-Apartness X (λ _ → Y)

  apart-function-into-Type-With-Tight-Apartness :
    Relation (l1 ⊔ l3) (X → type-Type-With-Tight-Apartness Y)
  apart-function-into-Type-With-Tight-Apartness =
    apart-Π-Type-With-Tight-Apartness X (λ _ → Y)

  is-prop-apart-function-into-Type-With-Tight-Apartness :
    (f g : X → type-Type-With-Tight-Apartness Y) →
    is-prop (apart-function-into-Type-With-Tight-Apartness f g)
  is-prop-apart-function-into-Type-With-Tight-Apartness =
    is-prop-apart-Π-Type-With-Tight-Apartness X (λ _ → Y)

  is-antireflexive-apart-function-into-Type-With-Tight-Apartness :
    is-antireflexive rel-apart-function-into-Type-With-Tight-Apartness
  is-antireflexive-apart-function-into-Type-With-Tight-Apartness =
    is-antireflexive-apart-Π-Type-With-Tight-Apartness X (λ _ → Y)

  is-symmetric-apart-function-into-Type-With-Tight-Apartness :
    is-symmetric apart-function-into-Type-With-Tight-Apartness
  is-symmetric-apart-function-into-Type-With-Tight-Apartness =
    is-symmetric-apart-Π-Type-With-Tight-Apartness X (λ _ → Y)

  is-cotransitive-apart-function-into-Type-With-Tight-Apartness :
    is-cotransitive rel-apart-function-into-Type-With-Tight-Apartness
  is-cotransitive-apart-function-into-Type-With-Tight-Apartness =
    is-cotransitive-apart-Π-Type-With-Tight-Apartness X (λ _ → Y)

  is-apartness-relation-apart-function-into-Type-With-Tight-Apartness :
    is-apartness-relation rel-apart-function-into-Type-With-Tight-Apartness
  is-apartness-relation-apart-function-into-Type-With-Tight-Apartness =
    is-apartness-relation-apart-Π-Type-With-Tight-Apartness X (λ _ → Y)

  apartness-relation-function-into-Type-With-Tight-Apartness :
    Apartness-Relation (l1 ⊔ l3) (X → type-Type-With-Tight-Apartness Y)
  apartness-relation-function-into-Type-With-Tight-Apartness =
    apartness-relation-Π-Type-With-Tight-Apartness X (λ _ → Y)

  is-tight-apart-function-into-Type-With-Tight-Apartness :
    is-tight rel-apart-function-into-Type-With-Tight-Apartness
  is-tight-apart-function-into-Type-With-Tight-Apartness =
    is-tight-apart-Π-Type-With-Tight-Apartness X (λ _ → Y)

  tight-apartness-relation-function-into-Type-With-Tight-Apartness :
    Tight-Apartness-Relation (l1 ⊔ l3) (X → type-Type-With-Tight-Apartness Y)
  tight-apartness-relation-function-into-Type-With-Tight-Apartness =
    tight-apartness-relation-Π-Type-With-Tight-Apartness X (λ _ → Y)

  function-into-Type-With-Tight-Apartness :
    Type-With-Tight-Apartness (l1 ⊔ l2) (l1 ⊔ l3)
  function-into-Type-With-Tight-Apartness =
    Π-Type-With-Tight-Apartness X (λ _ → Y)
```

### Types with tight apartness relations have double negation stable equality

```agda
has-double-negation-stable-equality-has-tight-antireflexive-relation :
  {l1 l2 : Level} {A : UU l1} {R : A → A → UU l2} →
  ((x : A) → ¬ (R x x)) → ((x y : A) → ¬ (R x y) → x ＝ y) →
  has-double-negation-stable-equality A
has-double-negation-stable-equality-has-tight-antireflexive-relation
  H K x y nnp =
  K x y (elim-triple-negation (map-double-negation (rec-Id x (H x) y) nnp))

has-double-negation-stable-equality-type-Type-With-Tight-Apartness :
  {l1 l2 : Level} (A : Type-With-Tight-Apartness l1 l2) →
  has-double-negation-stable-equality (type-Type-With-Tight-Apartness A)
has-double-negation-stable-equality-type-Type-With-Tight-Apartness A =
  has-double-negation-stable-equality-has-tight-antireflexive-relation
    ( antirefl-apart-Type-With-Tight-Apartness A)
    ( is-tight-apart-Type-With-Tight-Apartness A)
```

### A type with double negation stable equality is a type whose negated equality relation is tight

```agda
is-tight-nonequal-has-double-negation-stable-equality :
  {l : Level} {A : UU l} →
  has-double-negation-stable-equality A →
  is-tight (nonequal-Prop {A = A})
is-tight-nonequal-has-double-negation-stable-equality H x y = H x y
```

### Types with tight apartness relations are sets

```agda
is-set-has-tight-antireflexive-relation :
  {l1 l2 : Level} {A : UU l1} {R : A → A → UU l2} →
  ((x : A) → ¬ (R x x)) → ((x y : A) → ¬ (R x y) → x ＝ y) → is-set A
is-set-has-tight-antireflexive-relation {R = R} =
  is-set-prop-in-id (λ x y → ¬ (R x y)) (λ x y → is-prop-neg)

is-set-type-Type-With-Tight-Apartness :
  {l1 l2 : Level} (A : Type-With-Tight-Apartness l1 l2) →
  is-set (type-Type-With-Tight-Apartness A)
is-set-type-Type-With-Tight-Apartness A =
  is-set-has-tight-antireflexive-relation
    ( antirefl-apart-Type-With-Tight-Apartness A)
    ( is-tight-apart-Type-With-Tight-Apartness A)

set-Type-With-Tight-Apartness :
  {l1 l2 : Level} (A : Type-With-Tight-Apartness l1 l2) →
  Set l1
set-Type-With-Tight-Apartness A =
  ( type-Type-With-Tight-Apartness A , is-set-type-Type-With-Tight-Apartness A)
```

## References

{{#bibliography}} {{#reference MRR88}}
