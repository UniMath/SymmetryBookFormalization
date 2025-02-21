# Universal decidability search

```agda
module foundation.universal-decidability-search where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.constant-maps
open import foundation.coproduct-types
open import foundation.decidability-search
open import foundation.decidable-dependent-function-types
open import foundation.decidable-embeddings
open import foundation.decidable-maps
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-type-families
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.equivalences
open import foundation.evaluation-functions
open import foundation.fibers-of-maps
open import foundation.full-subtypes
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.irrefutable-equality
open import foundation.locally-small-types
open import foundation.mere-equality
open import foundation.negation
open import foundation.pi-0-trivial-maps
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.small-types
open import foundation.surjective-maps
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.contractible-types

open import logic.complements-decidable-subtypes
open import logic.de-morgan-subtypes
open import logic.de-morgan-types
open import logic.double-negation-dense-maps
open import logic.propositionally-decidable-types

open import univalent-combinatorics.counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A type `X` has
{{#concept "universal decidability search" Disambiguation="on type" Agda=has-universal-decidability-search}}
if we have a terminating algorithm `f` that, for every
[decidable type family](foundation.decidable-type-families.md) `P` on `X`
computes a section of `P`, `(x : X) → P x`, or produces a proof no such section
exists, in other words, exhibits a fiber of `P` that is
[empty](foundation.empty-types.md).

```text
  (P : decidable-family X) → is-decidable (∀ x. P x)
```

**Terminology.** In the terminology of Martín Escardó, a type that has universal
decidability search is referred to as _weakly compact_ or _satisfying the weak
principle of omniscience_, or _Π-compact_. {{#cite TypeTopology}} We reserve the
term _universally decidability searchable_ for types for which there (merely)
[exists](foundation.existential-quantification.md) a universal decidability
search.

## Definitions

### The predicate of having decidability search

```agda
has-universal-decidability-search-Level :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-universal-decidability-search-Level l2 X =
  (P : decidable-family l2 X) →
  is-decidable ((x : X) → family-decidable-family P x)

has-universal-decidability-search : {l1 : Level} → UU l1 → UUω
has-universal-decidability-search X =
  {l2 : Level} → has-universal-decidability-search-Level l2 X
```

### The type of types with universal decidability search

```agda
record Type-With-Universal-Decidable-Search (l : Level) : UUω
  where
  field

    type-Type-With-Universal-Decidable-Search : UU l

    has-universal-decidability-search-type-Type-With-Universal-Decidable-Search :
      has-universal-decidability-search
        type-Type-With-Universal-Decidable-Search
```

### The predicate of having decidability search on subtypes

```agda
has-universal-decidability-search-on-subtypes-Level :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-universal-decidability-search-on-subtypes-Level l2 X =
  (P : decidable-subtype l2 X) → is-decidable (is-full-decidable-subtype P)

has-universal-decidability-search-on-subtypes : {l1 : Level} → UU l1 → UUω
has-universal-decidability-search-on-subtypes X =
  {l2 : Level} → has-universal-decidability-search-on-subtypes-Level l2 X
```

## Properties

### Types with universal decidability search are De Morgan

```agda
is-de-morgan-has-universal-decidability-search-Prop :
  {l1 : Level} {X : UU l1} →
  has-universal-decidability-search X → is-de-morgan X
is-de-morgan-has-universal-decidability-search-Prop f =
  f ((λ _ → empty) , (λ _ → inr id))
```

### Types with universal decidability search on subtypes have universal decidability search

```agda
has-universal-decidability-search-has-universal-decidability-search-on-subtypes :
  {l1 : Level} {X : UU l1} →
  has-universal-decidability-search-on-subtypes X →
  has-universal-decidability-search X
has-universal-decidability-search-has-universal-decidability-search-on-subtypes
  f P =
  map-coproduct
    ( λ nnp x →
      rec-coproduct id (ex-falso ∘ nnp x) (is-decidable-decidable-family P x))
    ( λ nnnp p → nnnp (intro-double-negation ∘ p))
    ( f ( λ x →
          neg-type-Decidable-Prop
            ( ¬ (family-decidable-family P x))
            ( is-decidable-neg (is-decidable-decidable-family P x))))
```

### Universal decidability search transfers along double negation dense maps

```agda
has-universal-decidability-search-double-negation-dense-map :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → X ↠¬¬ Y →
  has-universal-decidability-search X → has-universal-decidability-search Y
has-universal-decidability-search-double-negation-dense-map h f P =
  map-coproduct
    ( λ p x →
      rec-coproduct
        ( id)
        ( λ np →
          ex-falso
            ( is-double-negation-dense-map-double-negation-dense-map h x
              ( λ yp →
                np (tr (family-decidable-family P) (pr2 yp) (p (pr1 yp))))))
        ( is-decidable-decidable-family P x))
    ( λ nph p → nph (p ∘ map-double-negation-dense-map h))
    ( f (reindex-decidable-family P (map-double-negation-dense-map h)))
```

### Universal decidability search transfers along surjections

```agda
has-universal-decidability-search-surjection :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → X ↠ Y →
  has-universal-decidability-search X → has-universal-decidability-search Y
has-universal-decidability-search-surjection h =
  has-universal-decidability-search-double-negation-dense-map
    ( double-negation-dense-map-surjection h)
```

### Types with universal decidability search are closed under retracts

```agda
has-universal-decidability-search-retract :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → Y retract-of X →
  has-universal-decidability-search X → has-universal-decidability-search Y
has-universal-decidability-search-retract R =
  has-universal-decidability-search-double-negation-dense-map
    ( double-negation-dense-map-retract R)
```

### Types with universal decidability search are closed under equivalences

```agda
has-universal-decidability-search-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → Y ≃ X →
  has-universal-decidability-search X → has-universal-decidability-search Y
has-universal-decidability-search-equiv e =
  has-universal-decidability-search-retract (retract-equiv e)

has-universal-decidability-search-equiv' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → X ≃ Y →
  has-universal-decidability-search X → has-universal-decidability-search Y
has-universal-decidability-search-equiv' e =
  has-universal-decidability-search-retract (retract-inv-equiv e)
```

### The empty type has decidability search

```agda
has-universal-decidability-search-empty :
  has-universal-decidability-search empty
has-universal-decidability-search-empty P = inl ind-empty
```

### The unit type has decidability search

```agda
has-universal-decidability-search-unit : has-universal-decidability-search unit
has-universal-decidability-search-unit P =
  map-coproduct
    ( λ p _ → p)
    ( λ np p → np (p star))
    ( is-decidable-decidable-family P star)
```

### Coproducts of types with universal decidability search

Coproducts of types with universal decidability search have universal
decidability search. Conversely, if the coproduct has decidability search and a
summand has an element, then that summand also has decidability search.

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  has-universal-decidability-search-coproduct :
    has-universal-decidability-search X →
    has-universal-decidability-search Y →
    has-universal-decidability-search (X + Y)
  has-universal-decidability-search-coproduct f g P =
    rec-coproduct
      ( λ pl →
        rec-coproduct
          ( λ pr → inl (ind-coproduct (family-decidable-family P) pl pr))
          ( λ npr → inr (λ p → npr (p ∘ inr)))
          ( g (reindex-decidable-family P inr)))
      ( λ npl → inr (λ p → npl (p ∘ inl)))
      ( f (reindex-decidable-family P inl))

  has-universal-decidability-search-left-summand-coproduct :
    has-universal-decidability-search (X + Y) →
    X → has-universal-decidability-search X
  has-universal-decidability-search-left-summand-coproduct f x =
    has-universal-decidability-search-retract
      ( retract-left-summand-coproduct x)
      ( f)

  has-universal-decidability-search-right-summand-coproduct :
    has-universal-decidability-search (X + Y) →
    Y → has-universal-decidability-search Y
  has-universal-decidability-search-right-summand-coproduct f y =
    has-universal-decidability-search-retract
      ( retract-right-summand-coproduct y)
      ( f)
```

### Dependent sums of types with universal decidability search

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  has-universal-decidability-search-Σ :
    has-universal-decidability-search A →
    ((x : A) → has-universal-decidability-search (B x)) →
    has-universal-decidability-search (Σ A B)
  has-universal-decidability-search-Σ f g P =
    is-decidable-equiv equiv-ev-pair
      ( f ( ( λ x → (y : B x) → family-decidable-family P (x , y)) ,
            ( λ x → g x (reindex-decidable-family P (pair x)))))

  has-universal-decidability-search-base-has-universal-decidability-search-Σ :
    has-universal-decidability-search (Σ A B) →
    ((x : A) → B x) →
    has-universal-decidability-search A
  has-universal-decidability-search-base-has-universal-decidability-search-Σ
    f s =
    has-universal-decidability-search-retract
      ( retract-base-Σ-section-family s)
      ( f)
```

### Products of types with universal decidability search

```agda
has-universal-decidability-search-product :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-universal-decidability-search A →
  has-universal-decidability-search B →
  has-universal-decidability-search (A × B)
has-universal-decidability-search-product f g =
  has-universal-decidability-search-Σ f (λ _ → g)
```

### Factors of products with universal decidability search

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  has-universal-decidability-search-left-factor-product :
    has-universal-decidability-search (X × Y) →
    Y → has-universal-decidability-search X
  has-universal-decidability-search-left-factor-product f y =
    has-universal-decidability-search-retract (retract-left-factor-product y) f

  has-universal-decidability-search-right-factor-product :
    has-universal-decidability-search (X × Y) →
    X → has-universal-decidability-search Y
  has-universal-decidability-search-right-factor-product f x =
    has-universal-decidability-search-retract (retract-right-factor-product x) f
```

### Standard finite types have universal decidability search

```agda
has-universal-decidability-search-Fin :
  (n : ℕ) → has-universal-decidability-search (Fin n)
has-universal-decidability-search-Fin zero-ℕ =
  has-universal-decidability-search-empty
has-universal-decidability-search-Fin (succ-ℕ n) =
  has-universal-decidability-search-coproduct
    ( has-universal-decidability-search-Fin n)
    ( has-universal-decidability-search-unit)
```

### Types equipped with a counting have universal decidability search

```agda
has-universal-decidability-search-count :
  {l : Level} {X : UU l} → count X → has-universal-decidability-search X
has-universal-decidability-search-count f =
  has-universal-decidability-search-equiv'
    ( equiv-count f)
    ( has-universal-decidability-search-Fin (number-of-elements-count f))
```

### The booleans have universal decidability search

```agda
has-universal-decidability-search-bool : has-universal-decidability-search bool
has-universal-decidability-search-bool =
  has-universal-decidability-search-equiv'
    ( equiv-bool-Fin-two-ℕ)
    ( has-universal-decidability-search-Fin 2)
```

### Types with decidability search have universal decidability search

```agda
has-universal-decidability-search-has-decidability-search :
  {l : Level} {X : UU l} →
  has-decidability-search X →
  has-universal-decidability-search X
has-universal-decidability-search-has-decidability-search f P =
  rec-coproduct
    ( λ xnp → inr (λ p → pr2 xnp (p (pr1 xnp))))
    ( λ nxnp →
      inl
        ( λ x →
          rec-coproduct
            ( id)
            ( λ np → ex-falso (nxnp (x , np)))
            ( is-decidable-decidable-family P x)))
    ( f (neg-decidable-family P))
```

### Merely decidable π₀-trivial types have universal decidability search

```agda
abstract
  has-universal-decidability-search-on-subtypes-is-inhabited-or-empty-all-elements-merely-equal :
    {l : Level} {X : UU l} →
    is-inhabited-or-empty X →
    all-elements-merely-equal X →
    has-universal-decidability-search-on-subtypes X
  has-universal-decidability-search-on-subtypes-is-inhabited-or-empty-all-elements-merely-equal
    { X = X} (inl |x|) H P =
    rec-trunc-Prop
      ( is-decidable-Prop (Π-Prop X (subtype-decidable-subtype P)))
      ( λ x →
        map-coproduct
          ( λ p x' →
            rec-trunc-Prop
              ( subtype-decidable-subtype P x')
              ( λ r → tr (is-in-decidable-subtype P) r p)
              ( H x x'))
          ( map-neg (ev x))
          ( is-decidable-decidable-subtype P x))
      ( |x|)
  has-universal-decidability-search-on-subtypes-is-inhabited-or-empty-all-elements-merely-equal
    ( inr nx) H P =
    inl (ex-falso ∘ nx)

abstract
  has-universal-decidability-search-is-inhabited-or-empty-all-elements-merely-equal :
    {l : Level} {X : UU l} →
    is-inhabited-or-empty X →
    all-elements-merely-equal X →
    has-universal-decidability-search X
  has-universal-decidability-search-is-inhabited-or-empty-all-elements-merely-equal
    d H =
    has-universal-decidability-search-has-universal-decidability-search-on-subtypes
      ( has-universal-decidability-search-on-subtypes-is-inhabited-or-empty-all-elements-merely-equal
        ( d)
        ( H))

abstract
  has-universal-decidability-search-is-decidable-all-elements-merely-equal :
    {l : Level} {X : UU l} →
    is-decidable X →
    all-elements-merely-equal X →
    has-universal-decidability-search X
  has-universal-decidability-search-is-decidable-all-elements-merely-equal d =
    has-universal-decidability-search-is-inhabited-or-empty-all-elements-merely-equal
      ( is-inhabited-or-empty-is-decidable d)
```

### Decidable irrefutably π₀-trivial types have universal decidability search

```agda
abstract
  has-universal-decidability-search-is-decidable-all-elements-irrefutably-equal :
    {l : Level} {X : UU l} →
    all-elements-irrefutably-equal X →
    is-decidable X →
    has-universal-decidability-search X
  has-universal-decidability-search-is-decidable-all-elements-irrefutably-equal
    H d =
    has-universal-decidability-search-has-decidability-search
      ( has-decidability-search-is-decidable-all-elements-irrefutably-equal H d)
```

### The total space of decidable π₀-trivial families over types with universal decidability search have universal decidability search

```agda
abstract
  has-universal-decidability-search-Σ-decidable-family-all-elements-irrefutably-equal :
    {l1 l2 : Level} {X : UU l1} →
    has-universal-decidability-search X →
    (P : decidable-family l2 X) →
    ((x : X) → all-elements-irrefutably-equal (family-decidable-family P x)) →
    has-universal-decidability-search (Σ X (family-decidable-family P))
  has-universal-decidability-search-Σ-decidable-family-all-elements-irrefutably-equal
    f P H =
    has-universal-decidability-search-Σ f
      ( λ x →
        has-universal-decidability-search-is-decidable-all-elements-irrefutably-equal
          ( H x)
          ( is-decidable-decidable-family P x))
```

### Decidable subtypes of types with universal decidability search have universal decidability search

```agda
abstract
  has-universal-decidability-search-type-decidable-subtype :
    {l1 l2 : Level} {X : UU l1} →
    has-universal-decidability-search X →
    (P : decidable-subtype l2 X) →
    has-universal-decidability-search (type-decidable-subtype P)
  has-universal-decidability-search-type-decidable-subtype {X = X} f P =
    has-universal-decidability-search-Σ-decidable-family-all-elements-irrefutably-equal
      ( f)
      ( decidable-family-decidable-subtype P)
      ( λ x p q →
        intro-double-negation
          ( eq-is-prop (is-prop-is-in-decidable-subtype P x)))

has-universal-decidability-search-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → Y ↪ᵈ X →
  has-universal-decidability-search X → has-universal-decidability-search Y
has-universal-decidability-search-decidable-emb h f =
  has-universal-decidability-search-equiv'
    ( compute-type-decidable-subtype-decidable-emb h)
    ( has-universal-decidability-search-type-decidable-subtype f
      ( decidable-subtype-decidable-emb h))
```
