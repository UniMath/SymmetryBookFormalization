# Decidability search

```agda
module foundation.decidability-search where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.constant-maps
open import foundation.coproduct-types
open import foundation.decidable-dependent-pair-types
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
open import foundation.existential-quantification
open import foundation.fibers-of-maps
open import foundation.full-subtypes
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.irrefutable-equality
open import foundation.locally-small-types
open import foundation.logical-operations-booleans
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
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.contractible-types

open import logic.complements-decidable-subtypes
open import logic.de-morgan-subtypes
open import logic.double-negation-dense-maps
open import logic.propositionally-decidable-types

open import univalent-combinatorics.counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A type `X` has
{{#concept "decidability search" Disambiguation="on type" Agda=has-decidability-search}}
if we have a terminating algorithm `f` that, for every
[decidable type family](foundation.decidable-type-families.md) `P` on `X`
computes an element in `P` or produces a proof that `P` is the empty family.

**Terminology.** In the terminology of Martín Escardó, a type that has
decidability search on decidable _subtypes_ is referred to as _searchable_,
_exhaustively searchable_, _exhaustibly searchable_, _exhaustible_,
_omniscient_, _satisfying the principle of omniscience_, _compact_, or
_Σ-compact_. {{#cite Esc08}} {{#cite TypeTopology}} We reserve the term
_decidability searchable_ for types for which there (merely)
[exists](foundation.existential-quantification.md) a decidability search.

## Definitions

### The predicate of having decidability search

```agda
has-decidability-search-Level :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-decidability-search-Level l2 X =
  (P : decidable-family l2 X) → is-decidable (Σ X (family-decidable-family P))

has-decidability-search : {l1 : Level} → UU l1 → UUω
has-decidability-search X = {l2 : Level} → has-decidability-search-Level l2 X
```

### The predicate of having small decidability search

```agda
has-decidability-search-bool : {l1 : Level} → UU l1 → UU l1
has-decidability-search-bool X =
  (b : X → bool) → is-decidable (Σ X (is-true ∘ b))
```

### The type of types with decidability search

```agda
record Type-With-Decidable-Search (l : Level) : UUω
  where
  field

    type-Type-With-Decidable-Search : UU l

    has-decidability-search-type-Type-With-Decidable-Search :
      has-decidability-search type-Type-With-Decidable-Search

open Type-With-Decidable-Search public
```

### The predicate of having decidability search on subtypes

```agda
has-decidability-search-on-subtypes-Level :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-decidability-search-on-subtypes-Level l2 X =
  (P : decidable-subtype l2 X) → is-decidable (Σ X (is-in-decidable-subtype P))

has-decidability-search-on-subtypes : {l1 : Level} → UU l1 → UUω
has-decidability-search-on-subtypes X =
  {l2 : Level} → has-decidability-search-on-subtypes-Level l2 X
```

### The predicate of having pointed decidability search

```agda
has-pointed-decidability-search-Level :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-pointed-decidability-search-Level l2 X =
  ( P : decidable-family l2 X) →
  Σ X
    ( λ x₀ →
      family-decidable-family P x₀ → (x : X) → family-decidable-family P x)

has-pointed-decidability-search : {l1 : Level} → UU l1 → UUω
has-pointed-decidability-search X =
  {l2 : Level} → has-pointed-decidability-search-Level l2 X
```

### The predicate of having pointed decidability search on subtypes

```agda
has-pointed-decidability-search-on-subtypes-Level :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-pointed-decidability-search-on-subtypes-Level l2 X =
  ( P : decidable-subtype l2 X) →
  Σ X
    ( λ x₀ →
      is-in-decidable-subtype P x₀ → (x : X) → is-in-decidable-subtype P x)

has-pointed-decidability-search-on-subtypes : {l1 : Level} → UU l1 → UUω
has-pointed-decidability-search-on-subtypes X =
  {l2 : Level} → has-pointed-decidability-search-on-subtypes-Level l2 X
```

### The small predicate of having pointed decidability search

```agda
has-pointed-decidability-search-bool : {l : Level} → UU l → UU l
has-pointed-decidability-search-bool X =
  (b : X → bool) → Σ X (λ x₀ → is-true (b x₀) → (x : X) → is-true (b x))

has-pointed-decidability-search-bool' : {l : Level} → UU l → UU l
has-pointed-decidability-search-bool' X =
  (b : X → bool) → Σ X (λ x₀ → is-false (b x₀) → (x : X) → is-false (b x))
```

## Properties

### Types with decidability search are decidable

```agda
is-decidable-type-has-decidability-search :
  {l1 : Level} {X : UU l1} → has-decidability-search X → is-decidable X
is-decidable-type-has-decidability-search f =
  is-decidable-equiv'
    ( right-unit-law-product)
    ( f ((λ _ → unit) , (λ _ → inl star)))
```

### Types with decidability search on subtypes have decidability search

```agda
abstract
  has-decidability-search-has-decidability-search-on-subtypes :
    {l1 : Level} {X : UU l1} →
    has-decidability-search-on-subtypes X → has-decidability-search X
  has-decidability-search-has-decidability-search-on-subtypes f P =
    map-coproduct
      ( λ xp →
        pr1 xp ,
        rec-coproduct
          ( id)
          ( ex-falso ∘ pr2 xp)
          ( is-decidable-decidable-family P (pr1 xp)))
      ( λ nxp xp → nxp (pr1 xp , intro-double-negation (pr2 xp)))
      ( f ( λ x →
            neg-type-Decidable-Prop
              ( ¬ (family-decidable-family P x))
              ( is-decidable-neg (is-decidable-decidable-family P x))))
```

### A type has decidability search if and only if it satisfies the small predicate of having decidability search

```agda
module _
  {l : Level} {X : UU l}
  where

  has-decidability-search-on-subtypes-has-decidability-search-bool :
    has-decidability-search-bool X →
    has-decidability-search-on-subtypes X
  has-decidability-search-on-subtypes-has-decidability-search-bool f P =
    is-decidable-equiv
      ( equiv-tot (compute-equiv-bool-Decidable-Prop ∘ P))
      ( f (bool-Decidable-Prop ∘ P))

  abstract
    has-decidability-search-has-decidability-search-bool :
      has-decidability-search-bool X → has-decidability-search X
    has-decidability-search-has-decidability-search-bool f =
      has-decidability-search-has-decidability-search-on-subtypes
        ( has-decidability-search-on-subtypes-has-decidability-search-bool f)

  has-decidability-search-bool-has-decidability-search-on-subtypes :
    has-decidability-search-on-subtypes X → has-decidability-search-bool X
  has-decidability-search-bool-has-decidability-search-on-subtypes f P =
    f (is-true-Decidable-Prop ∘ P)

  has-decidability-search-bool-has-decidability-search :
    has-decidability-search X → has-decidability-search-bool X
  has-decidability-search-bool-has-decidability-search f P =
    f (is-true ∘ P , λ x → has-decidable-equality-bool (P x) true)
```

### A pointed type with decidability search has pointed decidability search

```agda
has-pointed-decidability-search-has-decidability-search-has-element :
  {l : Level} {X : UU l} →
  X → has-decidability-search X → has-pointed-decidability-search X
has-pointed-decidability-search-has-decidability-search-has-element x₀ f P =
  rec-coproduct
    ( λ xr → (pr1 xr , ex-falso ∘ pr2 xr))
    ( λ nx →
      ( x₀ ,
        λ _ x →
        rec-coproduct
          ( id)
          ( λ npx → ex-falso (nx (x , npx)))
          ( is-decidable-decidable-family P x)))
    ( f (neg-decidable-family P))
```

### The two small predicate of having pointed decidability search are equivalent

```agda
flip-has-pointed-decidability-search-bool :
  {l : Level} {X : UU l} →
  has-pointed-decidability-search-bool' X →
  has-pointed-decidability-search-bool X
pr1 (flip-has-pointed-decidability-search-bool H b) = pr1 (H (neg-bool ∘ b))
pr2 (flip-has-pointed-decidability-search-bool H b) p x =
  is-true-is-false-neg-bool
    ( pr2
      ( H (neg-bool ∘ b))
      ( is-false-is-true-neg-bool
        ( is-involution-neg-bool (b (pr1 (H (neg-bool ∘ b)))) ∙ p))
      ( x))
```

> The converse remains to be formalized.

### A type has pointed decidability search if and only if it has small pointed decidability search

```agda
abstract
  has-pointed-decidability-search-on-subtypes-has-pointed-decidability-search-bool :
    {l : Level} {X : UU l} →
    has-pointed-decidability-search-bool X →
    has-pointed-decidability-search-on-subtypes X
  has-pointed-decidability-search-on-subtypes-has-pointed-decidability-search-bool
    f P =
    ( pr1 (f (bool-Decidable-Prop ∘ P))) ,
    ( λ Px₀ x →
      map-inv-equiv
        ( compute-equiv-bool-Decidable-Prop (P x))
          ( pr2
            ( f (bool-Decidable-Prop ∘ P))
            ( map-equiv
              ( compute-equiv-bool-Decidable-Prop
                ( P (pr1 (f (bool-Decidable-Prop ∘ P)))))
              ( Px₀))
            ( x)))

has-pointed-decidability-search-bool-has-pointed-decidability-search-on-subtypes :
  {l : Level} {X : UU l} →
  has-pointed-decidability-search-on-subtypes X →
  has-pointed-decidability-search-bool X
has-pointed-decidability-search-bool-has-pointed-decidability-search-on-subtypes
  f b =
  f (is-true-Decidable-Prop ∘ b)
```

### Types with pointed decidability search on subtypes has pointed decidability search

```agda
abstract
  has-pointed-decidability-search-has-pointed-decidability-search-on-subtypes :
    {l1 : Level} {X : UU l1} →
    has-pointed-decidability-search-on-subtypes X →
    has-pointed-decidability-search X
  has-pointed-decidability-search-has-pointed-decidability-search-on-subtypes
    {X = X} f P =
      ( pr1 g) ,
      ( λ p x →
        rec-coproduct
          ( id)
          ( ex-falso ∘ pr2 g (intro-double-negation p) x)
          ( is-decidable-decidable-family P x))
      where
        g : Σ X
              ( λ x₀ →
                ¬¬ (family-decidable-family P x₀) →
                (x : X) → ¬¬ (family-decidable-family P x))
        g =
          f
          ( λ x →
            neg-type-Decidable-Prop
              ( ¬ (family-decidable-family P x))
              ( is-decidable-neg (is-decidable-decidable-family P x)))
```

### Types with pointed decidability search have decidability search

```agda
is-decidable-Σ-is-this-other-thing :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} →
  ((x : X) → ¬ (Y x)) → ¬ (Σ X Y)
is-decidable-Σ-is-this-other-thing f xp = f (pr1 xp) (pr2 xp)

has-decidability-search-has-pointed-decidability-search :
  {l : Level} {X : UU l} →
  has-pointed-decidability-search X → has-decidability-search X
has-decidability-search-has-pointed-decidability-search {X = X} f P =
  map-coproduct
    ( pair (pr1 (f P)))
    ( λ np xp → np TODO)
    ( is-decidable-decidable-family P (pr1 (f P)))
 where postulate TODO : _ -- TODO

```

### Decidability search transfers along double negation dense maps

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (h : X ↠¬¬ Y)
  where

  has-decidability-search-double-negation-dense-map :
    has-decidability-search X → has-decidability-search Y
  has-decidability-search-double-negation-dense-map f P =
    map-coproduct
      ( λ xp → map-double-negation-dense-map h (pr1 xp) , pr2 xp)
      ( λ nxpf yp →
        is-double-negation-dense-map-double-negation-dense-map
          ( h)
          ( pr1 yp)
          ( λ xr →
            nxpf
              ( pr1 xr ,
                tr (family-decidable-family P) (inv (pr2 xr)) (pr2 yp))))
      ( f (reindex-decidable-family P (map-double-negation-dense-map h)))
```

### Decidability search transfers along surjections

```agda
has-decidability-search-surjection :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → X ↠ Y →
  has-decidability-search X → has-decidability-search Y
has-decidability-search-surjection h =
  has-decidability-search-double-negation-dense-map
    ( double-negation-dense-map-surjection h)
```

### Types with decidability search are closed under retracts

```agda
has-decidability-search-retract :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  Y retract-of X → has-decidability-search X → has-decidability-search Y
has-decidability-search-retract R =
  has-decidability-search-double-negation-dense-map
    ( double-negation-dense-map-retract R)
```

### Types with decidability search are closed under equivalences

```agda
has-decidability-search-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  Y ≃ X → has-decidability-search X → has-decidability-search Y
has-decidability-search-equiv e =
  has-decidability-search-retract (retract-equiv e)

has-decidability-search-equiv' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  X ≃ Y → has-decidability-search X → has-decidability-search Y
has-decidability-search-equiv' e =
  has-decidability-search-retract (retract-inv-equiv e)
```

### Decidable types that are irrefutably π₀-trivial have decidability search

```agda
has-decidability-search-is-decidable-all-elements-irrefutably-equal :
  {l1 : Level} {X : UU l1} → all-elements-irrefutably-equal X →
  is-decidable X → has-decidability-search X
has-decidability-search-is-decidable-all-elements-irrefutably-equal H d P =
  is-decidable-Σ-all-elements-irrefutably-equal-base H d
    ( is-decidable-decidable-family P)
```

**Comment.** It might suffice for the above result that `X` is inhabited or
empty.

### Decidable subtypes of types with decidability search have decidability search

```agda
has-decidability-search-type-decidable-subtype :
  {l1 l2 : Level} {X : UU l1} →
  has-decidability-search X →
  (P : decidable-subtype l2 X) →
  has-decidability-search (type-decidable-subtype P)
has-decidability-search-type-decidable-subtype {X = X} f P Q =
  is-decidable-equiv
    ( associative-Σ X (is-in-decidable-subtype P) (family-decidable-family Q))
    ( f ( comp-decidable-family-decidable-subtype P
          ( reindex-decidable-family Q ∘ pair)))

has-decidability-search-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  has-decidability-search X → Y ↪ᵈ X → has-decidability-search Y
has-decidability-search-decidable-emb f h =
  has-decidability-search-equiv'
    ( compute-type-decidable-subtype-decidable-emb h)
    ( has-decidability-search-type-decidable-subtype f
      ( decidable-subtype-decidable-emb h))
```

### The empty type has decidability search

```agda
has-decidability-search-empty : has-decidability-search empty
has-decidability-search-empty P = inr pr1
```

### The unit type has decidability search

```agda
has-decidability-search-unit : has-decidability-search unit
has-decidability-search-unit P =
  rec-coproduct
    ( inl ∘ pair star)
    ( inr ∘ map-neg pr2)
    ( is-decidable-decidable-family P star)
```

### Coproducts of types with decidability search

Coproducts of types with decidability search have decidability search.
Conversely, if the coproduct has decidability search and a summand has an
element, then that summand also has decidability search.

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  has-decidability-search-coproduct :
    has-decidability-search X →
    has-decidability-search Y →
    has-decidability-search (X + Y)
  has-decidability-search-coproduct f g P =
    rec-coproduct
      ( λ xp → inl (inl (pr1 xp) , pr2 xp))
      ( λ nx →
        rec-coproduct
          ( λ yp → inl (inr (pr1 yp) , pr2 yp))
          ( λ ny →
            inr
              ( λ where
                (inl x , p) → nx (x , p)
                (inr y , p) → ny (y , p)))
          ( g (reindex-decidable-family P inr)))
      ( f (reindex-decidable-family P inl))

  has-decidability-search-left-summand-coproduct :
    has-decidability-search (X + Y) →
    X → has-decidability-search X
  has-decidability-search-left-summand-coproduct f x =
    has-decidability-search-retract (retract-left-summand-coproduct x) f

  has-decidability-search-right-summand-coproduct :
    has-decidability-search (X + Y) →
    Y → has-decidability-search Y
  has-decidability-search-right-summand-coproduct f y =
    has-decidability-search-retract (retract-right-summand-coproduct y) f
```

### Dependent sums of types with decidability search

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  has-decidability-search-Σ :
    has-decidability-search A →
    ((x : A) → has-decidability-search (B x)) →
    has-decidability-search (Σ A B)
  has-decidability-search-Σ f g {l} P =
    is-decidable-equiv
      ( associative-Σ A B (family-decidable-family P))
      ( f ( ( λ x → Σ (B x) (λ y → family-decidable-family P (x , y))) ,
            ( λ x → g x (reindex-decidable-family P (λ b → (x , b))))))
```

### The total space of decidable irrefutably π₀-trivial families over types with decidability search have decidability search

```agda
abstract
  has-decidability-search-Σ-decidable-family-all-elements-irrefutably-equal :
    {l1 l2 : Level} {X : UU l1} →
    has-decidability-search X →
    (P : decidable-family l2 X) →
    ((x : X) → all-elements-irrefutably-equal (family-decidable-family P x)) →
    has-decidability-search (Σ X (family-decidable-family P))
  has-decidability-search-Σ-decidable-family-all-elements-irrefutably-equal
    f P H =
    has-decidability-search-Σ f
      ( λ x →
        has-decidability-search-is-decidable-all-elements-irrefutably-equal
          ( H x)
          ( is-decidable-decidable-family P x))
```

### Dependent sums of types with decidability search

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  has-decidability-search-base-has-decidability-search-Σ :
    has-decidability-search (Σ A B) →
    ((x : A) → B x) →
    has-decidability-search A
  has-decidability-search-base-has-decidability-search-Σ f s =
    has-decidability-search-retract (retract-base-Σ-section-family s) f
```

### Products of types with decidability search

```agda
has-decidability-search-product :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidability-search A →
  has-decidability-search B →
  has-decidability-search (A × B)
has-decidability-search-product f g = has-decidability-search-Σ f (λ _ → g)
```

### Factors of products with decidability search

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  has-decidability-search-left-factor-product :
    has-decidability-search (X × Y) →
    Y → has-decidability-search X
  has-decidability-search-left-factor-product f y =
    has-decidability-search-retract (retract-left-factor-product y) f

  has-decidability-search-right-factor-product :
    has-decidability-search (X × Y) →
    X → has-decidability-search Y
  has-decidability-search-right-factor-product f x =
    has-decidability-search-retract (retract-right-factor-product x) f
```

### Standard finite types have decidability search

```agda
has-decidability-search-Fin : (n : ℕ) → has-decidability-search (Fin n)
has-decidability-search-Fin zero-ℕ = has-decidability-search-empty
has-decidability-search-Fin (succ-ℕ n) =
  has-decidability-search-coproduct
    ( has-decidability-search-Fin n)
    ( has-decidability-search-unit)
```

### Types equipped with a counting have decidability search

```agda
has-decidability-search-count :
  {l : Level} {X : UU l} → count X → has-decidability-search X
has-decidability-search-count f =
  has-decidability-search-equiv'
    ( equiv-count f)
    ( has-decidability-search-Fin (number-of-elements-count f))
```

### The booleans have decidability search

```agda
has-decidability-search-bool' : has-decidability-search bool
has-decidability-search-bool' =
  has-decidability-search-equiv'
    ( equiv-bool-Fin-two-ℕ)
    ( has-decidability-search-Fin 2)
```

### The subuniverse of propositions has decidability search

```agda
-- has-decidability-search-Prop : {l : Level} → has-decidability-search (Prop l)
-- has-decidability-search-Prop {l} P =
--   rec-coproduct
--     ( λ p → inl (raise-unit-Prop l , p))
--     ( λ np →
--       rec-coproduct
--         ( λ q → inl (raise-empty-Prop l , q))
--         (λ nq → inr {!   !})
--         ( is-decidable-decidable-family P (raise-empty-Prop l)))
--     ( is-decidable-decidable-family P (raise-unit-Prop l))
```

### Subuniverses of propositions have decidability search

> TODO
