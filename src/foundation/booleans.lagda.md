# The booleans

```agda
module foundation.booleans where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.involutions
open import foundation.negated-equality
open import foundation.raising-universe-levels
open import foundation.tight-apartness-relations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.coproduct-types
open import foundation-core.decidable-propositions
open import foundation-core.double-negation-stable-equality
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.negation
open import foundation-core.propositions
open import foundation-core.sections
open import foundation-core.sets

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The type of {{#concept "booleans" WD="Boolean domain" WDID=Q3269980 Agda=bool}}
is a [2-element type](univalent-combinatorics.2-element-types.md) with elements
`true false : bool`, which is used for reasoning with
[decidable propositions](foundation-core.decidable-propositions.md).

## Definition

### The booleans

```agda
data bool : UU lzero where
  true false : bool

{-# BUILTIN BOOL bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}
```

### The induction principle of the booleans

```agda
module _
  {l : Level} (P : bool → UU l)
  where

  ind-bool : P true → P false → (b : bool) → P b
  ind-bool pt pf true = pt
  ind-bool pt pf false = pf
```

### The recursion principle of the booleans

```agda
module _
  {l : Level} {P : UU l}
  where

  rec-bool : P → P → bool → P
  rec-bool = ind-bool (λ _ → P)
```

### The `if_then_else` function

```agda
module _
  {l : Level} {A : UU l}
  where

  if_then_else_ : bool → A → A → A
  if b then x else y = rec-bool x y b
```

### Raising universe levels of the booleans

```agda
raise-bool : (l : Level) → UU l
raise-bool l = raise l bool

raise-true : (l : Level) → raise-bool l
raise-true l = map-raise true

raise-false : (l : Level) → raise-bool l
raise-false l = map-raise false

compute-raise-bool : (l : Level) → bool ≃ raise-bool l
compute-raise-bool l = compute-raise l bool
```

### The standard propositions associated to the constructors of bool

```agda
prop-bool : bool → Prop lzero
prop-bool true = unit-Prop
prop-bool false = empty-Prop

type-prop-bool : bool → UU lzero
type-prop-bool = type-Prop ∘ prop-bool
```

### Equality on the booleans

```agda
Eq-bool : bool → bool → UU lzero
Eq-bool true true = unit
Eq-bool true false = empty
Eq-bool false true = empty
Eq-bool false false = unit

refl-Eq-bool : (x : bool) → Eq-bool x x
refl-Eq-bool true = star
refl-Eq-bool false = star

Eq-eq-bool :
  {x y : bool} → x ＝ y → Eq-bool x y
Eq-eq-bool {x = x} refl = refl-Eq-bool x

eq-Eq-bool :
  {x y : bool} → Eq-bool x y → x ＝ y
eq-Eq-bool {true} {true} star = refl
eq-Eq-bool {false} {false} star = refl

neq-false-true-bool : false ≠ true
neq-false-true-bool ()

neq-true-false-bool : true ≠ false
neq-true-false-bool ()

is-decidable-Eq-bool : {x y : bool} → is-decidable (Eq-bool x y)
is-decidable-Eq-bool {true} {true} = inl star
is-decidable-Eq-bool {true} {false} = inr id
is-decidable-Eq-bool {false} {true} = inr id
is-decidable-Eq-bool {false} {false} = inl star
```

### The standard interpretation of booleans as decidable propositions

```agda
decidable-prop-bool : bool → Decidable-Prop lzero
decidable-prop-bool true = unit-Decidable-Prop
decidable-prop-bool false = empty-Decidable-Prop
```

## Properties

### The booleans are a set

```agda
abstract
  is-prop-Eq-bool : (x y : bool) → is-prop (Eq-bool x y)
  is-prop-Eq-bool true true = is-prop-unit
  is-prop-Eq-bool true false = is-prop-empty
  is-prop-Eq-bool false true = is-prop-empty
  is-prop-Eq-bool false false = is-prop-unit

abstract
  is-set-bool : is-set bool
  is-set-bool =
    is-set-prop-in-id
      ( Eq-bool)
      ( is-prop-Eq-bool)
      ( refl-Eq-bool)
      ( λ x y → eq-Eq-bool)

bool-Set : Set lzero
bool-Set = bool , is-set-bool
```

### The booleans have decidable equality

```agda
has-decidable-equality-bool : has-decidable-equality bool
has-decidable-equality-bool true true = inl refl
has-decidable-equality-bool true false = inr neq-true-false-bool
has-decidable-equality-bool false true = inr neq-false-true-bool
has-decidable-equality-bool false false = inl refl

bool-Discrete-Type : Discrete-Type lzero
bool-Discrete-Type = bool , has-decidable-equality-bool

has-double-negation-stable-equality-bool :
  has-double-negation-stable-equality bool
has-double-negation-stable-equality-bool x y =
  double-negation-elim-is-decidable (has-decidable-equality-bool x y)
```

### The booleans have a tight apartness relation

```agda
bool-Type-With-Tight-Apartness : Type-With-Tight-Apartness lzero lzero
bool-Type-With-Tight-Apartness =
  type-with-tight-apartness-Discrete-Type bool-Discrete-Type
```

### The "is true" predicate on booleans

```agda
is-true : bool → UU lzero
is-true = _＝ true

is-prop-is-true : (b : bool) → is-prop (is-true b)
is-prop-is-true b = is-set-bool b true

is-true-Prop : bool → Prop lzero
is-true-Prop b = (is-true b , is-prop-is-true b)

is-decidable-prop-is-true : (b : bool) → is-decidable-prop (is-true b)
is-decidable-prop-is-true b =
  ( is-prop-is-true b , has-decidable-equality-bool b true)

is-true-Decidable-Prop : bool → Decidable-Prop lzero
is-true-Decidable-Prop b = (is-true b , is-decidable-prop-is-true b)
```

### The "is false" predicate on booleans

```agda
is-false : bool → UU lzero
is-false = _＝ false

is-prop-is-false : (b : bool) → is-prop (is-false b)
is-prop-is-false b = is-set-bool b false

is-false-Prop : bool → Prop lzero
is-false-Prop b = is-false b , is-prop-is-false b

is-decidable-prop-is-false : (b : bool) → is-decidable-prop (is-false b)
is-decidable-prop-is-false b =
  ( is-prop-is-false b , has-decidable-equality-bool b false)

is-false-Decidable-Prop : bool → Decidable-Prop lzero
is-false-Decidable-Prop b = (is-false b , is-decidable-prop-is-false b)
```

### A boolean cannot be both true and false

```agda
is-not-false-is-true : (x : bool) → is-true x → ¬ (is-false x)
is-not-false-is-true true t ()
is-not-false-is-true false () f

is-not-true-is-false : (x : bool) → is-false x → ¬ (is-true x)
is-not-true-is-false true () f
is-not-true-is-false false t ()

is-false-is-not-true : (x : bool) → ¬ (is-true x) → is-false x
is-false-is-not-true true np = ex-falso (np refl)
is-false-is-not-true false np = refl

is-true-is-not-false : (x : bool) → ¬ (is-false x) → is-true x
is-true-is-not-false true np = refl
is-true-is-not-false false np = ex-falso (np refl)

contrapositive-is-true-bool :
  {x y : bool} → (is-true x → is-true y) → is-false y → is-false x
contrapositive-is-true-bool {x} f refl =
  is-false-is-not-true x (neq-false-true-bool ∘ f)

contrapositive-is-false-bool :
  {x y : bool} → (is-false x → is-false y) → is-true y → is-true x
contrapositive-is-false-bool {x} f refl =
  is-true-is-not-false x (neq-true-false-bool ∘ f)
```

### The type of booleans is equivalent to `Fin 2`

```agda
bool-Fin-2 : Fin 2 → bool
bool-Fin-2 (inl (inr star)) = true
bool-Fin-2 (inr star) = false

Fin-2-bool : bool → Fin 2
Fin-2-bool true = inl (inr star)
Fin-2-bool false = inr star

abstract
  is-retraction-Fin-2-bool : Fin-2-bool ∘ bool-Fin-2 ~ id
  is-retraction-Fin-2-bool (inl (inr star)) = refl
  is-retraction-Fin-2-bool (inr star) = refl

abstract
  is-section-Fin-2-bool : bool-Fin-2 ∘ Fin-2-bool ~ id
  is-section-Fin-2-bool true = refl
  is-section-Fin-2-bool false = refl

equiv-bool-Fin-2 : Fin 2 ≃ bool
pr1 equiv-bool-Fin-2 = bool-Fin-2
pr2 equiv-bool-Fin-2 =
  is-equiv-is-invertible
    ( Fin-2-bool)
    ( is-section-Fin-2-bool)
    ( is-retraction-Fin-2-bool)
```

### The type of booleans is finite

```agda
is-finite-bool : is-finite bool
is-finite-bool = is-finite-equiv equiv-bool-Fin-2 (is-finite-Fin 2)

number-of-elements-bool : number-of-elements-is-finite is-finite-bool ＝ 2
number-of-elements-bool =
  inv
    ( compute-number-of-elements-is-finite
      ( 2 , equiv-bool-Fin-2)
      ( is-finite-bool))

bool-Finite-Type : Finite-Type lzero
pr1 bool-Finite-Type = bool
pr2 bool-Finite-Type = is-finite-bool
```

### The constant function `const bool b` is not an equivalence

```agda
abstract
  no-section-const-bool : (b : bool) → ¬ (section (const bool b))
  no-section-const-bool true (g , G) = neq-true-false-bool (G false)
  no-section-const-bool false (g , G) = neq-false-true-bool (G true)

abstract
  is-not-equiv-const-bool :
    (b : bool) → ¬ (is-equiv (const bool b))
  is-not-equiv-const-bool b e = no-section-const-bool b (section-is-equiv e)
```
