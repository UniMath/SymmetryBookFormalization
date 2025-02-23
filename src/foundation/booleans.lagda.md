# The booleans

```agda
module foundation.booleans where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.involutions
open import foundation.negated-equality
open import foundation.raising-universe-levels
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.coproduct-types
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

The type of **booleans** is a
[2-element type](univalent-combinatorics.2-element-types.md) with elements
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
```

## Structure

### The boolean operators

```agda
neg-bool : bool → bool
neg-bool true = false
neg-bool false = true

conjunction-bool : bool → bool → bool
conjunction-bool true true = true
conjunction-bool true false = false
conjunction-bool false true = false
conjunction-bool false false = false

disjunction-bool : bool → bool → bool
disjunction-bool true true = true
disjunction-bool true false = true
disjunction-bool false true = true
disjunction-bool false false = false

implication-bool : bool → bool → bool
implication-bool true true = true
implication-bool true false = false
implication-bool false true = true
implication-bool false false = true
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
```

### The "is true" predicate on booleans

```agda
is-true : bool → UU lzero
is-true = _＝ true

is-prop-is-true : (b : bool) → is-prop (is-true b)
is-prop-is-true b = is-set-bool b true

is-true-Prop : bool → Prop lzero
is-true-Prop b = is-true b , is-prop-is-true b
```

### The "is false" predicate on booleans

```agda
is-false : bool → UU lzero
is-false = _＝ false

is-prop-is-false : (b : bool) → is-prop (is-false b)
is-prop-is-false b = is-set-bool b false

is-false-Prop : bool → Prop lzero
is-false-Prop b = is-false b , is-prop-is-false b
```

### A boolean cannot be both true and false

```agda
not-is-false-is-true : (x : bool) → is-true x → ¬ (is-false x)
not-is-false-is-true true t ()
not-is-false-is-true false () f

not-is-true-is-false : (x : bool) → is-false x → ¬ (is-true x)
not-is-true-is-false true () f
not-is-true-is-false false t ()
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

### Boolean negation has no fixed points

```agda
neq-neg-bool : (b : bool) → b ≠ neg-bool b
neq-neg-bool true ()
neq-neg-bool false ()

neq-neg-bool' : (b : bool) → neg-bool b ≠ b
neq-neg-bool' b = neq-neg-bool b ∘ inv
```

### Boolean negation is an involution

```agda
is-involution-neg-bool : is-involution neg-bool
is-involution-neg-bool true = refl
is-involution-neg-bool false = refl
```

### Boolean negation is an equivalence

```agda
abstract
  is-equiv-neg-bool : is-equiv neg-bool
  is-equiv-neg-bool = is-equiv-is-involution is-involution-neg-bool

equiv-neg-bool : bool ≃ bool
pr1 equiv-neg-bool = neg-bool
pr2 equiv-neg-bool = is-equiv-neg-bool
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

### The type of booleans is not contractible

```agda
abstract
  is-not-contractible-bool : ¬ (is-contr bool)
  is-not-contractible-bool (b , eq) = no-section-const-bool b (id , eq)
```

### The type of booleans is not equivalent to the unit type

```agda
abstract
  is-not-unit-bool : ¬ (bool ≃ unit)
  is-not-unit-bool e = is-not-contractible-bool (is-contr-equiv-unit e)
```
