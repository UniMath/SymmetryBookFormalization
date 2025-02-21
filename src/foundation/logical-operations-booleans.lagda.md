# Logical operations on the booleans

```agda
module foundation.logical-operations-booleans where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.booleans
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

We consider basic logical operations on the booleans and prove standard facts
about them.

## Definitions

### Negation

```agda
neg-bool : bool → bool
neg-bool true = false
neg-bool false = true
```

### Conjunction

```agda
and-bool : bool → bool → bool
and-bool true y = y
and-bool false y = false
```

### Disjunction

```agda
or-bool : bool → bool → bool
or-bool true y = true
or-bool false y = y
```

### Implication

```agda
hom-bool : bool → bool → bool
hom-bool x = or-bool (neg-bool x)
```

### Exclusive disjunction

```agda
xor-bool : bool → bool → bool
xor-bool true y = neg-bool y
xor-bool false y = y
```

### Negated exclusive disjunction

```agda
xnor-bool : bool → bool → bool
xnor-bool true y = y
xnor-bool false y = neg-bool y
```

## Properties

### Boolean negation has no fixed points

```agda
neq-neg-bool : (b : bool) → b ≠ neg-bool b
neq-neg-bool true ()
neq-neg-bool false ()

neq-neg-bool' : (b : bool) → neg-bool b ≠ b
neq-neg-bool' b = neq-neg-bool b ∘ inv

is-true-is-false-neg-bool : {b : bool} → is-false (neg-bool b) → is-true b
is-true-is-false-neg-bool {true} p = refl

is-false-is-true-neg-bool : {b : bool} → is-true (neg-bool b) → is-false b
is-false-is-true-neg-bool {false} p = refl
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

### Basic properties of the or operation

```agda
left-unit-law-or-bool : {x : bool} → or-bool false x ＝ x
left-unit-law-or-bool = refl

right-unit-law-or-bool : {x : bool} → or-bool x false ＝ x
right-unit-law-or-bool {true} = refl
right-unit-law-or-bool {false} = refl

left-zero-law-or-bool : {x : bool} → or-bool true x ＝ true
left-zero-law-or-bool = refl

right-zero-law-or-bool : {x : bool} → or-bool x true ＝ true
right-zero-law-or-bool {true} = refl
right-zero-law-or-bool {false} = refl

idempotent-or-bool : {x : bool} → or-bool x x ＝ x
idempotent-or-bool {true} = refl
idempotent-or-bool {false} = refl

commutative-or-bool : {x y : bool} → or-bool x y ＝ or-bool y x
commutative-or-bool {true} {true} = refl
commutative-or-bool {true} {false} = refl
commutative-or-bool {false} {true} = refl
commutative-or-bool {false} {false} = refl

associative-or-bool :
  {x y z : bool} → or-bool (or-bool x y) z ＝ or-bool x (or-bool y z)
associative-or-bool {true} {y} {z} = refl
associative-or-bool {false} {y} {z} = refl
```

### Basic properties of the and operation

```agda
left-unit-law-and-bool : {x : bool} → and-bool true x ＝ x
left-unit-law-and-bool = refl

right-unit-law-and-bool : {x : bool} → and-bool x true ＝ x
right-unit-law-and-bool {true} = refl
right-unit-law-and-bool {false} = refl

left-zero-law-and-bool : {x : bool} → and-bool false x ＝ false
left-zero-law-and-bool = refl

right-zero-law-and-bool : {x : bool} → and-bool x false ＝ false
right-zero-law-and-bool {true} = refl
right-zero-law-and-bool {false} = refl

commutative-and-bool : {x y : bool} → and-bool x y ＝ and-bool y x
commutative-and-bool {true} {true} = refl
commutative-and-bool {true} {false} = refl
commutative-and-bool {false} {true} = refl
commutative-and-bool {false} {false} = refl

idempotent-and-bool : {x : bool} → and-bool x x ＝ x
idempotent-and-bool {true} = refl
idempotent-and-bool {false} = refl

associative-and-bool :
  {x y z : bool} → and-bool (and-bool x y) z ＝ and-bool x (and-bool y z)
associative-and-bool {true} {y} {z} = refl
associative-and-bool {false} {y} {z} = refl
```

### Basic properties of the implication operation

```agda
left-unit-law-hom-bool : {x : bool} → hom-bool true x ＝ x
left-unit-law-hom-bool = refl

right-neg-law-hom-bool : {x : bool} → hom-bool x false ＝ neg-bool x
right-neg-law-hom-bool {true} = refl
right-neg-law-hom-bool {false} = refl

left-zero-law-hom-bool : {x : bool} → hom-bool false x ＝ true
left-zero-law-hom-bool = refl

right-zero-law-hom-bool : {x : bool} → hom-bool x true ＝ true
right-zero-law-hom-bool {true} = refl
right-zero-law-hom-bool {false} = refl

compute-hom-self-bool : {x : bool} → hom-bool x x ＝ true
compute-hom-self-bool {true} = refl
compute-hom-self-bool {false} = refl
```

### Computing implication on connectives

```agda
compute-and-hom-bool :
  {x y z : bool} → hom-bool (and-bool x y) z ＝ hom-bool x (hom-bool y z)
compute-and-hom-bool {true} {y} {z} = refl
compute-and-hom-bool {false} {y} {z} = refl

compute-or-hom-bool :
  {x y z : bool} →
  hom-bool (or-bool x y) z ＝ and-bool (hom-bool x z) (hom-bool y z)
compute-or-hom-bool {true} {true} {true} = refl
compute-or-hom-bool {true} {false} {true} = refl
compute-or-hom-bool {true} {true} {false} = refl
compute-or-hom-bool {true} {false} {false} = refl
compute-or-hom-bool {false} {y} {z} = refl

distributive-hom-and-bool :
  {x y z : bool} →
  hom-bool x (and-bool y z) ＝ and-bool (hom-bool x y) (hom-bool x z)
distributive-hom-and-bool {true} {y} {z} = refl
distributive-hom-and-bool {false} {y} {z} = refl
```

### Distributivity of conjunction over disjunction

```agda
distributive-and-or-bool :
  {x y z : bool} →
  and-bool x (or-bool y z) ＝ or-bool (and-bool x y) (and-bool x z)
distributive-and-or-bool {true} = refl
distributive-and-or-bool {false} = refl
```

### Distributivity of disjunction over conjunction

```agda
distributive-or-and-bool :
  {x y z : bool} →
  or-bool x (and-bool y z) ＝ and-bool (or-bool x y) (or-bool x z)
distributive-or-and-bool {true} = refl
distributive-or-and-bool {false} = refl
```

### The law of excluded middle

```agda
law-of-excluded-middle-bool :
  {x : bool} → or-bool x (neg-bool x) ＝ true
law-of-excluded-middle-bool {true} = refl
law-of-excluded-middle-bool {false} = refl
```

### Double negation elimination

```agda
double-negation-elim-bool : {x : bool} → neg-bool (neg-bool x) ＝ x
double-negation-elim-bool {true} = refl
double-negation-elim-bool {false} = refl
```

### De Morgan's laws

```agda
de-morgans-law-bool :
  {x y : bool} → neg-bool (and-bool x y) ＝ or-bool (neg-bool x) (neg-bool y)
de-morgans-law-bool {true} = refl
de-morgans-law-bool {false} = refl

de-morgans-law-bool' :
  {x y : bool} → neg-bool (or-bool x y) ＝ and-bool (neg-bool x) (neg-bool y)
de-morgans-law-bool' {true} = refl
de-morgans-law-bool' {false} = refl
```
