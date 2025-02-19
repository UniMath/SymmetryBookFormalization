# Function types

```agda
module foundation-core.function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "function"}} is a way of associating to each element $x$ of a domain type an element $f(x)$ of a type $B(x)$, which possibly depends on the input $x$. Functions are primitive in Agda. In this file we construct some basic functions.

The term "function" was first coined by Leibniz, who used the term to describe quantities related to curves, such as slopes, tangents, and
areas. The concept of functions was first given a precise definition by Euler {{#cite Euler1748}} in paragraph 4 of Chapter 1. Euler also introduced the now familiar notation $f(x)$ for functions.

## Examples

### The identity function

```agda
id : {l : Level} {A : UU l} → A → A
id a = a

id' : {l : Level} (A : UU l) → A → A
id' A = id

idω : {A : UUω} → A → A
idω a = a
```

### Dependent composition of functions

```agda
infixr 15 _∘_

_∘_ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (a : A) → B a → UU l3} →
  ({a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ f) a = g (f a)
```

### Evaluation at a point

```agda
ev-point :
  {l1 l2 : Level} {A : UU l1} (a : A) {P : A → UU l2} → ((x : A) → P x) → P a
ev-point a f = f a

ev-point' :
  {l1 l2 : Level} {A : UU l1} (a : A) {X : UU l2} → (A → X) → X
ev-point' a f = f a
```

### Postcomposition functions

```agda
map-Π :
  {l1 l2 l3 : Level}
  {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) →
  ((i : I) → A i) →
  ((i : I) → B i)
map-Π f h i = f i (h i)

map-Π' :
  {l1 l2 l3 l4 : Level}
  {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) →
  ((i : I) → A i → B i) →
  ((j : J) → A (α j)) →
  ((j : J) → B (α j))
map-Π' α f = map-Π (f ∘ α)

map-implicit-Π :
  {l1 l2 l3 : Level}
  {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) →
  ({i : I} → A i) →
  ({i : I} → B i)
map-implicit-Π f h {i} = map-Π f (λ i → h {i}) i
```

## See also

- [Postcomposition](foundation.postcomposition-functions.md)
- [Precomposition](foundation.precomposition-functions.md)

### Table of files about function types, composition, and equivalences

{{#include tables/composition.md}}
