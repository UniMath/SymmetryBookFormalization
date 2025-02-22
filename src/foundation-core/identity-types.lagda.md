# Identity types

```agda
module foundation-core.identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Idea

The {{#concept "equality" Agda=Id}} relation is defined in type theory by the
{{#concept "identity type" Agda=Id}}. The identity type on a type `A` is a
binary family of types

```text
  Id : A → A → 𝒰
```

equipped with a
{{#concept "reflexivity element" Disambiguation="identity type" Agda=refl}}

```text
  refl : (x : A) → Id x x.
```

In other words, the identity type is a reflexive
[type valued relation](foundation.binary-relations.md) on `A`. Furthermore, the
identity type on `A` satisfies the
[universal property](foundation.universal-property-identity-types.md) that it
maps uniquely into any other reflexive relation.

In type theory, we introduce the identity type as an inductive family of types,
where the induction principle can be understood as expressing that the identity
type is the least reflexive relation.

### Notation of the identity type

We include two notations for the identity type. First, we introduce the identity
type using Martin-Löf's original notation `Id`. Then we introduce as a secondary
option the infix notation `_＝_`.

**Note**: The equals sign in the infix notation is not the standard equals sign
on your keyboard, but it is the
[full width equals sign](https://codepoints.net/U+ff1d). Note that the full
width equals sign is slightly wider, and it is highlighted like all the other
defined constructions in Agda. In order to type the full width equals sign in
Agda's Emacs Mode, you need to add it to your agda input method as follows:

- Type `M-x customize-variable` and press enter.
- Type `agda-input-user-translations` and press enter.
- Click the `INS` button
- Type the regular equals sign `=` in the Key sequence field.
- Click the `INS` button
- Type the full width equals sign `＝` in the translations field.
- Click the `Apply and save` button.

After completing these steps, you can type `\=` in order to obtain the full
width equals sign `＝`.

## Table of files directly related to identity types

The following table lists files that are about identity types and operations on
identifications in arbitrary types.

{{#include tables/identity-types.md}}

## Definition

### Identity types

We introduce identity types as a `data` type. This is Agda's mechanism of
introducing types equipped with induction principles. The only constructor of
the identity type `Id x : A → 𝒰` is the reflexivity identification

```text
  refl : Id x x.
```

```agda
module _
  {l : Level} {A : UU l}
  where

  data Id (x : A) : A → UU l where
    instance refl : Id x x

  infix 6 _＝_
  _＝_ : A → A → UU l
  (a ＝ b) = Id a b

{-# BUILTIN EQUALITY Id #-}
```

We marked `refl` as an `instance` to enable Agda to automatically insert `refl`
in definitions that make use of Agda's
[instance search mechanism](https://agda.readthedocs.io/en/latest/language/instance-arguments.html).

Furthermore, we marked the identity type as
[`BUILTIN`](https://agda.readthedocs.io/en/latest/language/built-ins.html) in
order to support faster type checking.

### The induction principle of identity types

The induction principle of identity types states that given a base point `x : A`
and a family of types over the identity types based at `x`,
`B : (y : A) (p : x ＝ y) → UU l2`, then to construct a dependent function
`f : (y : A) (p : x ＝ y) → B y p` it suffices to define it at `f x refl`.

Note that Agda's pattern matching machinery allows us to define many operations
on the identity type directly. However, sometimes it is useful to explicitly
have the induction principle of the identity type.

```agda
ind-Id :
  {l1 l2 : Level} {A : UU l1}
  (x : A) (B : (y : A) (p : x ＝ y) → UU l2) →
  (B x refl) → (y : A) (p : x ＝ y) → B y p
ind-Id x B b y refl = b
```

## Operations on the identity type

The identity types form a weak groupoidal structure on types. Thus they come
equipped with
{{#concept "concatenation" Disambiguation="identifications" Agda=concat}}
`(x ＝ y) → (y ＝ z) → (x ＝ z)` and an
{{#concept "inverse" Disambiguation="identification" Agda=inv}} operation
`(x ＝ y) → (y ＝ x)`.

There are many more operations on identity types. Some of them are defined in
[path algebra](foundation.path-algebra.md) and
[whiskering of identifications](foundation.whiskering-identifications-concatenation.md).
For a complete reference to all the files about general identity types, see the
table given above.

### Concatenation of identifications

The
{{#concept "concatenation operation on identifications" Agda=_∙_ Agda=_∙'_ Agda=concat}}
is a family of binary operations

```text
  _∙_ : x ＝ y → y ＝ z → x ＝ z
```

indexed by `x y z : A`. However, there are essentially three different ways we
can define concatenation of identifications, all with different computational
behaviours.

1. We can define concatenation by induction on the equality `x ＝ y`. This gives
   us the computation rule `refl ∙ q ≐ q`.
2. We can define concatenation by induction on the equality `y ＝ z`. This gives
   us the computation rule `p ∙ refl ≐ p`.
3. We can define concatenation by induction on both `x ＝ y` and `y ＝ z`. This
   only gives us the computation rule `refl ∙ refl ≐ refl`.

While the third option may be preferred by some for its symmetry, for practical
reasons, we prefer one of the first two, and by convention we use the first
alternative.

The second option is considered in
[`foundation.strictly-right-unital-concatenation-identifications`](foundation.strictly-right-unital-concatenation-identifications.md),
and in [`foundation.yoneda-identity-types`](foundation.yoneda-identity-types.md)
we construct an identity type which satisfies both computation rules among
others.

```agda
module _
  {l : Level} {A : UU l}
  where

  infixl 15 _∙_
  _∙_ : {x y z : A} → x ＝ y → y ＝ z → x ＝ z
  refl ∙ q = q

  concat : {x y : A} → x ＝ y → (z : A) → y ＝ z → x ＝ z
  concat p z q = p ∙ q

  concat' : (x : A) {y z : A} → y ＝ z → x ＝ y → x ＝ z
  concat' x q p = p ∙ q
```

### Inverting identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  inv : {x y : A} → x ＝ y → y ＝ x
  inv refl = refl
```

### Concatenating with inverse identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  inv-concat : {x y : A} (p : x ＝ y) (z : A) → x ＝ z → y ＝ z
  inv-concat p = concat (inv p)

  inv-concat' : (x : A) {y z : A} → y ＝ z → x ＝ z → x ＝ y
  inv-concat' x q = concat' x (inv q)
```

## Properties

### Associativity of concatenation

For any three identifications `p : x ＝ y`, `q : y ＝ z`, and `r : z ＝ w`, we
have an identification

```text
  assoc p q r : ((p ∙ q) ∙ r) ＝ (p ∙ (q ∙ r)).
```

The identification `assoc p q r` is also called the
{{#concept "associator" Disambiguation="identification" Agda=assoc}}.

Note that the associator `assoc p q r` is an identification in the type
`x ＝ w`, i.e., it is an identification of identifications. Here we make crucial
use of the fact that the identity types are defined _for all types_. In other
words, since identity types are themselves types, we can consider identity types
of identity types, and so on.

#### Associators

```agda
module _
  {l : Level} {A : UU l}
  where

  assoc :
    {x y z w : A} (p : x ＝ y) (q : y ＝ z) (r : z ＝ w) →
    ((p ∙ q) ∙ r) ＝ (p ∙ (q ∙ r))
  assoc refl q r = refl
```

### The unit laws for concatenation

For any identification `p : x ＝ y` there is an identification

```text
  left-unit : (refl ∙ p) ＝ p.
```

Similarly, there is an identification

```text
  right-unit : (p ∙ refl) ＝ p.
```

In other words, the reflexivity identification is a unit element for
concatenation of identifications.

```agda
module _
  {l : Level} {A : UU l}
  where

  double-assoc :
    {x y z w v : A} (p : x ＝ y) (q : y ＝ z) (r : z ＝ w) (s : w ＝ v) →
    (((p ∙ q) ∙ r) ∙ s) ＝ p ∙ (q ∙ (r ∙ s))
  double-assoc refl q r s = assoc q r s

  triple-assoc :
    {x y z w v u : A}
    (p : x ＝ y) (q : y ＝ z) (r : z ＝ w) (s : w ＝ v) (t : v ＝ u) →
    ((((p ∙ q) ∙ r) ∙ s) ∙ t) ＝ p ∙ (q ∙ (r ∙ (s ∙ t)))
  triple-assoc refl q r s t = double-assoc q r s t
```

#### Unit laws

```agda
  left-unit : {x y : A} {p : x ＝ y} → refl ∙ p ＝ p
  left-unit = refl

  right-unit : {x y : A} {p : x ＝ y} → p ∙ refl ＝ p
  right-unit {p = refl} = refl
```

### The inverse laws for concatenation

```agda
module _
  {l : Level} {A : UU l}
  where

  left-inv : {x y : A} (p : x ＝ y) → inv p ∙ p ＝ refl
  left-inv refl = refl

  right-inv : {x y : A} (p : x ＝ y) → p ∙ (inv p) ＝ refl
  right-inv refl = refl
```

### Inverting identifications is an involution

```agda
module _
  {l : Level} {A : UU l}
  where

  inv-inv : {x y : A} (p : x ＝ y) → inv (inv p) ＝ p
  inv-inv refl = refl
```

### Inverting identifications distributes over concatenation

```agda
module _
  {l : Level} {A : UU l}
  where

  distributive-inv-concat :
    {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z) →
    inv (p ∙ q) ＝ inv q ∙ inv p
  distributive-inv-concat refl refl = refl
```

### Concatenating with an inverse is inverse to concatenating

We show that the operation `q ↦ inv p ∙ q` is inverse to the operation
`q ↦ p ∙ q` by constructing identifications

```text
  inv p ∙ (p ∙ q) ＝ q
  p ∙ (inv p ∙ q) ＝ q.
```

Similarly, we show that the operation `p ↦ p ∙ inv q` is inverse to the
operation `p ↦ p ∙ q` by constructing identifications

```text
  (p ∙ q) ∙ inv q ＝ p
  (p ∙ inv q) ∙ q ＝ p.
```

In [`foundation.identity-types`](foundation.identity-types.md) we will use these
families of identifications to conclude that `concat p z` and `concat' x q` are
[equivalences](foundation-core.equivalences.md) with inverses `concat (inv p) z`
and `concat' x (inv q)`, respectively.

```agda
module _
  {l : Level} {A : UU l}
  where

  is-retraction-inv-concat :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) → (inv p ∙ (p ∙ q)) ＝ q
  is-retraction-inv-concat refl q = refl

  is-section-inv-concat :
    {x y z : A} (p : x ＝ y) (r : x ＝ z) → (p ∙ (inv p ∙ r)) ＝ r
  is-section-inv-concat refl r = refl

  is-retraction-inv-concat' :
    {x y z : A} (q : y ＝ z) (p : x ＝ y) → (p ∙ q) ∙ inv q ＝ p
  is-retraction-inv-concat' refl refl = refl

  is-section-inv-concat' :
    {x y z : A} (q : y ＝ z) (r : x ＝ z) → (r ∙ inv q) ∙ q ＝ r
  is-section-inv-concat' refl refl = refl
```

### Transposing inverses

Consider a triangle of identifications

```text
      p
  x ----> y
   \     /
  r \   / q
     ∨ ∨
      z
```

in a type `A`. Then we have maps

```text
  p ∙ q ＝ r → q ＝ inv p ∙ r
  p ∙ q ＝ r → p ＝ r ∙ inv q.
```

In [`foundation.identity-types`](foundation.identity-types.md) we will show that
these maps are equivalences.

```agda
module _
  {l : Level} {A : UU l}
  where

  left-transpose-eq-concat :
    {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z) (r : x ＝ z) →
    p ∙ q ＝ r → q ＝ inv p ∙ r
  left-transpose-eq-concat refl q r s = s

  inv-left-transpose-eq-concat :
    {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z) (r : x ＝ z) →
    q ＝ inv p ∙ r → p ∙ q ＝ r
  inv-left-transpose-eq-concat refl q r s = s

  right-transpose-eq-concat :
    {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z) (r : x ＝ z) →
    p ∙ q ＝ r → p ＝ r ∙ inv q
  right-transpose-eq-concat p refl r s = (inv right-unit ∙ s) ∙ inv right-unit

  inv-right-transpose-eq-concat :
    {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z) (r : x ＝ z) →
    p ＝ r ∙ inv q → p ∙ q ＝ r
  inv-right-transpose-eq-concat p refl r s = right-unit ∙ (s ∙ right-unit)

  double-transpose-eq-concat :
    {x y u v : A} (r : x ＝ u) (p : x ＝ y) (s : u ＝ v) (q : y ＝ v) →
    p ∙ q ＝ r ∙ s → inv r ∙ p ＝ s ∙ inv q
  double-transpose-eq-concat refl p s refl α =
    (inv right-unit ∙ α) ∙ inv right-unit

  double-transpose-eq-concat' :
    {x y u v : A} (r : x ＝ u) (p : x ＝ y) (s : u ＝ v) (q : y ＝ v) →
    p ∙ q ＝ r ∙ s → q ∙ inv s ＝ inv p ∙ r
  double-transpose-eq-concat' r refl refl q α = right-unit ∙ (α ∙ right-unit)
```

### Splicing and unsplicing concatenations of identifications

Consider two identifications `p : a ＝ b` and `q : b ＝ c`, and consider two
further identifications `r : b ＝ x` and `s : x ＝ b` equipped with an
identification `inv r ＝ s`, as indicated in the diagram

```text
           x
          ∧ |
        r | | s
          | ∨
  a -----> b -----> c.
```

Then we have identifications

```text
    splice-concat : p ∙ q ＝ (p ∙ r) ∙ (s ∙ q)
  unsplice-concat : (p ∙ r) ∙ (s ∙ q) ＝ p ∙ q.
```

```agda
module _
  {l : Level} {A : UU l}
  where

  splice-concat :
    {a b c x : A}
    (p : a ＝ b) {r : b ＝ x} {s : x ＝ b} (α : inv r ＝ s) (q : b ＝ c) →
    p ∙ q ＝ (p ∙ r) ∙ (s ∙ q)
  splice-concat refl {r} refl q = inv (is-section-inv-concat r q)

  splice-concat' :
    {a b c x : A}
    (p : a ＝ b) {r : b ＝ x} {s : x ＝ b} (α : r ＝ inv s) (q : b ＝ c) →
    p ∙ q ＝ (p ∙ r) ∙ (s ∙ q)
  splice-concat' refl {.(inv s)} {s} refl q = inv (is-retraction-inv-concat s q)

  unsplice-concat :
    {a b c x : A}
    (p : a ＝ b) {r : b ＝ x} {s : x ＝ b} (α : inv r ＝ s) (q : b ＝ c) →
    (p ∙ r) ∙ (s ∙ q) ＝ p ∙ q
  unsplice-concat p α q = inv (splice-concat p α q)

  unsplice-concat' :
    {a b c x : A}
    (p : a ＝ b) {r : b ＝ x} {s : x ＝ b} (α : r ＝ inv s) (q : b ＝ c) →
    (p ∙ r) ∙ (s ∙ q) ＝ p ∙ q
  unsplice-concat' p α q = inv (splice-concat' p α q)
```

### Concatenation is injective

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  is-injective-concat :
    {x y z : A} (p : x ＝ y) {q r : y ＝ z} → p ∙ q ＝ p ∙ r → q ＝ r
  is-injective-concat refl s = s

  is-injective-concat' :
    {x y z : A} (r : y ＝ z) {p q : x ＝ y} → p ∙ r ＝ q ∙ r → p ＝ q
  is-injective-concat' refl s = (inv right-unit) ∙ (s ∙ right-unit)
```

## Equational reasoning

Identifications can be constructed by equational reasoning in the following way:

```text
equational-reasoning
  x ＝ y by eq-1
    ＝ z by eq-2
    ＝ v by eq-3
```

The resulting identification of this computation is `eq-1 ∙ (eq-2 ∙ eq-3)`,
i.e., the identification is associated fully to the right. For examples of the
use of equational reasoning, see
[addition-integers](elementary-number-theory.addition-integers.md).

```agda
infixl 1 equational-reasoning_
infixl 0 step-equational-reasoning

equational-reasoning_ :
  {l : Level} {X : UU l} (x : X) → x ＝ x
equational-reasoning x = refl

step-equational-reasoning :
  {l : Level} {X : UU l} {x y : X} →
  (x ＝ y) → (u : X) → (y ＝ u) → (x ＝ u)
step-equational-reasoning p z q = p ∙ q

syntax step-equational-reasoning p z q = p ＝ z by q
```

**Note.** Equational reasoning is a convenient way to construct identifications.
However, in some situations it may not be the fastest or cleanest mechanism to
construct an identification. Some constructions of identifications naturally
involve computations that are more deeply nested in the terms. Furthermore,
proofs by equational reasoning tend to require a lot of reassociation.

Some tools that allow us to perform faster computations are the transpositions
defined above, the transpositions and splicing operations defined in
[commuting squares of identifications](foundation.commuting-squares-of-identifications.md)
and
[commuting triangles of identifications](foundation.commuting-triangles-of-identifications.md),
and the higher concatenation operations defined in
[path algebra](foundation.path-algebra.md). Each of these operations has good
computational behavior, so there is infrastructure for reasoning about
identifications that are constructed using them.

We also note that there is similar infrastructure for
[homotopy reasoning](foundation-core.homotopies.md).

## References

Our setup of equational reasoning is derived from the following sources:

1. Martín Escardó.
   <https://github.com/martinescardo/TypeTopology/blob/master/source/Id.lagda>

2. Martín Escardó.
   <https://github.com/martinescardo/TypeTopology/blob/master/source/UF-Equiv.lagda>

3. The Agda standard library.
   <https://github.com/agda/agda-stdlib/blob/master/src/Relation/Binary/PropositionalEquality/Core.agda>
