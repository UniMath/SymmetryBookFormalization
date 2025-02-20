# Computational identity types

```agda
module foundation.computational-identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-extensionality
open import foundation.strictly-right-unital-concatenation-identifications
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universal-property-identity-systems
open import foundation.universe-levels
open import foundation.yoneda-identity-types

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.torsorial-type-families
```

</details>

## Idea

The standard definition of [identity types](foundation-core.identity-types.md)
has the limitation that many of the basic operations only satisfy algebraic laws
_weakly_. On this page, we consider the
{{#concept "computational identity types" Agda=computational-Id}} `x ＝ʲ y`,
whose elements we call
{{#concept "computational identifications" Agda=computational-Id}}. The
computational identity types are equivalent to the standard identity types, but
have strictly associative and one-sided unital concatenation and a strictly
involutive inverse operator.

The computational identity types are defined by taking the
[strictly involutive identity types](foundation.strictly-involutive-identity-types.md):

```text
  (x ＝ⁱ y) := Σ (z : A) ((z ＝ y) × (z ＝ x))
```

but using the [Yoneda identity types](foundation.yoneda-identity-types.md)

```text
  (x ＝ʸ y) := (z : A) → (z ＝ x) → (z ＝ y),
```

as the underlying identity types. Both of these underlying constructions are due
to Martín Escardó {{#cite Esc19DefinitionsEquivalence}}. Hence, the
_computational identity type_ is

```text
  (x ＝ʲ y) := Σ (z : A) ((z ＝ʸ y) × (z ＝ʸ x)).
```

Both the strictly involutive identity types and Yoneda identity types are
[equivalent](foundation-core.equivalences.md) to the standard identity types but
satisfy further strict algebraic laws. While the strictly involutive identity
types have a strictly involutive inverse operation and a one-sided unital
concatenation, the Yoneda identity types have a strictly associative two-sided
unital concatenation operation. We leverage this to define appropriate
operations on the computational identity types that satisfy the strict algebraic
laws

- `(p ∙ʲ q) ∙ʲ r ≐ p ∙ʲ (q ∙ʲ r)`
- `reflʲ ∙ʲ p ≐ p` or `p ∙ʲ reflʲ ≐ p`
- `invʲ (invʲ p) ≐ p`
- `invʲ reflʲ ≐ reflʲ`.

While the last three equalities hold by the same computations as for the
strictly involutive identity types using the fact that `invʸ reflʸ ≐ reflʸ`,
strict associativity relies on the strict associativity of the underlying Yoneda
identity types. See the page on strictly involutive identity types for further
details on computations related to the last three equalities. In addition to
these strict algebraic laws, we also have a recursion principle for the
computational identity types that computes strictly.

**Note.** The computational identity types do _not_ satisfy the strict laws

- `reflʲ ∙ʲ p ≐ p` and `p ∙ʲ reflʲ ≐ p` simultaneously,
- `invʲ p ∙ʲ p ≐ reflʲ`, or
- `p ∙ʲ invʲ p ≐ reflʲ`,

and they do not have a strict computation property for their induction
principle. This is a consequence of the fact that the Yoneda identity types do
not have a strict computation property for their induction principle, which is
explained further there.

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  computational-Id : (x y : A) → UU l
  computational-Id x y = Σ A (λ z → (z ＝ʸ y) × (z ＝ʸ x))

  infix 6 _＝ʲ_
  _＝ʲ_ : A → A → UU l
  (a ＝ʲ b) = computational-Id a b

  reflʲ : {x : A} → x ＝ʲ x
  reflʲ {x} = (x , reflʸ , reflʸ)
```

## Properties

### The computational identity types are equivalent to the Yoneda identity types

The computational identity types are equivalent to the Yoneda identity types,
and similarly to the strictly involutive identity types, this equivalence is a
strict [retraction](foundation-core.retractions.md) and preserves the
reflexivities strictly.

```agda
module _
  {l : Level} {A : UU l}
  where

  computational-eq-yoneda-eq : {x y : A} → x ＝ʸ y → x ＝ʲ y
  computational-eq-yoneda-eq {x} f = (x , f , reflʸ)

  yoneda-eq-computational-eq : {x y : A} → x ＝ʲ y → x ＝ʸ y
  yoneda-eq-computational-eq (z , p , q) = invʸ q ∙ʸ p

  is-retraction-yoneda-eq-computational-eq :
    {x y : A} →
    is-retraction
      ( computational-eq-yoneda-eq)
      ( yoneda-eq-computational-eq {x} {y})
  is-retraction-yoneda-eq-computational-eq f = refl

  is-section-yoneda-eq-computational-eq :
    {x y : A} →
    is-section
      ( computational-eq-yoneda-eq)
      ( yoneda-eq-computational-eq {x} {y})
  is-section-yoneda-eq-computational-eq (z , p , q) =
    ind-yoneda-Id
      ( λ _ q →
        computational-eq-yoneda-eq (yoneda-eq-computational-eq (z , p , q)) ＝
        (z , p , q))
      ( refl)
      ( q)

  is-equiv-computational-eq-yoneda-eq :
    {x y : A} → is-equiv (computational-eq-yoneda-eq {x} {y})
  is-equiv-computational-eq-yoneda-eq =
    is-equiv-is-invertible
      ( yoneda-eq-computational-eq)
      ( is-section-yoneda-eq-computational-eq)
      ( is-retraction-yoneda-eq-computational-eq)

  is-equiv-yoneda-eq-computational-eq :
    {x y : A} → is-equiv (yoneda-eq-computational-eq {x} {y})
  is-equiv-yoneda-eq-computational-eq =
    is-equiv-is-invertible
      ( computational-eq-yoneda-eq)
      ( is-retraction-yoneda-eq-computational-eq)
      ( is-section-yoneda-eq-computational-eq)

  equiv-computational-eq-yoneda-eq : {x y : A} → (x ＝ʸ y) ≃ (x ＝ʲ y)
  pr1 equiv-computational-eq-yoneda-eq = computational-eq-yoneda-eq
  pr2 equiv-computational-eq-yoneda-eq = is-equiv-computational-eq-yoneda-eq

  equiv-yoneda-eq-computational-eq : {x y : A} → (x ＝ʲ y) ≃ (x ＝ʸ y)
  pr1 equiv-yoneda-eq-computational-eq = yoneda-eq-computational-eq
  pr2 equiv-yoneda-eq-computational-eq = is-equiv-yoneda-eq-computational-eq
```

This equivalence preserves the reflexivity elements strictly in both directions.

```agda
module _
  {l : Level} {A : UU l}
  where

  preserves-refl-yoneda-eq-computational-eq :
    {x : A} →
    yoneda-eq-computational-eq (reflʲ {x = x}) ＝ reflʸ
  preserves-refl-yoneda-eq-computational-eq = refl

  preserves-refl-computational-eq-yoneda-eq :
    {x : A} →
    computational-eq-yoneda-eq (reflʸ {x = x}) ＝ reflʲ
  preserves-refl-computational-eq-yoneda-eq = refl
```

### The computational identity types are equivalent to the standard identity types

By the composite equivalence `(x ＝ y) ≃ (x ＝ʸ y) ≃ (x ＝ʲ y)`, the
computational identity types are equivalent to the standard identity types.
Since each of these equivalences preserve the groupoid structure weakly, so does
the composite. For the same reason, it preserves the reflexivities strictly.

```agda
module _
  {l : Level} {A : UU l}
  where

  computational-eq-eq : {x y : A} → x ＝ y → x ＝ʲ y
  computational-eq-eq = computational-eq-yoneda-eq ∘ yoneda-eq-eq

  eq-computational-eq : {x y : A} → x ＝ʲ y → x ＝ y
  eq-computational-eq = eq-yoneda-eq ∘ yoneda-eq-computational-eq

  equiv-computational-eq-eq : {x y : A} → (x ＝ y) ≃ (x ＝ʲ y)
  equiv-computational-eq-eq =
    equiv-computational-eq-yoneda-eq ∘e equiv-yoneda-eq-eq

  equiv-eq-computational-eq : {x y : A} → (x ＝ʲ y) ≃ (x ＝ y)
  equiv-eq-computational-eq =
    equiv-eq-yoneda-eq ∘e equiv-yoneda-eq-computational-eq

  is-retraction-eq-computational-eq :
    {x y : A} → is-retraction computational-eq-eq (eq-computational-eq {x} {y})
  is-retraction-eq-computational-eq p = left-unit-right-strict-concat

  is-section-eq-computational-eq :
    {x y : A} →
    is-section computational-eq-eq (eq-computational-eq {x} {y})
  is-section-eq-computational-eq (z , p , q) =
    ind-yoneda-Id
      ( λ _ q →
        computational-eq-eq (eq-computational-eq (z , p , q)) ＝ (z , p , q))
      ( eq-pair-eq-fiber (eq-pair (is-section-eq-yoneda-eq p) refl))
      ( q)

  is-equiv-computational-eq-eq :
    {x y : A} → is-equiv (computational-eq-eq {x} {y})
  is-equiv-computational-eq-eq = is-equiv-map-equiv equiv-computational-eq-eq

  is-equiv-eq-computational-eq :
    {x y : A} → is-equiv (eq-computational-eq {x} {y})
  is-equiv-eq-computational-eq = is-equiv-map-equiv equiv-eq-computational-eq
```

This equivalence preserves the reflexivity elements strictly in both directions.

```agda
module _
  {l : Level} {A : UU l}
  where

  preserves-refl-computational-eq-eq :
    {x : A} → computational-eq-eq (refl {x = x}) ＝ reflʲ
  preserves-refl-computational-eq-eq = refl

  preserves-refl-eq-computational-eq :
    {x : A} → eq-computational-eq (reflʲ {x = x}) ＝ refl
  preserves-refl-eq-computational-eq = refl
```

### Torsoriality of the computational identity types

```agda
module _
  {l : Level} {A : UU l} {x : A}
  where

  is-torsorial-computational-Id : is-torsorial (computational-Id x)
  is-torsorial-computational-Id =
    is-contr-equiv
      ( Σ A (x ＝_))
      ( equiv-tot (λ y → equiv-eq-computational-eq {x = x} {y}))
      ( is-torsorial-Id x)
```

### The dependent universal property of the computational identity types

```agda
module _
  {l : Level} {A : UU l} {x : A}
  where

  dependent-universal-property-identity-system-computational-Id :
    dependent-universal-property-identity-system
      ( computational-Id x)
      ( reflʲ)
  dependent-universal-property-identity-system-computational-Id =
    dependent-universal-property-identity-system-is-torsorial
      ( reflʲ)
      ( is-torsorial-computational-Id)
```

### The induction principle for the computational identity types

The computational identity types satisfy the induction principle of the identity
types. This states that given a base point `x : A` and a family of types over
the identity types based at `x`, `B : (y : A) (p : x ＝ʲ y) → UU l2`, then to
construct a dependent function `f : (y : A) (p : x ＝ʲ y) → B y p` it suffices
to define it at `f x reflʲ`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x : A}
  (B : (y : A) (p : x ＝ʲ y) → UU l2)
  where

  ind-computational-Id :
    (b : B x reflʲ) {y : A} (p : x ＝ʲ y) → B y p
  ind-computational-Id b {y} =
    map-inv-is-equiv
      ( dependent-universal-property-identity-system-computational-Id B)
      ( b)
      ( y)

  compute-ind-computational-Id :
    (b : B x reflʲ) → ind-computational-Id b reflʲ ＝ b
  compute-ind-computational-Id =
    is-section-map-inv-is-equiv
      ( dependent-universal-property-identity-system-computational-Id B)

  uniqueness-ind-computational-Id :
    (b : (y : A) (p : x ＝ʲ y) → B y p) →
    (λ y → ind-computational-Id (b x reflʲ) {y}) ＝ b
  uniqueness-ind-computational-Id =
    is-retraction-map-inv-is-equiv
      ( dependent-universal-property-identity-system-computational-Id B)
```

### The strict recursion principle for the computational identity types

Using the fact that the recusion principles of both the Yoneda identity types
and the strictly involutive identity types can be defined to compute strictly,
we obtain a strictly computing recursion principle for the computational
identity types as well.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x : A}
  {B : A → UU l2}
  where

  rec-computational-Id :
    (b : B x) {y : A} → x ＝ʲ y → B y
  rec-computational-Id b p = rec-yoneda-Id b (yoneda-eq-computational-eq p)

  compute-rec-computational-Id :
    (b : B x) → rec-computational-Id b reflʲ ＝ b
  compute-rec-computational-Id b = refl

  uniqueness-rec-computational-Id :
    (b : (y : A) → x ＝ʲ y → B y) →
    (λ y → rec-computational-Id (b x reflʲ) {y}) ＝ b
  uniqueness-rec-computational-Id b =
    ( inv
      ( uniqueness-ind-computational-Id
        ( λ y _ → B y)
        ( λ y → rec-computational-Id (b x reflʲ)))) ∙
    ( uniqueness-ind-computational-Id (λ y _ → B y) b)
```

## Structure

The computational identity types form a groupoidal structure on types. This
structure satisfies the following algebraic laws strictly

- `(p ∙ʲ q) ∙ʲ r ≐ p ∙ʲ (q ∙ʲ r)`
- `reflʲ ∙ʲ p ≐ p` or `p ∙ʲ reflʲ ≐ p`
- `invʲ (invʲ p) ≐ p`
- `invʲ reflʲ ≐ reflʲ`.

### Inverting computational identifications

The construction and computations are the same as for the strictly involutive
identity types. Thus, the inversion operation is defined by swapping the
positions of the two Yoneda identifications

```text
  invʲ := (z , p , q) ↦ (z , q , p).
```

```agda
module _
  {l : Level} {A : UU l}
  where

  invʲ : {x y : A} → x ＝ʲ y → y ＝ʲ x
  invʲ (z , p , q) = (z , q , p)

  compute-inv-refl-computational-Id :
    {x : A} → invʲ (reflʲ {x = x}) ＝ reflʲ
  compute-inv-refl-computational-Id = refl

  inv-inv-computational-Id :
    {x y : A} (p : x ＝ʲ y) →
    invʲ (invʲ p) ＝ p
  inv-inv-computational-Id p = refl
```

The inversion operation on computational identifications corresponds to the
standard inversion operation on identifications:

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  preserves-inv-computational-eq-eq :
    (p : x ＝ y) →
    computational-eq-eq (inv p) ＝ invʲ (computational-eq-eq p)
  preserves-inv-computational-eq-eq refl = refl

  preserves-inv-eq-computational-eq :
    (p : x ＝ʲ y) →
    eq-computational-eq (invʲ p) ＝ inv (eq-computational-eq p)
  preserves-inv-eq-computational-eq (z , f , g) =
    ( ap (g y) (left-unit-right-strict-concat)) ∙
    ( distributive-inv-Id-yoneda-Id g f) ∙
    ( ap (λ r → inv (f x r)) (inv left-unit-right-strict-concat))
```

### The concatenation operations on computational identifications

There is both a strictly left unital and a strictly right unital concatenation
operation, while both are strictly associative. The strict one-sided unitality
follows in both cases from the strict right unitality of the concatenation
operation on the Yoneda identifications, following the same computation as for
the strictly involutive identity types. For associativity on the other hand, we
must use the strict associativity of the Yoneda identity types. We will write
out the explicit computation later.

**Observation.** Since the concatenation operations are strictly associative,
every string of concatenations containing reflexivities will reduce aside from
possibly when the reflexivity appears all the way to the right or left in the
string.

#### The strictly left unital concatenation operation

The strictly left unital concatenation operation is constructed the same way as
the strictly left unital concatenation operation for the strictly involutive
identity types

```text
  (w , p , q) ∙ʲ (w' , p' , q') := (w' , p' , q' ∙ʸ invʸ p ∙ʸ q)
```

```agda
module _
  {l : Level} {A : UU l}
  where

  infixl 15 _∙ʲ_
  _∙ʲ_ : {x y z : A} → x ＝ʲ y → y ＝ʲ z → x ＝ʲ z
  (w , p , q) ∙ʲ (w' , p' , q') = (w' , p' , q' ∙ʸ invʸ p ∙ʸ q)

  concat-computational-Id : {x y : A} → x ＝ʲ y → (z : A) → y ＝ʲ z → x ＝ʲ z
  concat-computational-Id p z q = p ∙ʲ q

  concat-computational-Id' : (x : A) {y z : A} → y ＝ʲ z → x ＝ʲ y → x ＝ʲ z
  concat-computational-Id' x q p = p ∙ʲ q
```

The strictly left unital concatenation operation on computational
identifications corresponds to the strictly left unital concatenation operation
on standard identifications.

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  preserves-concat-computational-eq-eq :
    (p : x ＝ y) (q : y ＝ z) →
    computational-eq-eq (p ∙ q) ＝
    computational-eq-eq p ∙ʲ computational-eq-eq q
  preserves-concat-computational-eq-eq refl q = refl

  preserves-concat-eq-computational-eq :
    (p : x ＝ʲ y) (q : y ＝ʲ z) →
    eq-computational-eq (p ∙ʲ q) ＝
    eq-computational-eq p ∙ eq-computational-eq q
  preserves-concat-eq-computational-eq (w , f , g) (w' , f' , g') =
    ( ap (f' x) left-unit-right-strict-concat) ∙
    ( ap
      ( f' x)
      ( ( ap
          ( inv)
          ( commutative-preconcatr-Id-yoneda-Id
            ( g)
            ( g' w' refl)
            ( inv (f w refl)))) ∙
        ( ( distributive-inv-right-strict-concat
            ( g' w' refl)
            ( g y (inv (f w refl)))) ∙
          ( ( ap
              ( _∙ᵣ inv (g' w' refl))
              ( inv-distributive-inv-Id-yoneda-Id f g)) ∙
            ( eq-concat-right-strict-concat
              ( f x (inv (g w refl)))
              ( inv (g' w' refl)))))) ∙
    ( commutative-preconcat-Id-yoneda-Id f'
      ( f x (inv (g w refl)))
      ( inv (g' w' refl)))) ∙
    ( ap-binary
      ( _∙_)
      ( ap (f x) (inv left-unit-right-strict-concat))
      ( ap (f' y) (inv left-unit-right-strict-concat)))
```

#### The strictly right unital concatenation operation

```agda
module _
  {l : Level} {A : UU l}
  where

  infixl 15 _∙ᵣʲ_
  _∙ᵣʲ_ : {x y z : A} → x ＝ʲ y → y ＝ʲ z → x ＝ʲ z
  (w , p , q) ∙ᵣʲ (w' , p' , q') = (w , p ∙ʸ invʸ q' ∙ʸ p' , q)

  right-strict-concat-computational-Id :
    {x y : A} → x ＝ʲ y → (z : A) → y ＝ʲ z → x ＝ʲ z
  right-strict-concat-computational-Id p z q = p ∙ᵣʲ q

  right-strict-concat-computational-Id' :
    (x : A) {y z : A} → y ＝ʲ z → x ＝ʲ y → x ＝ʲ z
  right-strict-concat-computational-Id' x q p = p ∙ᵣʲ q
```

The strictly right unital concatenation operation on computational
identifications corresponds to the strictly right unital concatenation operation
on standard identifications.

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  preserves-right-strict-concat-computational-eq-eq :
    (p : x ＝ y) (q : y ＝ z) →
    computational-eq-eq (p ∙ᵣ q) ＝
    computational-eq-eq p ∙ᵣʲ computational-eq-eq q
  preserves-right-strict-concat-computational-eq-eq p refl = refl

  preserves-right-strict-concat-eq-computational-eq :
    (p : x ＝ʲ y) (q : y ＝ʲ z) →
    eq-computational-eq (p ∙ᵣʲ q) ＝
    eq-computational-eq p ∙ᵣ eq-computational-eq q
  preserves-right-strict-concat-eq-computational-eq (w , f , g) (w' , f' , g') =
    ( ap
      ( λ r → f' x (f x r ∙ᵣ inv (g' w' refl)))
      ( left-unit-right-strict-concat)) ∙
    ( commutative-preconcatr-Id-yoneda-Id
      ( f')
      ( f x (inv (g w refl)))
      ( inv (g' w' refl))) ∙
    ( ap-binary
      ( _∙ᵣ_)
      ( ap (f x) (inv left-unit-right-strict-concat))
      ( ap (f' y) (inv left-unit-right-strict-concat)))
```

### The groupoidal laws for the computational identity types

#### The groupoidal laws for the strictly left unital concatenation operation

To see that `_∙ʲ_` is strictly associative, we unfold both `(P ∙ʲ Q) ∙ʲ R` and
`P ∙ʲ (Q ∙ʲ R)` and observe that it follows from the strict associativity of
`_∙ʸ_`:

```text
  (P ∙ʲ Q) ∙ʲ R
  ≐ ((u , p , p') ∙ʲ (v , q , q')) ∙ʲ (w , r , r')
  ≐ ((v , q , (q' ∙ʸ invʸ p) ∙ʸ p')) ∙ʲ (w , r , r')
  ≐ (w , r , (r' ∙ʸ invʸ q) ∙ʸ ((q' ∙ʸ invʸ p) ∙ʸ p'))

  ≐ (w , r , (((r' ∙ʸ invʸ q) ∙ʸ q') ∙ʸ invʸ p) ∙ʸ p')
  ≐ (u , p , p') ∙ʲ ((w , r , (r' ∙ʸ invʸ q) ∙ʸ q'))
  ≐ (u , p , p') ∙ʲ ((v , q , q') ∙ʲ (w , r , r'))
  ≐ P ∙ʲ (Q ∙ʲ R).
```

```agda
module _
  {l : Level} {A : UU l} {x y z w : A}
  where

  assoc-concat-computational-Id :
    (p : x ＝ʲ y) (q : y ＝ʲ z) (r : z ＝ʲ w) →
    (p ∙ʲ q) ∙ʲ r ＝ p ∙ʲ (q ∙ʲ r)
  assoc-concat-computational-Id p q r = refl

module _
  {l : Level} {A : UU l} {x y : A}
  where

  left-unit-concat-computational-Id :
    {p : x ＝ʲ y} → reflʲ ∙ʲ p ＝ p
  left-unit-concat-computational-Id = refl

  right-unit-concat-computational-Id :
    {p : x ＝ʲ y} → p ∙ʲ reflʲ ＝ p
  right-unit-concat-computational-Id {z , p , q} =
    ind-yoneda-Id
      ( λ _ p → (z , p , q) ∙ʲ reflʲ ＝ (z , p , q))
      ( refl)
      ( p)

  left-inv-concat-computational-Id :
    (p : x ＝ʲ y) → invʲ p ∙ʲ p ＝ reflʲ
  left-inv-concat-computational-Id (z , p , q) =
    ind-yoneda-Id
      ( λ _ p →
        ( invʲ (z , p , q) ∙ʲ (z , p , q)) ＝
        ( reflʲ))
      ( eq-pair-eq-fiber (eq-pair-eq-fiber (right-inv-yoneda-Id q)))
      ( p)

  right-inv-concat-computational-Id :
    (p : x ＝ʲ y) → p ∙ʲ invʲ p ＝ reflʲ
  right-inv-concat-computational-Id (z , p , q) =
    ind-yoneda-Id
      ( λ _ q →
        ( (z , p , q) ∙ʲ invʲ (z , p , q)) ＝
        ( reflʲ))
      ( eq-pair-eq-fiber (eq-pair-eq-fiber (right-inv-yoneda-Id p)))
      ( q)

  distributive-inv-concat-computational-Id :
    (p : x ＝ʲ y) {z : A} (q : y ＝ʲ z) →
    invʲ (p ∙ʲ q) ＝
    invʲ q ∙ʲ invʲ p
  distributive-inv-concat-computational-Id p =
    ind-computational-Id
      ( λ _ q →
        invʲ (p ∙ʲ q) ＝
        invʲ q ∙ʲ invʲ p)
      ( ap invʲ (right-unit-concat-computational-Id))
```

#### The groupoidal laws for the strictly right unital concatenation operation

Associativity for the strictly right unital concatenation operation follows from
a similar computation to the one for the strictly left unital concatenation
operation.

```agda
module _
  {l : Level} {A : UU l}
  where

  assoc-right-strict-concat-computational-Id :
    {x y z w : A} (p : x ＝ʲ y) (q : y ＝ʲ z) (r : z ＝ʲ w) →
    (p ∙ᵣʲ q) ∙ᵣʲ r ＝ p ∙ᵣʲ (q ∙ᵣʲ r)
  assoc-right-strict-concat-computational-Id p q r = refl

module _
  {l : Level} {A : UU l} {x y : A}
  where

  right-unit-right-strict-concat-computational-Id :
    {p : x ＝ʲ y} → p ∙ᵣʲ reflʲ ＝ p
  right-unit-right-strict-concat-computational-Id = refl

  left-unit-right-strict-concat-computational-Id :
    {p : x ＝ʲ y} → reflʲ ∙ᵣʲ p ＝ p
  left-unit-right-strict-concat-computational-Id {z , p , q} =
    ind-yoneda-Id (λ _ q → reflʲ ∙ᵣʲ (z , p , q) ＝ (z , p , q)) refl q

  left-inv-right-strict-concat-computational-Id :
    (p : x ＝ʲ y) → invʲ p ∙ᵣʲ p ＝ reflʲ
  left-inv-right-strict-concat-computational-Id (z , p , q) =
    ind-yoneda-Id
      ( λ _ p → invʲ (z , p , q) ∙ᵣʲ (z , p , q) ＝ reflʲ)
      ( eq-pair-eq-fiber (eq-pair (right-inv-yoneda-Id q) refl))
      ( p)

  right-inv-right-strict-concat-computational-Id :
    (p : x ＝ʲ y) → p ∙ᵣʲ invʲ p ＝ reflʲ
  right-inv-right-strict-concat-computational-Id (z , p , q) =
    ind-yoneda-Id
      ( λ _ q → (z , p , q) ∙ᵣʲ invʲ (z , p , q) ＝ reflʲ)
      ( eq-pair-eq-fiber (eq-pair (right-inv-yoneda-Id p) refl))
      ( q)

module _
  {l : Level} {A : UU l} {x y : A}
  where

  distributive-inv-right-strict-concat-computational-Id :
    (p : x ＝ʲ y) {z : A} (q : y ＝ʲ z) → invʲ (p ∙ᵣʲ q) ＝ invʲ q ∙ᵣʲ invʲ p
  distributive-inv-right-strict-concat-computational-Id p =
    ind-computational-Id
      ( λ _ q → invʲ (p ∙ᵣʲ q) ＝ invʲ q ∙ᵣʲ invʲ p)
      ( inv left-unit-right-strict-concat-computational-Id)
```

## Operations

We can define a range of basic operations on computational identifications that
all enjoy strict computational properties.

### Action of functions on computational identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  eq-ap-computational-Id : {x y : A} → x ＝ʲ y → f x ＝ f y
  eq-ap-computational-Id = ap f ∘ eq-computational-eq

  ap-computational-Id : {x y : A} → x ＝ʲ y → f x ＝ʲ f y
  ap-computational-Id =
    computational-eq-yoneda-eq ∘ ap-yoneda-Id f ∘ yoneda-eq-computational-eq

  compute-ap-refl-computational-Id :
    {x : A} →
    ap-computational-Id (reflʲ {x = x}) ＝ reflʲ
  compute-ap-refl-computational-Id = refl

module _
  {l1 : Level} {A : UU l1}
  where

  compute-ap-id-computational-Id :
    {x y : A} (p : x ＝ʲ y) → ap-computational-Id id p ＝ p
  compute-ap-id-computational-Id p =
    ( ap
      ( computational-eq-yoneda-eq)
      ( compute-ap-id-yoneda-Id (yoneda-eq-computational-eq p))) ∙
    ( is-section-yoneda-eq-computational-eq p)
```

### Transport along computational identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  tr-computational-Id : {x y : A} → x ＝ʲ y → B x → B y
  tr-computational-Id = tr B ∘ eq-computational-eq

  compute-tr-refl-computational-Id :
    {x : A} → tr-computational-Id (reflʲ {x = x}) ＝ id
  compute-tr-refl-computational-Id = refl
```

### Function extensionality with respect to computational identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  where

  htpy-computational-eq : f ＝ʲ g → f ~ g
  htpy-computational-eq = htpy-eq ∘ eq-computational-eq

  computational-eq-htpy : f ~ g → f ＝ʲ g
  computational-eq-htpy = computational-eq-eq ∘ eq-htpy

  equiv-htpy-computational-eq : (f ＝ʲ g) ≃ (f ~ g)
  equiv-htpy-computational-eq = equiv-funext ∘e equiv-eq-computational-eq

  equiv-computational-eq-htpy : (f ~ g) ≃ (f ＝ʲ g)
  equiv-computational-eq-htpy = equiv-computational-eq-eq ∘e equiv-eq-htpy

  funext-computational-Id : is-equiv htpy-computational-eq
  funext-computational-Id = is-equiv-map-equiv equiv-htpy-computational-eq
```

### Univalence with respect to computational identifications

```agda
module _
  {l1 : Level} {A B : UU l1}
  where

  map-computational-eq : A ＝ʲ B → A → B
  map-computational-eq = map-eq ∘ eq-computational-eq

  equiv-computational-eq : A ＝ʲ B → A ≃ B
  equiv-computational-eq = equiv-eq ∘ eq-computational-eq

  computational-eq-equiv : A ≃ B → A ＝ʲ B
  computational-eq-equiv = computational-eq-eq ∘ eq-equiv

  equiv-equiv-computational-eq : (A ＝ʲ B) ≃ (A ≃ B)
  equiv-equiv-computational-eq = equiv-univalence ∘e equiv-eq-computational-eq

  is-equiv-equiv-computational-eq : is-equiv equiv-computational-eq
  is-equiv-equiv-computational-eq =
    is-equiv-map-equiv equiv-equiv-computational-eq

  equiv-computational-eq-equiv : (A ≃ B) ≃ (A ＝ʲ B)
  equiv-computational-eq-equiv = equiv-computational-eq-eq ∘e equiv-eq-equiv A B

  is-equiv-computational-eq-equiv : is-equiv computational-eq-equiv
  is-equiv-computational-eq-equiv =
    is-equiv-map-equiv equiv-computational-eq-equiv
```

## References

{{#bibliography}}

## See also

- [The strictly involutive identity types](foundation.strictly-involutive-identity-types.md)
- [The Yoneda identity types](foundation.yoneda-identity-types.md)
