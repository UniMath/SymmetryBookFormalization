# The Cantor–Schröder–Bernstein–Escardó construction

```agda
module foundation.cantor-schroder-bernstein-escardo where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.decidable-embeddings
open import foundation.decidable-maps
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.injective-maps
open import foundation.law-of-excluded-middle
open import foundation.maps-with-hilbert-epsilon-operators
open import foundation.perfect-images
open import foundation.pi-0-trivial-maps
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sections
open import foundation.split-surjective-maps
open import foundation.universe-levels
open import foundation.weak-limited-principle-of-omniscience

open import foundation-core.coproduct-types
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.negation
open import foundation-core.propositional-maps
open import foundation-core.sets

open import logic.double-negation-eliminating-maps
open import logic.double-negation-stable-embeddings
```

</details>

## Idea

The classical Cantor–Schröder–Bernstein theorem asserts that from any pair of
[injective maps](foundation-core.injective-maps.md) `f : A → B` and `g : B → A`
we can construct a bijection between `A` and `B`. In a recent generalization,
Escardó proved that a Cantor–Schröder–Bernstein theorem also holds for
∞-groupoids. His generalization asserts that given two types that
[embed](foundation-core.embeddings.md) into each other, then the types are
[equivalent](foundation-core.equivalences.md). {{#cite Esc21}}

In this file we give a fine-grained analysis of the construction used in the
proof of this _Cantor–Schröder–Bernstein-Escardó theorem_, and use this
deconstruction to give a series of further generalizations of the theorem.

The Cantor–Schröder–Bernstein theorem is the 25th theorem on
[Freek Wiedijk's](http://www.cs.ru.nl/F.Wiedijk/) list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

## The Cantor-Schröder-Bernstein-Escardó construction

Given a pair of mutual maps `f : A → B` and `g : B → A` such that

1. the maps `f` and `g` satisfy double negation elimination on their fibers
2. For every element `x : A` it is decidable wheter `x` is a perfect image of
   `g` relative to `f`
3. `g` is injective
4. `f` is π₀-trivial

Then `B` is a retract of `A`. If `f` moreover is injective, then this retract is
an equivalence.

```agda
module _
  {l1 l2 : Level}
  {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  (G' : is-injective g)
  (G : is-double-negation-eliminating-map g)
  (F : is-double-negation-eliminating-map f)
  where

  map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó :
    (x : A) → is-decidable (is-perfect-image f g x) → B
  map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
    x (inl γ) =
    inverse-of-perfect-image x γ
  map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
    x (inr nγ) =
    f x

  compute-map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó :
    (y : B) →
    (γ : is-perfect-image f g (g y)) →
    (d : is-decidable (is-perfect-image f g (g y))) →
    map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
      ( g y) d ＝
    y
  compute-map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
    y γ (inl v') =
    is-retraction-inverse-of-perfect-image G' y v'
  compute-map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
    y γ (inr v) =
    ex-falso (v γ)

  compute-map-construction-is-not-perfect-image-Cantor-Schröder-Bernstein–Escardó :
    (F' : is-π₀-trivial-map' f) →
    (y : B) →
    (nγ : ¬ (is-perfect-image f g (g y))) →
    (d :
      is-decidable
        ( is-perfect-image f g
          ( element-has-nonperfect-fiber-is-not-perfect-image
              G G' F F' y nγ))) →
    map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
      ( element-has-nonperfect-fiber-is-not-perfect-image G G' F F' y nγ)
      ( d) ＝
    y
  compute-map-construction-is-not-perfect-image-Cantor-Schröder-Bernstein–Escardó
    F' y nγ (inl v) =
    ex-falso
      ( is-not-perfect-image-has-nonperfect-fiber-is-not-perfect-image
          G G' F F' y nγ v)
  compute-map-construction-is-not-perfect-image-Cantor-Schröder-Bernstein–Escardó
    F' y nγ (inr _) =
    is-in-fiber-element-has-nonperfect-fiber-is-not-perfect-image
      G G' F F' y nγ

  map-section-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó :
    (F' : is-π₀-trivial-map' f) →
    (y : B) → is-decidable (is-perfect-image f g (g y)) → A
  map-section-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
    F' y (inl _) = g y
  map-section-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
    F' y (inr nγ) =
    element-has-nonperfect-fiber-is-not-perfect-image G G' F F' y nγ

  is-section-map-section-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó :
    (F' : is-π₀-trivial-map' f) →
    (y : B)
    (d : is-decidable (is-perfect-image f g (g y))) →
    (d' :
      is-decidable
        ( is-perfect-image f g
          ( map-section-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
              F' y d))) →
    map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
      ( map-section-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
          F' y d)
      ( d') ＝
    y
  is-section-map-section-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
    F' y (inl γ) =
    compute-map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
      y γ
  is-section-map-section-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
    F' y (inr nγ) =
    compute-map-construction-is-not-perfect-image-Cantor-Schröder-Bernstein–Escardó
      F' y nγ

  map-construction-Cantor-Schröder-Bernstein–Escardó :
    (D : (x : A) → is-decidable (is-perfect-image f g x)) → A → B
  map-construction-Cantor-Schröder-Bernstein–Escardó D x =
    map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
      ( x)
      ( D x)

  map-section-construction-Cantor-Schröder-Bernstein–Escardó :
    (F' : is-π₀-trivial-map' f) →
    (D : (y : B) → is-decidable (is-perfect-image f g (g y))) → B → A
  map-section-construction-Cantor-Schröder-Bernstein–Escardó F' D y =
    map-section-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
      ( F')
      ( y)
      ( D y)

  is-section-map-section-construction-Cantor-Schröder-Bernstein–Escardó :
    (F' : is-π₀-trivial-map' f) →
    (D : (x : A) → is-decidable (is-perfect-image f g x)) →
    is-section
      ( map-construction-Cantor-Schröder-Bernstein–Escardó D)
      ( map-section-construction-Cantor-Schröder-Bernstein–Escardó F' (D ∘ g))
  is-section-map-section-construction-Cantor-Schröder-Bernstein–Escardó F' D y =
    is-section-map-section-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
      ( F')
      ( y)
      ( D (g y))
      ( D ( map-section-construction-Cantor-Schröder-Bernstein–Escardó
              F' (D ∘ g) y))

  section-construction-Cantor-Schröder-Bernstein–Escardó :
    (F' : is-π₀-trivial-map' f) →
    (D : (x : A) → is-decidable (is-perfect-image f g x)) →
    section (map-construction-Cantor-Schröder-Bernstein–Escardó D)
  section-construction-Cantor-Schröder-Bernstein–Escardó F' D =
    map-section-construction-Cantor-Schröder-Bernstein–Escardó F' (D ∘ g) ,
    is-section-map-section-construction-Cantor-Schröder-Bernstein–Escardó F' D
```

Injectivity of the constructed map.

```agda
  is-injective-map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó :
    (F' : is-injective f) →
    {x x' : A}
    (d : is-decidable (is-perfect-image f g x))
    (d' : is-decidable (is-perfect-image f g x')) →
    ( map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
      ( x)
      ( d)) ＝
    ( map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
      ( x')
      ( d')) →
    x ＝ x'
  is-injective-map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
    F' { x} {x'} (inl ρ) (inl ρ') p =
    ( inv (is-section-inverse-of-perfect-image x ρ)) ∙
    ( ap g p ∙
      is-section-inverse-of-perfect-image x' ρ')
  is-injective-map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
    F' {x} {x'} (inl ρ) (inr nρ') p =
    ex-falso (perfect-image-has-distinct-image x' x nρ' ρ (inv p))
  is-injective-map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
    F' { x} {x'} (inr nρ) (inl ρ') p =
    ex-falso (perfect-image-has-distinct-image x x' nρ ρ' p)
  is-injective-map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
    F' {lx} {x'} (inr nρ) (inr nρ') p = F' p -- TODO: look for alternative approach avoiding `is-injective f`
```

Piecing it all together.

```agda
  is-equiv-map-construction-Cantor-Schröder-Bernstein–Escardó :
    (F' : is-π₀-trivial-map' f) →
    (F'' : is-injective f) →
    (D : (x : A) → is-decidable (is-perfect-image f g x)) →
    is-equiv (map-construction-Cantor-Schröder-Bernstein–Escardó D)
  is-equiv-map-construction-Cantor-Schröder-Bernstein–Escardó
    F' F'' D =
    is-equiv-is-injective
      ( section-construction-Cantor-Schröder-Bernstein–Escardó F' D)
      ( λ {x} {x'} →
        is-injective-map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein–Escardó
          ( F'')
          ( D x)
          ( D x'))

  equiv-construction-Cantor-Schröder-Bernstein–Escardó :
    (F' : is-π₀-trivial-map' f) →
    (F'' : is-injective f) →
    (D : (x : A) → is-decidable (is-perfect-image f g x)) →
    A ≃ B
  equiv-construction-Cantor-Schröder-Bernstein–Escardó F' F'' D =
    map-construction-Cantor-Schröder-Bernstein–Escardó D ,
    is-equiv-map-construction-Cantor-Schröder-Bernstein–Escardó F' F'' D
```

## Theorem

### The Cantor-Schröder-Bernstein theorem assuming the weak limited principle of omniscience

It follows from the weak limited principle of omniscience that, for every pair
of mutual decidable embeddings `f : A ↪ B` and `g : B ↪ A`, it is decidable for
every element `x : A` whether `x` is a perfect image of `g` relative to `f`.

Applying this fact to the Cantor-Schröder-Bernstein-Escardó construction, we
conclude that every pair of types that mutually embed into oneanother via
decidable embeddings are equivalent.

In fact, it suffices to assume that `f` is decidable, π₀-trivial, and injective.

```agda
abstract
  is-decidable-is-perfect-image'-WLPO :
    {l1 l2 : Level} (wlpo : level-WLPO (l1 ⊔ l2))
    {A : UU l1} {B : UU l2} {f : A → B} {g : B → A} →
    is-decidable-emb g → is-decidable-map f → is-π₀-trivial-map' f →
    (a : A) → is-decidable (is-perfect-image' f g a)
  is-decidable-is-perfect-image'-WLPO wlpo {f = f} {g} G F F' a =
    wlpo
      ( λ n →
        is-perfect-image-at' f g a n ,
        is-decidable-prop-is-perfect-image-at' G F F' a n)

is-decidable-is-perfect-image-WLPO :
  {l1 l2 : Level} (wlpo : level-WLPO (l1 ⊔ l2))
  {A : UU l1} {B : UU l2} {f : A → B} {g : B → A} →
  is-decidable-emb g → is-decidable-map f → is-π₀-trivial-map' f →
  (a : A) → is-decidable (is-perfect-image f g a)
is-decidable-is-perfect-image-WLPO wlpo {f = f} {g} G F F' a =
  is-decidable-equiv'
    ( compute-is-perfect-image f g a)
    ( is-decidable-is-perfect-image'-WLPO wlpo G F F' a)
```

```agda
generalized-Cantor-Schröder-Bernstein-WLPO :
  {l1 l2 : Level} → level-WLPO (l1 ⊔ l2) →
  {A : UU l1} {B : UU l2} {f : A → B} {g : B → A} →
  is-decidable-emb g →
  is-decidable-map f → is-π₀-trivial-map' f → is-injective f →
  A ≃ B
generalized-Cantor-Schröder-Bernstein-WLPO wlpo G F F' F'' =
  equiv-construction-Cantor-Schröder-Bernstein–Escardó
    ( is-injective-is-decidable-emb G)
    ( is-double-negation-eliminating-map-is-decidable-emb G)
    ( is-double-negation-eliminating-map-is-decidable-map F)
    ( F')
    ( F'')
    ( is-decidable-is-perfect-image-WLPO wlpo
      ( G)
      ( F)
      ( F'))

Cantor-Schröder-Bernstein-WLPO' :
  {l1 l2 : Level} → level-WLPO (l1 ⊔ l2) →
  {A : UU l1} {B : UU l2} {f : A → B} {g : B → A} →
  is-decidable-emb g → is-decidable-emb f →
  A ≃ B
Cantor-Schröder-Bernstein-WLPO' wlpo G F =
  generalized-Cantor-Schröder-Bernstein-WLPO wlpo G
    ( is-decidable-map-is-decidable-emb F)
    ( is-π₀-trivial-map'-is-emb (is-emb-is-decidable-emb F))
    ( is-injective-is-decidable-emb F)

Cantor-Schröder-Bernstein-WLPO :
  {l1 l2 : Level} → level-WLPO (l1 ⊔ l2) →
  {A : UU l1} {B : UU l2} → (A ↪ᵈ B) → (B ↪ᵈ A) → A ≃ B
Cantor-Schröder-Bernstein-WLPO wlpo (f , F) (g , G) =
  Cantor-Schröder-Bernstein-WLPO' wlpo G F
```

### The ε-generalized Cantor-Schröder-Bernstein-Escardó theorem

Assuming the [law of exluded middle](foundation.law-of-excluded-middle.md), then
given two types `A` and `B` such that there is a π₀-trivial injection `A → B`
equipped with a Hilbert ε-operator, and an embedding `B ↪ A`, then `A` and `B`
are equivalent.

```agda
ε-Cantor-Schröder-Bernstein-LEM :
  {l1 l2 : Level} → LEM (l1 ⊔ l2) →
  {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  (G : is-emb g) →
  (F : is-π₀-trivial-map' f) →
  (F' : is-injective f) →
  (εF : ε-operator-map-Hilbert f) →
  A ≃ B
ε-Cantor-Schröder-Bernstein-LEM lem {f = f} {g} G F F' εF =
  equiv-construction-Cantor-Schröder-Bernstein–Escardó
    ( is-injective-is-emb G)
    ( is-double-negation-eliminating-map-is-decidable-map
      ( λ y → lem (fiber g y , is-prop-map-is-emb G y)))
    ( λ y →
      ( λ nnf →
        εF
          ( y)
          ( double-negation-elim-is-decidable
            ( lem (trunc-Prop (fiber f y)))
            ( map-double-negation unit-trunc-Prop nnf))))
    ( F)
    ( F')
    ( lem ∘ is-perfect-image-Prop G)
```

### The Cantor-Schröder-Bernstein-Escardó theorem

```agda
Cantor-Schröder-Bernstein-Escardó' :
  {l1 l2 : Level} → LEM (l1 ⊔ l2) →
  {A : UU l1} {B : UU l2} {f : A → B} {g : B → A} →
  is-emb g → is-emb f → A ≃ B
Cantor-Schröder-Bernstein-Escardó' lem {f = f} {g} G F =
  Cantor-Schröder-Bernstein-WLPO'
    ( λ P → lem (Π-Prop ℕ (prop-Decidable-Prop ∘ P)))
    ( G , λ y → lem (fiber g y , is-prop-map-is-emb G y))
    ( F , λ y → lem (fiber f y , is-prop-map-is-emb F y))

Cantor-Schröder-Bernstein-Escardó :
  {l1 l2 : Level} → LEM (l1 ⊔ l2) →
  {A : UU l1} {B : UU l2} →
  A ↪ B → B ↪ A → A ≃ B
Cantor-Schröder-Bernstein-Escardó lem (f , F) (g , G) =
  Cantor-Schröder-Bernstein-Escardó' lem G F
```

### The Cantor–Schröder–Bernstein theorem

```agda
Cantor-Schröder-Bernstein :
  {l1 l2 : Level} (lem : LEM (l1 ⊔ l2))
  (A : Set l1) (B : Set l2) →
  injection (type-Set A) (type-Set B) →
  injection (type-Set B) (type-Set A) →
  (type-Set A) ≃ (type-Set B)
Cantor-Schröder-Bernstein lem A B f g =
  Cantor-Schröder-Bernstein-Escardó lem (emb-injection B f) (emb-injection A g)
```

## References

- Escardó's formalizations regarding this theorem can be found at
  <https://www.cs.bham.ac.uk/~mhe/TypeTopology/CantorSchroederBernstein.index.html>.
  {{#cite TypeTopology}}

{{#bibliography}}
