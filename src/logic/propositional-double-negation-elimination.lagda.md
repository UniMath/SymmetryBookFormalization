# Propositional double negation elimination

```agda
module logic.propositional-double-negation-elimination where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.evaluation-functions
open import foundation.functoriality-propositional-truncation
open import foundation.hilberts-epsilon-operators
open import foundation.identity-types
open import foundation.irrefutable-equality
open import foundation.logical-equivalences
open import foundation.mere-equality
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.retracts-of-types
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions

open import logic.double-negation-elimination
open import logic.propositionally-decidable-types
```

</details>

## Idea

We say a type `A` satisfies
{{#concept "propositional double negation elimination" Disambiguation="on a type" Agda=has-prop-double-negation-elim}}
if there is a map

```text
  ¬¬A → ║A║₋₁.
```

## Definitions

### Untruncated double negation elimination

```agda
module _
  {l : Level} (A : UU l)
  where

  has-prop-double-negation-elim : UU l
  has-prop-double-negation-elim = ¬¬ A → ║ A ║₋₁

  is-prop-has-prop-double-negation-elim : is-prop has-prop-double-negation-elim
  is-prop-has-prop-double-negation-elim =
    is-prop-function-type is-prop-type-trunc-Prop

  has-prop-double-negation-elim-Prop : Prop l
  has-prop-double-negation-elim-Prop =
    ( has-prop-double-negation-elim , is-prop-has-prop-double-negation-elim)
```

## Properties

### Propositional double negation elimination is preserved by logical equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  has-prop-double-negation-elim-iff :
    A ↔ B → has-prop-double-negation-elim B → has-prop-double-negation-elim A
  has-prop-double-negation-elim-iff e H =
    map-trunc-Prop (backward-implication e) ∘
    H ∘
    map-double-negation (forward-implication e)

  has-prop-double-negation-elim-iff' :
    B ↔ A → has-prop-double-negation-elim B → has-prop-double-negation-elim A
  has-prop-double-negation-elim-iff' e =
    has-prop-double-negation-elim-iff (inv-iff e)
```

### Propositional double negation elimination is preserved by equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  has-prop-double-negation-elim-equiv :
    A ≃ B → has-prop-double-negation-elim B → has-prop-double-negation-elim A
  has-prop-double-negation-elim-equiv e =
    has-prop-double-negation-elim-iff (iff-equiv e)

  has-prop-double-negation-elim-equiv' :
    B ≃ A → has-prop-double-negation-elim B → has-prop-double-negation-elim A
  has-prop-double-negation-elim-equiv' e =
    has-prop-double-negation-elim-iff' (iff-equiv e)
```

### Propositional double negation elimination is preserved by retracts

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  has-prop-double-negation-elim-retract :
    A retract-of B →
    has-prop-double-negation-elim B → has-prop-double-negation-elim A
  has-prop-double-negation-elim-retract e =
    has-prop-double-negation-elim-iff (iff-retract e)

  has-prop-double-negation-elim-retract' :
    B retract-of A →
    has-prop-double-negation-elim B → has-prop-double-negation-elim A
  has-prop-double-negation-elim-retract' e =
    has-prop-double-negation-elim-iff' (iff-retract e)
```

### If the negation of a type with double negation elimination is decidable, then the type is merely decidable

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  is-inhabited-or-empty-is-decidable-neg-has-prop-double-negation-elim :
    has-prop-double-negation-elim A →
    is-decidable (¬ A) →
    is-inhabited-or-empty A
  is-inhabited-or-empty-is-decidable-neg-has-prop-double-negation-elim f
    ( inl nx) =
    inr nx
  is-inhabited-or-empty-is-decidable-neg-has-prop-double-negation-elim f
    ( inr nnx) =
    inl (f nnx)
```

**Remark.** It is an established fact that both the property of satisfying
double negation elimination, and the property of having decidable negation, are
strictly weaker conditions than being decidable. Therefore, this result
demonstrates that they are independent too.

### Types with double negation elimination satisfy propositional double negation elimination

```agda
has-prop-double-negation-elim-has-double-negation-elim :
  {l : Level} {A : UU l} →
  has-double-negation-elim A →
  has-prop-double-negation-elim A
has-prop-double-negation-elim-has-double-negation-elim H = unit-trunc-Prop ∘ H
```

### Propositional double negation elimination for merely decidable types

```agda
prop-double-negation-elim-is-inhabited-or-empty :
  {l : Level} {A : UU l} →
  is-inhabited-or-empty A → has-prop-double-negation-elim A
prop-double-negation-elim-is-inhabited-or-empty (inl |a|) _ = |a|
prop-double-negation-elim-is-inhabited-or-empty (inr na) nna = ex-falso (nna na)
```

### Propositional double negation elimination for dependent sums

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  has-prop-double-negation-elim-Σ-all-elements-irrefutably-equal-base :
    all-elements-irrefutably-equal A →
    has-prop-double-negation-elim A →
    ((x : A) → has-prop-double-negation-elim (B x)) →
    has-prop-double-negation-elim (Σ A B)
  has-prop-double-negation-elim-Σ-all-elements-irrefutably-equal-base
    H f g nnab =
    rec-trunc-Prop
      ( trunc-Prop (Σ A B))
      ( λ a →
        rec-trunc-Prop
          ( trunc-Prop (Σ A B))
          ( λ b → unit-trunc-Prop (a , b))
          ( g a (λ nb → nnab (λ x → H (pr1 x) a (λ p → nb (tr B p (pr2 x)))))))
      ( f (map-double-negation pr1 nnab))

  has-prop-double-negation-elim-Σ-all-elements-merely-equal-base :
    all-elements-merely-equal A →
    has-prop-double-negation-elim A →
    ((x : A) → has-prop-double-negation-elim (B x)) →
    has-prop-double-negation-elim (Σ A B)
  has-prop-double-negation-elim-Σ-all-elements-merely-equal-base H =
    has-prop-double-negation-elim-Σ-all-elements-irrefutably-equal-base
      ( λ x y →
        double-negation-double-negation-type-trunc-Prop
          ( intro-double-negation (H x y)))

  has-prop-double-negation-elim-Σ-is-prop-base :
    is-prop A →
    has-prop-double-negation-elim A →
    ((x : A) → has-prop-double-negation-elim (B x)) →
    has-prop-double-negation-elim (Σ A B)
  has-prop-double-negation-elim-Σ-is-prop-base is-prop-A =
    has-prop-double-negation-elim-Σ-all-elements-merely-equal-base
      ( λ x y → unit-trunc-Prop (eq-is-prop is-prop-A))

  has-prop-double-negation-elim-base-Σ-section' :
    has-prop-double-negation-elim (Σ A B) →
    (A → Σ A B) →
    has-prop-double-negation-elim A
  has-prop-double-negation-elim-base-Σ-section' H f nna =
    map-trunc-Prop pr1 (H (λ nab → nna (λ x → nab (f x))))

  has-prop-double-negation-elim-base-Σ-section :
    has-prop-double-negation-elim (Σ A B) →
    ((x : A) → B x) →
    has-prop-double-negation-elim A
  has-prop-double-negation-elim-base-Σ-section H f =
    has-prop-double-negation-elim-base-Σ-section' H (λ x → x , f x)

  has-prop-double-negation-elim-family-Σ-all-elements-merely-equal-base :
    has-prop-double-negation-elim (Σ A B) →
    all-elements-merely-equal A →
    (x : A) → has-prop-double-negation-elim (B x)
  has-prop-double-negation-elim-family-Σ-all-elements-merely-equal-base
    K q x nnb =
    rec-trunc-Prop
      ( trunc-Prop (B x))
      ( λ xy →
        rec-trunc-Prop
          ( trunc-Prop (B x))
          ( λ p → unit-trunc-Prop (tr B p (pr2 xy)))
          ( q (pr1 xy) x))
      ( K (λ nab → nnb (λ y → nab (x , y))))
```

### Double negation elimination for products of types with double negation elimination

```agda
has-prop-double-negation-elim-product :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-prop-double-negation-elim A →
  has-prop-double-negation-elim B →
  has-prop-double-negation-elim (A × B)
has-prop-double-negation-elim-product {A = A} {B} f g nnab =
  rec-trunc-Prop
    ( trunc-Prop (A × B))
    ( λ a →
      rec-trunc-Prop
        ( trunc-Prop (A × B))
        ( λ b → unit-trunc-Prop (a , b))
        ( g (map-double-negation pr2 nnab)))
    ( f (map-double-negation pr1 nnab))
```

## See also

- [The double negation modality](foundation.double-negation-modality.md)
- [Irrefutable propositions](foundation.irrefutable-propositions.md) are double
  negation connected types.
