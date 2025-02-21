# The well-ordering principle of the standard finite types

```agda
module elementary-number-theory.well-ordering-principle-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-standard-finite-types
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-subtypes
open import foundation.decidable-type-families
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.hilberts-epsilon-operators
open import foundation.identity-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.decidable-dependent-pair-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The standard finite types inherit a well-ordering principle from the natural
numbers.

## Properties

### For any decidable family `P` over `Fin n`, if `P x` doesn't hold for all `x` then there exists an `x` for which `P x` is false

```agda
exists-not-not-for-all-Fin :
  {l : Level} (k : ℕ) {P : Fin k → UU l} → (is-decidable-family P) →
  ¬ ((x : Fin k) → P x) → Σ (Fin k) (λ x → ¬ (P x))
exists-not-not-for-all-Fin {l} zero-ℕ d H = ex-falso (H ind-empty)
exists-not-not-for-all-Fin {l} (succ-ℕ k) {P} d H with d (inr star)
... | inl p =
  T ( exists-not-not-for-all-Fin k
      ( λ x → d (inl x))
      ( λ f → H (ind-coproduct P f (ind-unit p))))
  where
  T : Σ (Fin k) (λ x → ¬ (P (inl x))) → Σ (Fin (succ-ℕ k)) (λ x → ¬ (P x))
  T z = pair (inl (pr1 z)) (pr2 z)
... | inr f = pair (inr star) f

exists-not-not-for-all-count :
  {l1 l2 : Level} {X : UU l1} (P : X → UU l2) →
  (is-decidable-family P) → count X →
  ¬ ((x : X) → P x) → Σ X (λ x → ¬ (P x))
exists-not-not-for-all-count {l1} {l2} {X} P p e =
  ( g) ∘
  ( ( exists-not-not-for-all-Fin
      ( number-of-elements-count e)
      ( p ∘ map-equiv-count e)) ∘ f)
  where
  k : ℕ
  k = number-of-elements-count e
  P' : Fin k → UU l2
  P' = P ∘ map-equiv (pr2 e)
  f : ¬ ((x : X) → P x) → ¬ ((x : Fin k) → P' x)
  f nf f' =
    nf
      ( λ x →
        tr
          ( P)
          ( htpy-eq-equiv (right-inverse-law-equiv (pr2 e)) x)
          ( f' (map-inv-equiv (pr2 e) x)))
  g : Σ (Fin k) (λ x → ¬ (P' x)) → Σ X (λ x → ¬ (P x))
  pr1 (g (pair l np)) = map-equiv (pr2 e) l
  pr2 (g (pair l np)) x = np x
```

```agda
is-lower-bound-Fin :
  {l : Level} (k : ℕ) (P : Fin k → UU l) → Fin k → UU l
is-lower-bound-Fin k P x = (y : Fin k) → P y → leq-Fin k x y

abstract
  is-prop-is-lower-bound-Fin :
    {l : Level} (k : ℕ) {P : Fin k → UU l} (x : Fin k) →
    is-prop (is-lower-bound-Fin k P x)
  is-prop-is-lower-bound-Fin k x =
    is-prop-Π (λ y → is-prop-function-type (is-prop-leq-Fin k x y))

  is-lower-bound-fin-Prop :
    {l : Level} (k : ℕ) (P : Fin k → UU l) (x : Fin k) → Prop l
  pr1 (is-lower-bound-fin-Prop k P x) = is-lower-bound-Fin k P x
  pr2 (is-lower-bound-fin-Prop k P x) = is-prop-is-lower-bound-Fin k x

minimal-element-Fin :
  {l : Level} (k : ℕ) (P : Fin k → UU l) → UU l
minimal-element-Fin k P =
  Σ (Fin k) (λ x → (P x) × is-lower-bound-Fin k P x)

abstract
  all-elements-equal-minimal-element-Fin :
    {l : Level} (k : ℕ) (P : subtype l (Fin k)) →
    all-elements-equal (minimal-element-Fin k (is-in-subtype P))
  all-elements-equal-minimal-element-Fin k P
    (pair x (pair p l)) (pair y (pair q m)) =
    eq-type-subtype
      ( λ t →
        product-Prop (P t) (is-lower-bound-fin-Prop k (is-in-subtype P) t))
      ( antisymmetric-leq-Fin k x y (l y q) (m x p))

abstract
  is-prop-minimal-element-Fin :
    {l : Level} (k : ℕ) (P : subtype l (Fin k)) →
    is-prop (minimal-element-Fin k (is-in-subtype P))
  is-prop-minimal-element-Fin k P =
    is-prop-all-elements-equal (all-elements-equal-minimal-element-Fin k P)

minimal-element-Fin-Prop :
  {l : Level} (k : ℕ) (P : subtype l (Fin k)) → Prop l
pr1 (minimal-element-Fin-Prop k P) = minimal-element-Fin k (is-in-subtype P)
pr2 (minimal-element-Fin-Prop k P) = is-prop-minimal-element-Fin k P

is-lower-bound-inl-Fin :
  {l : Level} (k : ℕ) {P : Fin (succ-ℕ k) → UU l} {x : Fin k} →
  is-lower-bound-Fin k (P ∘ inl) x →
  is-lower-bound-Fin (succ-ℕ k) P (inl-Fin k x)
is-lower-bound-inl-Fin k H (inl y) p = H y p
is-lower-bound-inl-Fin k {P} {x} H (inr star) p =
  ( leq-neg-one-Fin k (inl x))

well-ordering-principle-Σ-Fin :
  {l : Level} (k : ℕ) {P : Fin k → UU l} → ((x : Fin k) → is-decidable (P x)) →
  Σ (Fin k) P → minimal-element-Fin k P
pr1 (well-ordering-principle-Σ-Fin (succ-ℕ k) d (pair (inl x) p)) =
  inl (pr1 (well-ordering-principle-Σ-Fin k (λ x' → d (inl x')) (pair x p)))
pr1 (pr2 (well-ordering-principle-Σ-Fin (succ-ℕ k) d (pair (inl x) p))) =
  pr1 (pr2 (well-ordering-principle-Σ-Fin k (λ x' → d (inl x')) (pair x p)))
pr2 (pr2 (well-ordering-principle-Σ-Fin (succ-ℕ k) d (pair (inl x) p))) =
  is-lower-bound-inl-Fin k (pr2 (pr2 m))
  where
  m = well-ordering-principle-Σ-Fin k (λ x' → d (inl x')) (pair x p)
well-ordering-principle-Σ-Fin (succ-ℕ k) {P} d (pair (inr star) p)
  with
  is-decidable-Σ-Fin k (λ t → d (inl t))
... | inl t =
  pair
    ( inl (pr1 m))
    ( pair (pr1 (pr2 m)) (is-lower-bound-inl-Fin k (pr2 (pr2 m))))
  where
  m = well-ordering-principle-Σ-Fin k (λ x' → d (inl x')) t
... | inr f =
  pair
    ( inr star)
    ( pair p g)
  where
  g : (y : Fin (succ-ℕ k)) → P y → leq-Fin (succ-ℕ k) (neg-one-Fin k) y
  g (inl y) q = ex-falso (f (pair y q))
  g (inr star) q = refl-leq-Fin (succ-ℕ k) (neg-one-Fin k)

well-ordering-principle-∃-Fin :
  {l : Level} (k : ℕ) (P : decidable-subtype l (Fin k)) →
  exists (Fin k) (subtype-decidable-subtype P) →
  minimal-element-Fin k (is-in-decidable-subtype P)
well-ordering-principle-∃-Fin k P H =
  apply-universal-property-trunc-Prop H
    ( minimal-element-Fin-Prop k (subtype-decidable-subtype P))
    ( well-ordering-principle-Σ-Fin k
      ( is-decidable-decidable-subtype P))
```

### Hilbert's `ε`-operator for decidable subtypes of standard finite types

```agda
ε-operator-decidable-subtype-Fin :
  {l : Level} (k : ℕ) (P : decidable-subtype l (Fin k)) →
  ε-operator-Hilbert (type-decidable-subtype P)
ε-operator-decidable-subtype-Fin {l} zero-ℕ P t =
  ex-falso (apply-universal-property-trunc-Prop t empty-Prop pr1)
ε-operator-decidable-subtype-Fin {l} (succ-ℕ k) P t =
  map-Σ
    ( is-in-decidable-subtype P)
    ( mod-succ-ℕ k)
    ( λ x → id)
    ( ε-operator-total-Q
      ( map-trunc-Prop
        ( map-Σ
          ( type-Prop ∘ Q)
          ( nat-Fin (succ-ℕ k))
          ( λ x →
            tr (is-in-decidable-subtype P) (inv (is-section-nat-Fin k x))))
        ( t)))
  where
  Q : ℕ → Prop l
  Q n = subtype-decidable-subtype P (mod-succ-ℕ k n)
  is-decidable-Q : (n : ℕ) → is-decidable (type-Prop (Q n))
  is-decidable-Q n =
    is-decidable-decidable-subtype P (mod-succ-ℕ k n)
  ε-operator-total-Q : ε-operator-Hilbert (type-subtype Q)
  ε-operator-total-Q =
    ε-operator-decidable-subtype-ℕ Q is-decidable-Q
```

```agda
abstract
  elim-trunc-decidable-fam-Fin :
    {l1 : Level} {k : ℕ} {B : Fin k → UU l1} →
    ((x : Fin k) → is-decidable (B x)) →
    type-trunc-Prop (Σ (Fin k) B) → Σ (Fin k) B
  elim-trunc-decidable-fam-Fin {l1} {zero-ℕ} {B} d y =
    ex-falso (is-empty-type-trunc-Prop pr1 y)
  elim-trunc-decidable-fam-Fin {l1} {succ-ℕ k} {B} d y
    with d (inr star)
  ... | inl x = pair (inr star) x
  ... | inr f =
    map-Σ-map-base inl B
      ( elim-trunc-decidable-fam-Fin {l1} {k} {B ∘ inl}
        ( λ x → d (inl x))
        ( map-equiv-trunc-Prop
          ( ( ( right-unit-law-coproduct-is-empty
                ( Σ (Fin k) (B ∘ inl))
                ( B (inr star)) f) ∘e
              ( equiv-coproduct id-equiv (left-unit-law-Σ (B ∘ inr)))) ∘e
            ( right-distributive-Σ-coproduct (Fin k) unit B))
          ( y)))
```
