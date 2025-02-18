# Constant maps

```agda
module foundation.constant-maps where

open import foundation-core.constant-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.0-maps
open import foundation.action-on-homotopies-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.faithful-maps
open import foundation.function-extensionality
open import foundation.functoriality-dependent-pair-types
open import foundation.images
open import foundation.morphisms-arrows
open import foundation.postcomposition-functions
open import foundation.propositional-truncations
open import foundation.retracts-of-maps
open import foundation.retracts-of-types
open import foundation.transposition-identifications-along-equivalences
open import foundation.type-arithmetic-unit-type
open import foundation.type-theoretic-principle-of-choice
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.1-types
open import foundation-core.commuting-squares-of-maps
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Properties

### The action on homotopies of a constant map is constant

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} {B : A → UU l2} {C : UU l3}
  {f g : (x : A) → B x}
  where

  compute-action-htpy-function-const :
    (c : C) (H : f ~ g) →
    action-htpy-function (const ((x : A) → B x) c) H ＝ refl
  compute-action-htpy-function-const c H = ap-const c (eq-htpy H)
```

### Computing the fibers of point inclusions

```agda
module _
  {l : Level} {A : UU l} (x y : A)
  where

  compute-fiber-point : fiber (point x) y ≃ (x ＝ y)
  compute-fiber-point = left-unit-law-product

  map-compute-fiber-point : fiber (point x) y → (x ＝ y)
  map-compute-fiber-point = map-equiv compute-fiber-point

  map-inv-compute-fiber-point : (x ＝ y) → fiber (point x) y
  map-inv-compute-fiber-point = map-inv-equiv compute-fiber-point

  is-equiv-map-compute-fiber-point : is-equiv map-compute-fiber-point
  is-equiv-map-compute-fiber-point = is-equiv-map-equiv compute-fiber-point
```

### A type is `k+1`-truncated if and only if all point inclusions are `k`-truncated maps

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-trunc-map-point-is-trunc :
      (k : 𝕋) → is-trunc (succ-𝕋 k) A →
      (x : A) → is-trunc-map k (point x)
    is-trunc-map-point-is-trunc k is-trunc-A x y =
      is-trunc-equiv k
        ( x ＝ y)
        ( compute-fiber-point x y)
        ( is-trunc-A x y)

  abstract
    is-trunc-is-trunc-map-point :
      (k : 𝕋) → ((x : A) → is-trunc-map k (point x)) →
      is-trunc (succ-𝕋 k) A
    is-trunc-is-trunc-map-point k is-trunc-point x y =
      is-trunc-equiv' k
        ( Σ unit (λ _ → x ＝ y))
        ( left-unit-law-Σ (λ _ → x ＝ y))
        ( is-trunc-point x y)

  abstract
    is-contr-map-point-is-prop :
      is-prop A → (x : A) → is-contr-map (point x)
    is-contr-map-point-is-prop = is-trunc-map-point-is-trunc neg-two-𝕋

  abstract
    is-equiv-point-is-prop :
      is-prop A → (x : A) → is-equiv (point x)
    is-equiv-point-is-prop H x =
      is-equiv-is-contr-map (is-contr-map-point-is-prop H x)

  abstract
    is-prop-map-point-is-set :
      is-set A → (x : A) → is-prop-map (point x)
    is-prop-map-point-is-set = is-trunc-map-point-is-trunc neg-one-𝕋

  abstract
    is-emb-point-is-set : is-set A → (x : A) → is-emb (point x)
    is-emb-point-is-set H x = is-emb-is-prop-map (is-prop-map-point-is-set H x)

  abstract
    is-0-map-point-is-1-type : is-1-type A → (x : A) → is-0-map (point x)
    is-0-map-point-is-1-type = is-trunc-map-point-is-trunc zero-𝕋

  abstract
    is-faithful-point-is-1-type :
      is-1-type A → (x : A) → is-faithful (point x)
    is-faithful-point-is-1-type H x =
      is-faithful-is-0-map (is-0-map-point-is-1-type H x)

  abstract
    is-prop-is-contr-map-point :
      ((x : A) → is-contr-map (point x)) → is-prop A
    is-prop-is-contr-map-point = is-trunc-is-trunc-map-point neg-two-𝕋

  abstract
    is-prop-is-equiv-point :
      ((x : A) → is-equiv (point x)) → is-prop A
    is-prop-is-equiv-point H =
      is-prop-is-contr-map-point (is-contr-map-is-equiv ∘ H)

  abstract
    is-set-is-prop-map-point :
      ((x : A) → is-prop-map (point x)) → is-set A
    is-set-is-prop-map-point = is-trunc-is-trunc-map-point neg-one-𝕋

  abstract
    is-set-is-emb-point :
      ((x : A) → is-emb (point x)) → is-set A
    is-set-is-emb-point H =
      is-set-is-prop-map-point (is-prop-map-is-emb ∘ H)

  abstract
    is-1-type-is-0-map-point :
      ((x : A) → is-0-map (point x)) → is-1-type A
    is-1-type-is-0-map-point = is-trunc-is-trunc-map-point zero-𝕋

  abstract
    is-1-type-is-faithful-point :
      ((x : A) → is-faithful (point x)) → is-1-type A
    is-1-type-is-faithful-point H =
      is-1-type-is-0-map-point (is-0-map-is-faithful ∘ H)

point-equiv :
  {l : Level} (A : Prop l) (x : type-Prop A) → unit ≃ type-Prop A
pr1 (point-equiv A x) = point x
pr2 (point-equiv A x) = is-equiv-point-is-prop (is-prop-type-Prop A) x

point-emb :
  {l : Level} (A : Set l) (x : type-Set A) → unit ↪ type-Set A
pr1 (point-emb A x) = point x
pr2 (point-emb A x) = is-emb-point-is-set (is-set-type-Set A) x

point-faithful-map :
  {l : Level} (A : 1-Type l) (x : type-1-Type A) →
  faithful-map unit (type-1-Type A)
pr1 (point-faithful-map A x) = point x
pr2 (point-faithful-map A x) =
  is-faithful-point-is-1-type (is-1-type-type-1-Type A) x
```

### The image of a constant map into a set is contractible

```agda
abstract
  is-contr-im :
    {l1 l2 : Level} {A : UU l1} (B : Set l2) {f : A → type-Set B}
    (a : A) (H : (x : A) → f x ＝ f a) → is-contr (im f)
  pr1 (is-contr-im B {f} a H) = map-unit-im f a
  pr2 (is-contr-im B {f} a H) (x , u) =
    apply-dependent-universal-property-trunc-Prop
      ( λ v → Id-Prop (im-Set B f) (map-unit-im f a) (x , v))
      ( u)
      ( λ where
        ( a' , refl) →
          eq-Eq-im f (map-unit-im f a) (map-unit-im f a') (inv (H a')))
```

## See also

- [Constant pointed maps](structured-types.constant-pointed-maps.md)
