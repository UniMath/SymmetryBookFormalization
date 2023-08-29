# Functoriality of function types

```agda
module foundation.functoriality-function-types where

open import foundation-core.functoriality-function-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.transport
open import foundation.type-theoretic-principle-of-choice
open import foundation.unit-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.constant-maps
open import foundation-core.embeddings
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositional-maps
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Properties

### An equivalence of domain and codomain induce an equivalence on function types

```agda
module _
  { l1 l2 l3 l4 : Level}
  { A' : UU l1} {B' : UU l2} {A : UU l3} (B : UU l4)
  ( e : A' ≃ A) (f : B' ≃ B)
  where

  map-equiv-function-type : (A' → B') → (A → B)
  map-equiv-function-type h = map-equiv f ∘ (h ∘ map-inv-equiv e)

  compute-map-equiv-function-type :
    (h : A' → B') (x : A') →
    map-equiv-function-type h (map-equiv e x) ＝ map-equiv f (h x)
  compute-map-equiv-function-type h x =
    ap (map-equiv f ∘ h) (is-retraction-map-inv-equiv e x)

  is-equiv-map-equiv-function-type : is-equiv map-equiv-function-type
  is-equiv-map-equiv-function-type =
    is-equiv-comp
      ( precomp (map-equiv (inv-equiv e)) B)
      ( postcomp A' (map-equiv f))
      ( is-equiv-postcomp-equiv f A')
      ( is-equiv-precomp-equiv (inv-equiv e) B)

  equiv-function-type : (A' → B') ≃ (A → B)
  pr1 equiv-function-type = map-equiv-function-type
  pr2 equiv-function-type = is-equiv-map-equiv-function-type
```

### TODO

```agda
is-trunc-map-postcomp-is-trunc-map :
  {l1 l2 l3 : Level} (k : 𝕋) (A : UU l3) {X : UU l1} {Y : UU l2} (f : X → Y) →
  is-trunc-map k f → is-trunc-map k (postcomp A f)
is-trunc-map-postcomp-is-trunc-map k A {X} {Y} f is-trunc-f =
  is-trunc-map-map-Π-is-trunc-map' k
    ( const A unit star)
    ( const unit (X → Y) f)
    ( const unit (is-trunc-map k f) is-trunc-f)

is-trunc-map-is-trunc-map-postcomp :
  {l1 l2 : Level} (k : 𝕋) {X : UU l1} {Y : UU l2} (f : X → Y) →
  ( {l3 : Level} (A : UU l3) → is-trunc-map k (postcomp A f)) →
  is-trunc-map k f
is-trunc-map-is-trunc-map-postcomp k {X} {Y} f is-trunc-post-f =
  is-trunc-map-is-trunc-map-map-Π' k
    ( const unit (X → Y) f)
    ( λ {l} {J} α → is-trunc-post-f {l} J)
    ( star)
```

### The precomposition function preserves homotopies

```agda
htpy-precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {f g : A → B} (H : f ~ g) (C : UU l3) →
  (precomp f C) ~ (precomp g C)
htpy-precomp H C h = eq-htpy (h ·l H)

compute-htpy-precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : UU l3) →
  (htpy-precomp (refl-htpy' f) C) ~ refl-htpy
compute-htpy-precomp f C h = eq-htpy-refl-htpy (h ∘ f)
```

## See also

- Functorial properties of dependent function types are recorded in
  [`foundation.functoriality-dependent-function-types`](foundation.functoriality-dependent-function-types.md).
- Arithmetical laws involving dependent function types are recorded in
  [`foundation.type-arithmetic-dependent-function-types`](foundation.type-arithmetic-dependent-function-types.md).
- Equality proofs in dependent function types are characterized in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).
