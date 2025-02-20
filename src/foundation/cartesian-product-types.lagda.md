# Cartesian product types

```agda
module foundation.cartesian-product-types where

open import foundation-core.cartesian-product-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.subuniverses
open import foundation.universe-levels

open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.retracts-of-types
open import foundation-core.sections
open import foundation-core.transport-along-identifications
```

</details>

## Properties

### Transport in a family of cartesian products

```agda
tr-product :
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A}
  (B C : A → UU l2) (p : a0 ＝ a1) (u : B a0 × C a0) →
  (tr (λ a → B a × C a) p u) ＝ (pair (tr B p (pr1 u)) (tr C p (pr2 u)))
tr-product B C refl u = refl
```

### Subuniverses closed under cartesian product types

```agda
is-closed-under-products-subuniverses :
  {l1 l2 l3 l4 l5 : Level} (P : subuniverse l1 l2) (Q : subuniverse l3 l4)
  (R : subuniverse (l1 ⊔ l3) l5) → UU (lsuc l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4 ⊔ l5)
is-closed-under-products-subuniverses {l1} {l2} {l3} P Q R =
  {X : UU l1} {Y : UU l3} →
  is-in-subuniverse P X → is-in-subuniverse Q Y → is-in-subuniverse R (X × Y)

is-closed-under-products-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU (lsuc l1 ⊔ l2)
is-closed-under-products-subuniverse P =
  is-closed-under-products-subuniverses P P P
```

### If a factor has an element, then the opposite factor is a retract of the product

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  section-pr1-product : Y → section (pr1 {A = X} {B = λ _ → Y})
  section-pr1-product y = ((λ x → (x , y)) , refl-htpy)

  retract-left-factor-product : Y → X retract-of (X × Y)
  retract-left-factor-product y = retract-section pr1 (section-pr1-product y)

  section-pr2-product : X → section (pr2 {A = X} {B = λ _ → Y})
  section-pr2-product x = ((λ y → (x , y)) , refl-htpy)

  retract-right-factor-product : X → Y retract-of (X × Y)
  retract-right-factor-product x = retract-section pr2 (section-pr2-product x)
```
