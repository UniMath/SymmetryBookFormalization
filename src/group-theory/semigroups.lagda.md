# Semigroups

```agda
module group-theory.semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import structured-types.magmas
```

</details>

## Idea

{{#concept "Semigroups" WDID=Q207348 WD="semigroup" Agda=Semigroup}} are
[sets](foundation-core.sets.md) [equipped](foundation.structure.md) with an
associative binary operation.

## Definitions

```agda
has-associative-mul : {l : Level} (X : UU l) → UU l
has-associative-mul X =
  Σ (X → X → X) (λ μ → (x y z : X) → μ (μ x y) z ＝ μ x (μ y z))

has-associative-mul-Set :
  {l : Level} (X : Set l) → UU l
has-associative-mul-Set X =
  has-associative-mul (type-Set X)

Semigroup :
  (l : Level) → UU (lsuc l)
Semigroup l = Σ (Set l) has-associative-mul-Set

module _
  {l : Level} (G : Semigroup l)
  where

  set-Semigroup : Set l
  set-Semigroup = pr1 G

  type-Semigroup : UU l
  type-Semigroup = type-Set set-Semigroup

  is-set-type-Semigroup : is-set type-Semigroup
  is-set-type-Semigroup = is-set-type-Set set-Semigroup

  has-associative-mul-Semigroup : has-associative-mul type-Semigroup
  has-associative-mul-Semigroup = pr2 G

  mul-Semigroup : type-Semigroup → type-Semigroup → type-Semigroup
  mul-Semigroup = pr1 has-associative-mul-Semigroup

  mul-Semigroup' : type-Semigroup → type-Semigroup → type-Semigroup
  mul-Semigroup' x y = mul-Semigroup y x

  ap-mul-Semigroup :
    {x x' y y' : type-Semigroup} →
    x ＝ x' → y ＝ y' → mul-Semigroup x y ＝ mul-Semigroup x' y'
  ap-mul-Semigroup p q = ap-binary mul-Semigroup p q

  associative-mul-Semigroup :
    (x y z : type-Semigroup) →
    Id
      ( mul-Semigroup (mul-Semigroup x y) z)
      ( mul-Semigroup x (mul-Semigroup y z))
  associative-mul-Semigroup = pr2 has-associative-mul-Semigroup

  left-swap-mul-Semigroup :
    {x y z : type-Semigroup} → mul-Semigroup x y ＝ mul-Semigroup y x →
    mul-Semigroup x (mul-Semigroup y z) ＝
    mul-Semigroup y (mul-Semigroup x z)
  left-swap-mul-Semigroup H =
    ( inv (associative-mul-Semigroup _ _ _)) ∙
    ( ap (mul-Semigroup' _) H) ∙
    ( associative-mul-Semigroup _ _ _)

  right-swap-mul-Semigroup :
    {x y z : type-Semigroup} → mul-Semigroup y z ＝ mul-Semigroup z y →
    mul-Semigroup (mul-Semigroup x y) z ＝
    mul-Semigroup (mul-Semigroup x z) y
  right-swap-mul-Semigroup H =
    ( associative-mul-Semigroup _ _ _) ∙
    ( ap (mul-Semigroup _) H) ∙
    ( inv (associative-mul-Semigroup _ _ _))

  interchange-mul-mul-Semigroup :
    {x y z w : type-Semigroup} → mul-Semigroup y z ＝ mul-Semigroup z y →
    mul-Semigroup (mul-Semigroup x y) (mul-Semigroup z w) ＝
    mul-Semigroup (mul-Semigroup x z) (mul-Semigroup y w)
  interchange-mul-mul-Semigroup H =
    ( associative-mul-Semigroup _ _ _) ∙
    ( ap (mul-Semigroup _) (left-swap-mul-Semigroup H)) ∙
    ( inv (associative-mul-Semigroup _ _ _))

  magma-Semigroup : Magma l
  pr1 magma-Semigroup = type-Semigroup
  pr2 magma-Semigroup = mul-Semigroup
```

### The structure of a semigroup

```agda
structure-semigroup :
  {l1 : Level} → UU l1 → UU l1
structure-semigroup X =
  Σ (is-set X) (λ p → has-associative-mul-Set (X , p))

semigroup-structure-semigroup :
  {l1 : Level} → (X : UU l1) → structure-semigroup X → Semigroup l1
pr1 (semigroup-structure-semigroup X (s , g)) = X , s
pr2 (semigroup-structure-semigroup X (s , g)) = g
```
