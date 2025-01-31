# Truncations

```agda
module foundation.truncations where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.truncated-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.contractible-maps
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
open import foundation-core.truncation-levels
open import foundation-core.universal-property-truncation
```

</details>

## Idea

We postulate the existence of truncations.

## Postulates

```agda
postulate
  type-trunc : {l : Level} (k : 𝕋) → UU l → UU l

postulate
  is-trunc-type-trunc :
    {l : Level} {k : 𝕋} {A : UU l} → is-trunc k (type-trunc k A)

trunc : {l : Level} (k : 𝕋) → UU l → Truncated-Type l k
pr1 (trunc k A) = type-trunc k A
pr2 (trunc k A) = is-trunc-type-trunc

postulate
  unit-trunc : {l : Level} {k : 𝕋} {A : UU l} → A → type-trunc k A

postulate
  is-truncation-trunc :
    {l : Level} {k : 𝕋} {A : UU l} →
    is-truncation (trunc k A) unit-trunc

equiv-universal-property-trunc :
  {l1 l2 : Level} {k : 𝕋} (A : UU l1) (B : Truncated-Type l2 k) →
  (type-trunc k A → type-Truncated-Type B) ≃ (A → type-Truncated-Type B)
pr1 (equiv-universal-property-trunc A B) = precomp-Trunc unit-trunc B
pr2 (equiv-universal-property-trunc A B) = is-truncation-trunc B
```

## Properties

### The `n`-truncations satisfy the universal property of `n`-truncations

```agda
universal-property-trunc :
  {l1 : Level} (k : 𝕋) (A : UU l1) →
  universal-property-truncation (trunc k A) unit-trunc
universal-property-trunc k A =
  universal-property-truncation-is-truncation
    ( trunc k A)
    ( unit-trunc)
    ( is-truncation-trunc)

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1}
  where

  apply-universal-property-trunc :
    (B : Truncated-Type l2 k) (f : A → type-Truncated-Type B) →
    Σ ( type-trunc k A → type-Truncated-Type B)
      ( λ h → h ∘ unit-trunc ~ f)
  apply-universal-property-trunc B f =
    center
      ( universal-property-truncation-is-truncation
        ( trunc k A)
        ( unit-trunc)
        ( is-truncation-trunc)
        ( B)
        ( f))

  map-universal-property-trunc :
    (B : Truncated-Type l2 k) → (A → type-Truncated-Type B) →
    type-trunc k A → type-Truncated-Type B
  map-universal-property-trunc B f =
    pr1 (apply-universal-property-trunc B f)

  triangle-universal-property-trunc :
    (B : Truncated-Type l2 k) (f : A → type-Truncated-Type B) →
    map-universal-property-trunc B f ∘ unit-trunc ~ f
  triangle-universal-property-trunc B f =
    pr2 (apply-universal-property-trunc B f)
```

### The `n`-truncations satisfy the dependent universal property of `n`-truncations

```agda
module _
  {l1 : Level} {k : 𝕋} {A : UU l1}
  where

  dependent-universal-property-trunc :
    dependent-universal-property-truncation (trunc k A) unit-trunc
  dependent-universal-property-trunc =
    dependent-universal-property-truncation-is-truncation
      ( trunc k A)
      ( unit-trunc)
      ( is-truncation-trunc)

  equiv-dependent-universal-property-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k) →
    ((x : type-trunc k A) → type-Truncated-Type (B x)) ≃
    ((a : A) → type-Truncated-Type (B (unit-trunc a)))
  pr1 (equiv-dependent-universal-property-trunc B) =
    precomp-Π-Truncated-Type unit-trunc B
  pr2 (equiv-dependent-universal-property-trunc B) =
    dependent-universal-property-trunc B

  unique-dependent-function-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k)
    (f : (x : A) → type-Truncated-Type (B (unit-trunc x))) →
    is-contr
      ( Σ ( (x : type-trunc k A) → type-Truncated-Type (B x))
          ( λ h → (h ∘ unit-trunc) ~ f))
  unique-dependent-function-trunc B f =
    is-contr-equiv'
      ( fiber (precomp-Π-Truncated-Type unit-trunc B) f)
      ( equiv-tot (λ h → equiv-funext))
      ( is-contr-map-is-equiv (dependent-universal-property-trunc B) f)

  apply-dependent-universal-property-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k) →
    (f : (x : A) → type-Truncated-Type (B (unit-trunc x))) →
    Σ ( (x : type-trunc k A) → type-Truncated-Type (B x))
      ( λ h → (h ∘ unit-trunc) ~ f)
  apply-dependent-universal-property-trunc B f =
    center (unique-dependent-function-trunc B f)

  function-dependent-universal-property-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k) →
    (f : (x : A) → type-Truncated-Type (B (unit-trunc x))) →
    (x : type-trunc k A) → type-Truncated-Type (B x)
  function-dependent-universal-property-trunc B f =
    pr1 (apply-dependent-universal-property-trunc B f)

  htpy-dependent-universal-property-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k) →
    (f : (x : A) → type-Truncated-Type (B (unit-trunc x))) →
    ( function-dependent-universal-property-trunc B f ∘ unit-trunc) ~ f
  htpy-dependent-universal-property-trunc B f =
    pr2 (apply-dependent-universal-property-trunc B f)
```

### Families of `k`-truncated-types over `k+1`-truncations of types

```agda
unique-truncated-fam-trunc :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} →
  (B : A → Truncated-Type l2 k) →
  is-contr
    ( Σ ( type-trunc (succ-𝕋 k) A → Truncated-Type l2 k)
        ( λ C → (x : A) → type-equiv-Truncated-Type (B x) (C (unit-trunc x))))
unique-truncated-fam-trunc {l1} {l2} {k} {A} B =
  is-contr-equiv'
    ( Σ ( type-trunc (succ-𝕋 k) A → Truncated-Type l2 k)
        ( λ C → (C ∘ unit-trunc) ~ B))
    ( equiv-tot
      ( λ C →
        equiv-Π-equiv-family
          ( λ x →
            ( extensionality-Truncated-Type (B x) (C (unit-trunc x))) ∘e
            ( equiv-inv (C (unit-trunc x)) (B x)))))
    ( universal-property-trunc
      ( succ-𝕋 k)
      ( A)
      ( Truncated-Type-Truncated-Type l2 k)
      ( B))

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : A → Truncated-Type l2 k)
  where

  truncated-fam-trunc : type-trunc (succ-𝕋 k) A → Truncated-Type l2 k
  truncated-fam-trunc =
    pr1 (center (unique-truncated-fam-trunc B))

  fam-trunc : type-trunc (succ-𝕋 k) A → UU l2
  fam-trunc = type-Truncated-Type ∘ truncated-fam-trunc

  compute-truncated-fam-trunc :
    (x : A) →
    type-equiv-Truncated-Type (B x) (truncated-fam-trunc (unit-trunc x))
  compute-truncated-fam-trunc =
    pr2 (center (unique-truncated-fam-trunc B))

  map-compute-truncated-fam-trunc :
    (x : A) → type-Truncated-Type (B x) → (fam-trunc (unit-trunc x))
  map-compute-truncated-fam-trunc x =
    map-equiv (compute-truncated-fam-trunc x)

  total-truncated-fam-trunc : UU (l1 ⊔ l2)
  total-truncated-fam-trunc = Σ (type-trunc (succ-𝕋 k) A) fam-trunc

module _
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} (B : A → Truncated-Type l2 k)
  ( C : total-truncated-fam-trunc B → Truncated-Type l3 k)
  ( f :
    ( x : A)
    ( y : type-Truncated-Type (B x)) →
    type-Truncated-Type
      ( C (unit-trunc x , map-equiv (compute-truncated-fam-trunc B x) y)))
  where

  dependent-universal-property-total-truncated-fam-trunc :
    is-contr
      ( Σ ( (t : total-truncated-fam-trunc B) → type-Truncated-Type (C t))
          ( λ h →
            (x : A) (y : type-Truncated-Type (B x)) →
            Id
              ( h (unit-trunc x , map-compute-truncated-fam-trunc B x y))
              ( f x y)))
  dependent-universal-property-total-truncated-fam-trunc =
    is-contr-equiv _
      ( equiv-Σ
        ( λ g →
          (x : A) →
          Id
            ( g (unit-trunc x))
            ( map-equiv-Π
              ( λ u → type-Truncated-Type (C (unit-trunc x , u)))
              ( compute-truncated-fam-trunc B x)
              ( λ u → id-equiv)
              ( f x)))
        ( equiv-ev-pair)
        ( λ g →
          equiv-Π-equiv-family
            ( λ x →
              ( inv-equiv equiv-funext) ∘e
              ( equiv-Π
                ( λ y →
                  Id
                    ( g (unit-trunc x , y))
                    ( map-equiv-Π
                      ( λ u →
                        type-Truncated-Type (C (unit-trunc x , u)))
                      ( compute-truncated-fam-trunc B x)
                      ( λ u → id-equiv)
                      ( f x)
                      ( y)))
                ( compute-truncated-fam-trunc B x)
                ( λ y →
                  equiv-concat'
                    ( g (unit-trunc x , map-compute-truncated-fam-trunc B x y))
                    ( inv
                      ( compute-map-equiv-Π
                        ( λ u → type-Truncated-Type (C (unit-trunc x , u)))
                        ( compute-truncated-fam-trunc B x)
                        ( λ y → id-equiv)
                        ( f x)
                        ( y))))))))
      ( unique-dependent-function-trunc
        ( λ y →
          truncated-type-succ-Truncated-Type k
            ( Π-Truncated-Type k
              ( truncated-fam-trunc B y)
              ( λ u → C (y , u))))
        ( λ y →
          map-equiv-Π
            ( λ u → type-Truncated-Type (C (unit-trunc y , u)))
            ( compute-truncated-fam-trunc B y)
            ( λ u → id-equiv)
            ( f y)))

  function-dependent-universal-property-total-truncated-fam-trunc :
    (t : total-truncated-fam-trunc B) → type-Truncated-Type (C t)
  function-dependent-universal-property-total-truncated-fam-trunc =
    pr1 (center dependent-universal-property-total-truncated-fam-trunc)

  htpy-dependent-universal-property-total-truncated-fam-trunc :
    (x : A) (y : type-Truncated-Type (B x)) →
    Id
      ( function-dependent-universal-property-total-truncated-fam-trunc
        ( unit-trunc x , map-compute-truncated-fam-trunc B x y))
      ( f x y)
  htpy-dependent-universal-property-total-truncated-fam-trunc =
    pr2 (center dependent-universal-property-total-truncated-fam-trunc)
```

### An `n`-truncated type is equivalent to its `n`-truncation

```agda
module _
  {l : Level} {k : 𝕋} (A : Truncated-Type l k)
  where

  map-inv-unit-trunc :
    type-trunc k (type-Truncated-Type A) → type-Truncated-Type A
  map-inv-unit-trunc = map-universal-property-trunc A id

  is-retraction-map-inv-unit-trunc :
    ( map-inv-unit-trunc ∘ unit-trunc) ~ id
  is-retraction-map-inv-unit-trunc = triangle-universal-property-trunc A id

  is-section-map-inv-unit-trunc :
    ( unit-trunc ∘ map-inv-unit-trunc) ~ id
  is-section-map-inv-unit-trunc =
    htpy-eq
      ( pr1
        ( pair-eq-Σ
          ( eq-is-prop'
            ( is-trunc-succ-is-trunc
              ( neg-two-𝕋)
              ( universal-property-trunc
                ( k)
                ( type-Truncated-Type A)
                ( trunc k (type-Truncated-Type A))
                ( unit-trunc)))
            ( unit-trunc ∘ map-inv-unit-trunc ,
              unit-trunc ·l is-retraction-map-inv-unit-trunc)
            ( id , refl-htpy))))

  is-equiv-unit-trunc : is-equiv unit-trunc
  is-equiv-unit-trunc =
    is-equiv-is-invertible
      map-inv-unit-trunc
      is-section-map-inv-unit-trunc
      is-retraction-map-inv-unit-trunc

  equiv-unit-trunc :
    type-Truncated-Type A ≃ type-trunc k (type-Truncated-Type A)
  pr1 equiv-unit-trunc = unit-trunc
  pr2 equiv-unit-trunc = is-equiv-unit-trunc
```

### A contractible type is equivalent to its `k`-truncation

```agda
module _
  {l : Level} (k : 𝕋) (A : UU l)
  where

  is-equiv-unit-trunc-is-contr : is-contr A → is-equiv unit-trunc
  is-equiv-unit-trunc-is-contr c =
    is-equiv-unit-trunc (A , is-trunc-is-contr k c)

  is-contr-type-trunc : is-contr A → is-contr (type-trunc k A)
  is-contr-type-trunc H =
    is-contr-is-equiv' A unit-trunc (is-equiv-unit-trunc-is-contr H) H
```

### Truncation is idempotent

```agda
module _
  {l : Level} (k : 𝕋) (A : UU l)
  where

  idempotent-trunc : type-trunc k (type-trunc k A) ≃ type-trunc k A
  idempotent-trunc = inv-equiv (equiv-unit-trunc (trunc k A))
```

### Characterization of the identity types of truncations

```agda
module _
  {l : Level} (k : 𝕋) {A : UU l} (a : A)
  where

  Eq-trunc-Truncated-Type : type-trunc (succ-𝕋 k) A → Truncated-Type l k
  Eq-trunc-Truncated-Type = truncated-fam-trunc (λ y → trunc k (a ＝ y))

  Eq-trunc : type-trunc (succ-𝕋 k) A → UU l
  Eq-trunc x = type-Truncated-Type (Eq-trunc-Truncated-Type x)

  compute-Eq-trunc : (x : A) → type-trunc k (a ＝ x) ≃ Eq-trunc (unit-trunc x)
  compute-Eq-trunc = compute-truncated-fam-trunc (λ y → trunc k (a ＝ y))

  map-compute-Eq-trunc :
    (x : A) → type-trunc k (a ＝ x) → Eq-trunc (unit-trunc x)
  map-compute-Eq-trunc x = map-equiv (compute-Eq-trunc x)

  refl-Eq-trunc : Eq-trunc (unit-trunc a)
  refl-Eq-trunc = map-compute-Eq-trunc a (unit-trunc refl)

  refl-compute-Eq-trunc :
    map-compute-Eq-trunc a (unit-trunc refl) ＝ refl-Eq-trunc
  refl-compute-Eq-trunc = refl

  is-torsorial-Eq-trunc : is-torsorial Eq-trunc
  pr1 (pr1 is-torsorial-Eq-trunc) = unit-trunc a
  pr2 (pr1 is-torsorial-Eq-trunc) = refl-Eq-trunc
  pr2 is-torsorial-Eq-trunc =
    function-dependent-universal-property-total-truncated-fam-trunc
      ( λ y → trunc k (a ＝ y))
      ( Id-Truncated-Type
          ( Σ-Truncated-Type
            ( trunc (succ-𝕋 k) A)
            ( λ b →
              truncated-type-succ-Truncated-Type k
                ( Eq-trunc-Truncated-Type b)))
          ( unit-trunc a , refl-Eq-trunc))
      ( λ y →
        function-dependent-universal-property-trunc
          ( λ q →
            Id-Truncated-Type
              ( Σ-Truncated-Type
                ( trunc (succ-𝕋 k) A)
                ( λ y →
                  truncated-type-succ-Truncated-Type k
                    ( Eq-trunc-Truncated-Type y)))
              ( unit-trunc a , refl-Eq-trunc)
              ( unit-trunc y , map-compute-Eq-trunc y q))
          ( r y))
    where
    r :
      (y : A) (p : a ＝ y) →
      Id
        { A = Σ (type-trunc (succ-𝕋 k) A) Eq-trunc}
        ( unit-trunc a , refl-Eq-trunc)
        ( unit-trunc y , (map-compute-Eq-trunc y (unit-trunc p)))
    r .a refl = refl

  Eq-eq-trunc : (x : type-trunc (succ-𝕋 k) A) → (unit-trunc a ＝ x) → Eq-trunc x
  Eq-eq-trunc .(unit-trunc a) refl = refl-Eq-trunc

  is-equiv-Eq-eq-trunc :
    (x : type-trunc (succ-𝕋 k) A) → is-equiv (Eq-eq-trunc x)
  is-equiv-Eq-eq-trunc =
    fundamental-theorem-id
      ( is-torsorial-Eq-trunc)
      ( Eq-eq-trunc)

  extensionality-trunc :
    (x : type-trunc (succ-𝕋 k) A) → (unit-trunc a ＝ x) ≃ Eq-trunc x
  pr1 (extensionality-trunc x) = Eq-eq-trunc x
  pr2 (extensionality-trunc x) = is-equiv-Eq-eq-trunc x

  effectiveness-trunc :
    (x : A) →
    type-trunc k (a ＝ x) ≃ (unit-trunc {k = succ-𝕋 k} a ＝ unit-trunc x)
  effectiveness-trunc x =
    inv-equiv (extensionality-trunc (unit-trunc x)) ∘e compute-Eq-trunc x

  map-effectiveness-trunc :
    (x : A) →
    type-trunc k (a ＝ x) → (unit-trunc {k = succ-𝕋 k} a ＝ unit-trunc x)
  map-effectiveness-trunc x = map-equiv (effectiveness-trunc x)

  refl-effectiveness-trunc :
    map-effectiveness-trunc a (unit-trunc refl) ＝ refl
  refl-effectiveness-trunc =
    is-retraction-map-inv-equiv (extensionality-trunc (unit-trunc a)) refl
```

### Truncations of Σ-types

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2}
  where

  map-trunc-Σ :
    type-trunc k (Σ A B) → type-trunc k (Σ A (λ x → type-trunc k (B x)))
  map-trunc-Σ =
    map-universal-property-trunc
      ( trunc k (Σ A (λ x → type-trunc k (B x))))
      ( λ (a , b) → unit-trunc (a , unit-trunc b))

  map-inv-trunc-Σ :
    type-trunc k (Σ A (λ x → type-trunc k (B x))) → type-trunc k (Σ A B)
  map-inv-trunc-Σ =
    map-universal-property-trunc
      ( trunc k (Σ A B))
      ( λ (a , |b|) →
        map-universal-property-trunc
          ( trunc k (Σ A B))
          ( λ b → unit-trunc (a , b))
          ( |b|))

  is-retraction-map-inv-trunc-Σ :
    ( map-inv-trunc-Σ ∘ map-trunc-Σ) ~ id
  is-retraction-map-inv-trunc-Σ =
    function-dependent-universal-property-trunc
      ( λ |ab| →
        Id-Truncated-Type'
          ( trunc k (Σ A B))
          ( map-inv-trunc-Σ (map-trunc-Σ |ab|))
          ( |ab|))
      ( λ (a , b) →
        ( ap
          ( map-inv-trunc-Σ)
          ( triangle-universal-property-trunc _
            ( λ (a' , b') → unit-trunc (a' , unit-trunc b'))
            ( a , b))) ∙
        ( triangle-universal-property-trunc _
          ( λ (a' , |b'|) →
            map-universal-property-trunc
              ( trunc k (Σ A B))
              ( λ b' → unit-trunc (a' , b'))
              ( |b'|))
          ( a , unit-trunc b) ∙
        triangle-universal-property-trunc _
          ( λ b' → unit-trunc (a , b'))
          ( b)))

  is-section-map-inv-trunc-Σ :
    ( map-trunc-Σ ∘ map-inv-trunc-Σ) ~ id
  is-section-map-inv-trunc-Σ =
    function-dependent-universal-property-trunc
      ( λ |a|b|| →
        Id-Truncated-Type'
          ( trunc k (Σ A (λ x → type-trunc k (B x))))
          ( map-trunc-Σ (map-inv-trunc-Σ |a|b||))
          ( |a|b||))
      ( λ (a , |b|) →
        function-dependent-universal-property-trunc
          (λ |b'| →
            Id-Truncated-Type'
              ( trunc k (Σ A (λ x → type-trunc k (B x))))
              (map-trunc-Σ (map-inv-trunc-Σ (unit-trunc (a , |b'|))))
              (unit-trunc (a , |b'|)))
          (λ b →
            ap map-trunc-Σ
              (triangle-universal-property-trunc _
                ( λ (a' , |b'|) →
                  map-universal-property-trunc
                    ( trunc k (Σ A B))
                    ( λ b' → unit-trunc (a' , b'))
                    ( |b'|))
                ( a , unit-trunc b)) ∙
            (ap map-trunc-Σ
              (triangle-universal-property-trunc
                ( trunc k (Σ A B))
                ( λ b' → unit-trunc (a , b'))
                ( b)) ∙
            triangle-universal-property-trunc _
              ( λ (a' , b') → unit-trunc (a' , unit-trunc b'))
              ( a , b)))
          ( |b|))

  equiv-trunc-Σ :
      type-trunc k (Σ A B) ≃ type-trunc k (Σ A (λ x → type-trunc k (B x)))
  pr1 equiv-trunc-Σ = map-trunc-Σ
  pr2 equiv-trunc-Σ =
    is-equiv-is-invertible
      map-inv-trunc-Σ
      is-section-map-inv-trunc-Σ
      is-retraction-map-inv-trunc-Σ

  inv-equiv-trunc-Σ :
    type-trunc k (Σ A (λ x → type-trunc k (B x))) ≃ type-trunc k (Σ A B)
  pr1 inv-equiv-trunc-Σ = map-inv-trunc-Σ
  pr2 inv-equiv-trunc-Σ =
    is-equiv-is-invertible
      map-trunc-Σ
      is-retraction-map-inv-trunc-Σ
      is-section-map-inv-trunc-Σ
```
