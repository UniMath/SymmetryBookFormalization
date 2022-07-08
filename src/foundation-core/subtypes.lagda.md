---
title: Subtypes
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.subtypes where

open import foundation-core.contractible-types using
  ( is-contr; is-contr-equiv; is-contr-total-path)
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.embeddings using (is-emb; _↪_)
open import foundation-core.equivalences using
  ( is-equiv; _≃_; map-inv-is-equiv; id-equiv; map-inv-equiv; map-equiv;
    isretr-map-inv-is-equiv)
open import foundation-core.fibers-of-maps using (equiv-fib-pr1)
open import foundation-core.functions using (_∘_)
open import foundation-core.functoriality-dependent-pair-types using
  ( tot; is-equiv-tot-is-fiberwise-equiv; equiv-Σ; map-Σ; is-equiv-map-Σ)
open import foundation-core.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation-core.identity-types using (_＝_; refl; ap; tr)
open import foundation-core.logical-equivalences using (_↔_; equiv-iff')
open import foundation-core.propositional-maps using
  ( is-emb-is-prop-map; is-prop-map-is-emb)
open import foundation-core.propositions using
  ( is-prop; UU-Prop; is-proof-irrelevant-is-prop; is-prop-equiv;
    is-prop-equiv'; type-Prop; is-prop-type-Prop; is-equiv-is-prop)
open import foundation-core.sets using (is-set; UU-Set; type-Set; is-set-type-Set)
open import foundation-core.subtype-identity-principle using
  ( is-contr-total-Eq-subtype; extensionality-subtype)
open import foundation-core.truncated-types using (is-trunc; is-trunc-is-emb)
open import foundation-core.truncation-levels using
  ( 𝕋; neg-two-𝕋; neg-one-𝕋; zero-𝕋; succ-𝕋)
open import foundation-core.type-arithmetic-dependent-pair-types using
  ( left-unit-law-Σ-is-contr; equiv-right-swap-Σ)
open import foundation-core.universe-levels using (Level; UU; _⊔_; lsuc)
```

## Idea

A subtype of a type `A` is a family of propositions over `A`. The underlying type of a subtype `P` of `A` is the total space `Σ A B`. 

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  is-subtype : UU (l1 ⊔ l2)
  is-subtype = (x : A) → is-prop (B x)

  is-property : UU (l1 ⊔ l2)
  is-property = is-subtype

subtype : {l1 : Level} (l : Level) (A : UU l1) → UU (l1 ⊔ lsuc l)
subtype l A = A → UU-Prop l

module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A)
  where

  is-in-subtype : A → UU l2
  is-in-subtype x = type-Prop (P x)

  is-prop-is-in-subtype : (x : A) → is-prop (is-in-subtype x)
  is-prop-is-in-subtype x = is-prop-type-Prop (P x)

  type-subtype : UU (l1 ⊔ l2)
  type-subtype = Σ A is-in-subtype

  inclusion-subtype : type-subtype → A
  inclusion-subtype = pr1

  ap-inclusion-subtype :
    (x y : type-subtype) →
    x ＝ y → (inclusion-subtype x ＝ inclusion-subtype y)
  ap-inclusion-subtype x y p = ap inclusion-subtype p

  is-in-subtype-inclusion-subtype :
    (x : type-subtype) → is-in-subtype (inclusion-subtype x)
  is-in-subtype-inclusion-subtype = pr2
```

## Properties

### Equality in subtypes

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A)
  where

  Eq-type-subtype : (x y : type-subtype P) → UU l1
  Eq-type-subtype x y = (pr1 x ＝ pr1 y)

  extensionality-type-subtype :
    (a b : type-subtype P) → (a ＝ b) ≃ (pr1 a ＝ pr1 b)
  extensionality-type-subtype (pair a p) =
    extensionality-subtype P p refl (λ x → id-equiv)

  eq-subtype :
    {a b : type-subtype P} → (pr1 a ＝ pr1 b) → a ＝ b
  eq-subtype {a} {b} = map-inv-equiv (extensionality-type-subtype a b)
```

### If `B` is a subtype of `A`, then the projection map `Σ A B → A` is an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : subtype l2 A)
  where

  abstract
    is-emb-inclusion-subtype : is-emb (inclusion-subtype B)
    is-emb-inclusion-subtype =
      is-emb-is-prop-map
        ( λ x →
          is-prop-equiv
            ( equiv-fib-pr1 (is-in-subtype B) x)
            ( is-prop-is-in-subtype B x))

  emb-subtype : type-subtype B ↪ A
  pr1 emb-subtype = inclusion-subtype B
  pr2 emb-subtype = is-emb-inclusion-subtype

  equiv-ap-inclusion-subtype :
    {s t : type-subtype B} →
    (s ＝ t) ≃ (inclusion-subtype B s ＝ inclusion-subtype B t)
  pr1 (equiv-ap-inclusion-subtype {s} {t}) = ap-inclusion-subtype B s t
  pr2 (equiv-ap-inclusion-subtype {s} {t}) = is-emb-inclusion-subtype s t
```

### If the projection map of a type family is an embedding, then the type family is a subtype

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where
  
  abstract
    is-subtype-is-emb-pr1 : is-emb (pr1 {B = B}) → is-subtype B
    is-subtype-is-emb-pr1 H x =
      is-prop-equiv' (equiv-fib-pr1 B x) (is-prop-map-is-emb H x)
```

### A subtype of a (k+1)-truncated type is (k+1)-truncated.

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} (P : subtype l2 A)
  where
  
  abstract
    is-trunc-type-subtype :
      is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) (type-subtype P)
    is-trunc-type-subtype =
      is-trunc-is-emb k
        ( inclusion-subtype P)
        ( is-emb-inclusion-subtype P)

module _
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A)
  where
  
  abstract
    is-prop-type-subtype : is-prop A → is-prop (type-subtype P)
    is-prop-type-subtype = is-trunc-type-subtype neg-two-𝕋 P

  abstract
    is-set-type-subtype : is-set A → is-set (type-subtype P)
    is-set-type-subtype = is-trunc-type-subtype neg-one-𝕋 P

subprop-Prop :
  {l1 l2 : Level} (A : UU-Prop l1) (P : subtype l2 (type-Prop A)) →
  UU-Prop (l1 ⊔ l2)
pr1 (subprop-Prop A P) = type-subtype P
pr2 (subprop-Prop A P) =
  is-prop-type-subtype P (is-prop-type-Prop A)

subset-Set :
  {l1 l2 : Level} (A : UU-Set l1) (P : subtype l2 (type-Set A)) →
  UU-Set (l1 ⊔ l2)
pr1 (subset-Set A P) = type-subtype P
pr2 (subset-Set A P) =
  is-set-type-subtype P (is-set-type-Set A)
```

### Logically equivalent subtypes induce equivalences on the underlying type of a subtype

```agda
equiv-type-subtype :
  { l1 l2 l3 : Level} {A : UU l1} {P : A → UU l2} {Q : A → UU l3} →
  ( is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q) →
  ( f : (x : A) → P x → Q x) →
  ( g : (x : A) → Q x → P x) →
  ( Σ A P) ≃ (Σ A Q)
pr1 (equiv-type-subtype is-subtype-P is-subtype-Q f g) = tot f
pr2 (equiv-type-subtype is-subtype-P is-subtype-Q f g) =
  is-equiv-tot-is-fiberwise-equiv {f = f}
    ( λ x → is-equiv-is-prop (is-subtype-P x) (is-subtype-Q x) (g x))
```

### Equivalences of subtypes

```agda
equiv-subtype-equiv :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} (e : A ≃ B)
  (C : A → UU-Prop l3) (D : B → UU-Prop l4) →
  ((x : A) → type-Prop (C x) ↔ type-Prop (D (map-equiv e x))) →
  type-subtype C ≃ type-subtype D
equiv-subtype-equiv e C D H =
  equiv-Σ (λ y → type-Prop (D y)) e
    ( λ x → equiv-iff' (C x) (D (map-equiv e x)) (H x))
```

```agda
abstract
  is-equiv-subtype-is-equiv :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
    {P : A → UU l3} {Q : B → UU l4}
    (is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q)
    (f : A → B) (g : (x : A) → P x → Q (f x)) →
    is-equiv f → ((x : A) → (Q (f x)) → P x) → is-equiv (map-Σ Q f g)
  is-equiv-subtype-is-equiv {Q = Q} is-subtype-P is-subtype-Q f g is-equiv-f h =
    is-equiv-map-Σ Q f g is-equiv-f
      ( λ x → is-equiv-is-prop (is-subtype-P x) (is-subtype-Q (f x)) (h x))

abstract
  is-equiv-subtype-is-equiv' :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
    {P : A → UU l3} {Q : B → UU l4}
    (is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q)
    (f : A → B) (g : (x : A) → P x → Q (f x)) →
    (is-equiv-f : is-equiv f) →
    ((y : B) → (Q y) → P (map-inv-is-equiv is-equiv-f y)) →
    is-equiv (map-Σ Q f g)
  is-equiv-subtype-is-equiv' {P = P} {Q}
    is-subtype-P is-subtype-Q f g is-equiv-f h =
    is-equiv-map-Σ Q f g is-equiv-f
      ( λ x → is-equiv-is-prop (is-subtype-P x) (is-subtype-Q (f x))
        ( (tr P (isretr-map-inv-is-equiv is-equiv-f x)) ∘ (h (f x))))
```
