# Injective maps

```agda
module foundation-core.injective-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

A map `f : A → B` is **injective** if `f x ＝ f y` implies `x ＝ y`.

## Warning

The notion of injective map is, however, not homotopically coherent. It is fine
to use injectivity for maps between [sets](foundation-core.sets.md), but for
maps between general types it is recommended to use the notion of
[embedding](foundation-core.embeddings.md).

## Definition

```agda
is-injective : {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-injective {l1} {l2} {A} {B} f = {x y : A} → f x ＝ f y → x ＝ y

injection : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
injection A B = Σ (A → B) is-injective
```

## Examples

### The identity function is injective

```agda
is-injective-id : {l1 : Level} {A : UU l1} → is-injective (id {A = A})
is-injective-id p = p

id-injection : {l1 : Level} {A : UU l1} → injection A A
pr1 id-injection = id
pr2 id-injection = is-injective-id
```

## Properties

### If a composite is injective, then so is its right factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-injective-right-factor :
    (g : B → C) (h : A → B) →
    is-injective (g ∘ h) → is-injective h
  is-injective-right-factor g h is-inj-gh p = is-inj-gh (ap g p)

  is-injective-top-map-triangle :
    (f : A → C) (g : B → C) (h : A → B) (H : f ~ (g ∘ h)) →
    is-injective f → is-injective h
  is-injective-top-map-triangle f g h H is-inj-f {x} {x'} p =
    is-inj-f {x} {x'} ((H x) ∙ ((ap g p) ∙ (inv (H x'))))
```

### Injective maps are closed under composition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-injective-comp :
    {g : B → C} {h : A → B} →
    is-injective h → is-injective g → is-injective (g ∘ h)
  is-injective-comp is-inj-h is-inj-g = is-inj-h ∘ is-inj-g

  is-injective-left-map-triangle :
    (f : A → C) (g : B → C) (h : A → B) → f ~ (g ∘ h) →
    is-injective h → is-injective g → is-injective f
  is-injective-left-map-triangle f g h H is-inj-h is-inj-g {x} {x'} p =
    is-inj-h (is-inj-g ((inv (H x)) ∙ (p ∙ (H x'))))
```

### Equivalences are injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-injective-is-equiv : {f : A → B} → is-equiv f → is-injective f
  is-injective-is-equiv {f} H =
    is-injective-retraction f (retraction-is-equiv H)

  is-injective-equiv : (e : A ≃ B) → is-injective (map-equiv e)
  is-injective-equiv e = is-injective-is-equiv (is-equiv-map-equiv e)

abstract
  is-injective-map-inv-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    is-injective (map-inv-equiv e)
  is-injective-map-inv-equiv e =
    is-injective-is-equiv (is-equiv-map-inv-equiv e)
```

### Injective maps that have a section are equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-equiv-is-injective : {f : A → B} → section f → is-injective f → is-equiv f
  is-equiv-is-injective {f} (g , G) H =
    is-equiv-is-invertible g G (λ x → H (G (f x)))
```

### Any embedding is injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-injective-is-emb : {f : A → B} → is-emb f → is-injective f
  is-injective-is-emb is-emb-f {x} {y} = map-inv-is-equiv (is-emb-f x y)

  is-injective-emb : (e : A ↪ B) → is-injective (map-emb e)
  is-injective-emb e {x} {y} = map-inv-is-equiv (is-emb-map-emb e x y)
```

### Any map out of a contractible type is injective

```agda
is-injective-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-contr A → is-injective f
is-injective-is-contr f H p = eq-is-contr H
```

## See also

- [Embeddings](foundation-core.embeddings.md)
- [Path-cosplit maps](foundation.path-cosplit-maps.md)
