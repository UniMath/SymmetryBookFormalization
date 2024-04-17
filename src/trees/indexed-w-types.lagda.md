# Indexed W-types

```agda
module trees.indexed-w-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Idea

The concept of _indexed W-types_ is a generalization of ordinary
[W-types](trees.w-types.md) using a dependently typed variant of
[polynomial endofunctors](trees.polynomial-endofunctors.md). The main idea is
that indexed W-types are initial
[algebras](trees.algebras-polynomial-endofunctors.md) for the polynomial
endofunctor

```text
  (X : I → UU) ↦ (λ (j : I) → Σ (a : A j), Π (i : I), B i j a → X i),
```

where `B : (i j : I) → A j → 𝒰` is a type family. In other words, given the data

```text
  A : I → 𝒰
  B : (i j : I) → A j → 𝒰
```

of an indexed container we obtain for each `j : I` a multivariable polynomial

```text
  Σ (a : A j), Π (i : I), B i j a → X i
```

Since the functorial operation

```text
  (X : I → UU) ↦ (λ (j : I) → Σ (a : A j), Π (i : I), B i j a → X i),
```

takes an `I`-indexed family of inputs and returns an `I`-indexed family of
outputs, it is endofunctorial, meaning that it can be iterated and we can
consider initial algebras for this endofunctor.

We will formally define the {{#concept "indexed W-type" Agda=indexed-𝕎}}
associated to the data of an indexed container as the inductive type generated
by

```text
  tree-indexed-𝕎 :
    (x : A j) (α : (i : I) (y : B i j x) → indexed-𝕎 i) → indexed-𝕎 j.
```

**Note.** In the usual definition of indexed container, the type family `B` is
directly given as a type family over `A`

```text
  B : (i : I) → A i → 𝒰,
```

and furthermore there is a reindexing function

```text
  j : (i : I) (a : A i) → B i a → I.
```

The pair `(B , j)` of such a type family and a reindexing function is via
[type duality](foundation.type-duality.md) equivalent to a single type family

```text
  (j i : I) → A i → 𝒰.
```

## Definitions

### The indexed W-type associated to an indexed container

```agda
data
  indexed-𝕎
    {l1 l2 l3 : Level} (I : UU l1) (A : I → UU l2)
    (B : (i j : I) → A j → UU l3) (j : I) :
    UU (l1 ⊔ l2 ⊔ l3)
    where
  tree-indexed-𝕎 :
    (x : A j) (α : (i : I) (y : B i j x) → indexed-𝕎 I A B i) →
    indexed-𝕎 I A B j
```
