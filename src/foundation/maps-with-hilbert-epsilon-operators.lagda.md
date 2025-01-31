# Maps with Hilbert ε-operators

```agda
module foundation.maps-with-hilbert-epsilon-operators where
```

<details><summary>Imports</summary>

```agda
open import foundation.hilberts-epsilon-operators
open import foundation.universe-levels

open import foundation-core.fibers-of-maps
```

</details>

## Idea

We consider maps `f : A → B` [equippes](foundation.structure.md) with
[Hilbert ε-operators](foundation.hilberts-epsilon-operators.md) on its
[fibers](foundation-core.fibers-of-maps.md). I.e., for every `y : B` there is an
operator

```text
  ε_y : ║ fiber f y ║₋₁ → fiber f y
```

## Definitions

### The structure of an Hilbert ε-operator on a map

```agda
ε-operator-map-Hilbert :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
ε-operator-map-Hilbert {B = B} f = (y : B) → ε-operator-Hilbert (fiber f y)
```
