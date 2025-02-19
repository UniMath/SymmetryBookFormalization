# Bezout's lemma on the natural numbers

```agda
module elementary-number-theory.bezouts-lemma-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.congruence-integers
open import elementary-number-theory.distance-integers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.divisibility-modular-arithmetic
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.euclidean-division-natural-numbers
open import elementary-number-theory.greatest-common-divisor-natural-numbers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.lower-bounds-natural-numbers
open import elementary-number-theory.minimal-structured-natural-numbers
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.well-ordering-principle-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.negation
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Bezout's lemma shows that for any two natural numbers `x` and `y` there exist
`k` and `l` such that `dist-ℕ (kx,ly) = gcd(x,y)`. To prove this, note that the
predicate `P : ℕ → UU lzero` given by

```text
  P z := Σ (k : ℕ), Σ (l : ℕ), dist-ℕ (kx, ly) = z
```

is decidable, because `P z ⇔ [y]_x | [z]_x` in `ℤ/x`. The least positive `z`
such that `P z` holds is `gcd x y`.

Bézout's Lemma is the [60th](literature.100-theorems.md#60) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}. It was
originally added to agda-unimath by [Bryan Lu](https://blu-bird.github.io).

## Definitions

```agda
is-distance-between-multiples-ℕ : ℕ → ℕ → ℕ → UU lzero
is-distance-between-multiples-ℕ x y z =
  Σ ℕ (λ k → Σ ℕ (λ l → dist-ℕ (k *ℕ x) (l *ℕ y) ＝ z))

is-distance-between-multiples-fst-coeff-ℕ :
  {x y z : ℕ} → is-distance-between-multiples-ℕ x y z → ℕ
is-distance-between-multiples-fst-coeff-ℕ dist = pr1 dist

is-distance-between-multiples-snd-coeff-ℕ :
  {x y z : ℕ} → is-distance-between-multiples-ℕ x y z → ℕ
is-distance-between-multiples-snd-coeff-ℕ dist = pr1 (pr2 dist)

is-distance-between-multiples-eqn-ℕ :
  {x y z : ℕ} (d : is-distance-between-multiples-ℕ x y z) →
  dist-ℕ
    ( (is-distance-between-multiples-fst-coeff-ℕ d) *ℕ x)
    ( (is-distance-between-multiples-snd-coeff-ℕ d) *ℕ y) ＝ z
is-distance-between-multiples-eqn-ℕ dist = pr2 (pr2 dist)

is-distance-between-multiples-sym-ℕ :
  (x y z : ℕ) → is-distance-between-multiples-ℕ x y z →
  is-distance-between-multiples-ℕ y x z
is-distance-between-multiples-sym-ℕ x y z (pair k (pair l eqn)) =
  pair l (pair k (symmetric-dist-ℕ (l *ℕ y) (k *ℕ x) ∙ eqn))
```

## Lemmas

### If `z = dist-ℕ (kx, ly)` for some `k` and `l`, then `[y] | [z]` in `ℤ-Mod x`

If `z = dist-ℕ (kx, ly)` for some `k` and `l`, then it follows that
`ly ≡ ±z mod x`. It follows that `±ly ≡ z mod x`, and therefore that `[y] | [z]`
in `ℤ-Mod x`

```agda
int-is-distance-between-multiples-ℕ :
  (x y z : ℕ) (d : is-distance-between-multiples-ℕ x y z) →
  ( H :
    leq-ℕ
      ( (is-distance-between-multiples-fst-coeff-ℕ d) *ℕ x)
      ( (is-distance-between-multiples-snd-coeff-ℕ d) *ℕ y)) →
  ( int-ℕ z) +ℤ
  ( (int-ℕ (is-distance-between-multiples-fst-coeff-ℕ d)) *ℤ (int-ℕ x)) ＝
  ( int-ℕ (is-distance-between-multiples-snd-coeff-ℕ d)) *ℤ (int-ℕ y)
int-is-distance-between-multiples-ℕ x y z (k , l , p) H =
  equational-reasoning
    (int-ℕ z) +ℤ ((int-ℕ k) *ℤ (int-ℕ x))
    ＝ (int-ℕ z) +ℤ (int-ℕ (k *ℕ x))
      by ap ((int-ℕ z) +ℤ_) (mul-int-ℕ k x)
    ＝ int-ℕ (z +ℕ (k *ℕ x))
      by add-int-ℕ z (k *ℕ x)
    ＝ int-ℕ (l *ℕ y)
      by ap (int-ℕ) (rewrite-left-dist-add-ℕ z (k *ℕ x) (l *ℕ y) H (inv p))
    ＝ (int-ℕ l) *ℤ (int-ℕ y)
      by inv (mul-int-ℕ l y)

div-mod-is-distance-between-multiples-ℕ :
  (x y z : ℕ) →
  is-distance-between-multiples-ℕ x y z → div-ℤ-Mod x (mod-ℕ x y) (mod-ℕ x z)
div-mod-is-distance-between-multiples-ℕ x y z (k , l , p) =
  kxly-case-split (linear-leq-ℕ (k *ℕ x) (l *ℕ y))
  where
  kxly-case-split :
    leq-ℕ (k *ℕ x) (l *ℕ y) + leq-ℕ (l *ℕ y) (k *ℕ x) →
    div-ℤ-Mod x (mod-ℕ x y) (mod-ℕ x z)
  kxly-case-split (inl kxly) =
    ( mod-ℕ x l ,
      ( equational-reasoning
        mul-ℤ-Mod x (mod-ℕ x l) (mod-ℕ x y)
        ＝ mul-ℤ-Mod x (mod-ℤ x (int-ℕ l)) (mod-ℕ x y)
          by inv (ap (λ p → mul-ℤ-Mod x p (mod-ℕ x y)) (mod-int-ℕ x l))
        ＝ mul-ℤ-Mod x (mod-ℤ x (int-ℕ l)) (mod-ℤ x (int-ℕ y))
          by inv (ap (λ p → mul-ℤ-Mod x (mod-ℤ x (int-ℕ l)) p) (mod-int-ℕ x y))
        ＝ mod-ℤ x ((int-ℕ l) *ℤ (int-ℕ y))
          by inv (preserves-mul-mod-ℤ x (int-ℕ l) (int-ℕ y))
        ＝ mod-ℤ x ((int-ℕ z) +ℤ ((int-ℕ k) *ℤ (int-ℕ x)))
          by
          inv
            ( ap
              ( mod-ℤ x)
              ( int-is-distance-between-multiples-ℕ x y z (k , l , p) kxly))
        ＝ add-ℤ-Mod x (mod-ℤ x (int-ℕ z)) (mod-ℤ x ((int-ℕ k) *ℤ (int-ℕ x)))
          by preserves-add-mod-ℤ x (int-ℕ z) ((int-ℕ k) *ℤ (int-ℕ x))
        ＝ add-ℤ-Mod x
            ( mod-ℤ x (int-ℕ z))
            ( mul-ℤ-Mod x (mod-ℤ x (int-ℕ k)) (mod-ℤ x (int-ℕ x)))
          by
          ap
            ( add-ℤ-Mod x (mod-ℤ x (int-ℕ z)))
            ( preserves-mul-mod-ℤ x (int-ℕ k) (int-ℕ x))
        ＝ add-ℤ-Mod x
            ( mod-ℤ x (int-ℕ z))
            ( mul-ℤ-Mod x (mod-ℤ x (int-ℕ k)) (mod-ℤ x zero-ℤ))
          by
          ap
            ( λ p →
              add-ℤ-Mod x
                ( mod-ℤ x (int-ℕ z))
                ( mul-ℤ-Mod x (mod-ℤ x (int-ℕ k)) p))
            ( mod-int-ℕ x x ∙ (mod-refl-ℕ x ∙ inv (mod-zero-ℤ x)))
        ＝ add-ℤ-Mod x
            ( mod-ℤ x (int-ℕ z))
            ( mod-ℤ x ((int-ℕ k) *ℤ zero-ℤ))
          by
          ap
            ( add-ℤ-Mod x (mod-ℤ x (int-ℕ z)))
            ( inv (preserves-mul-mod-ℤ x (int-ℕ k) zero-ℤ))
        ＝ add-ℤ-Mod x (mod-ℤ x (int-ℕ z)) (mod-ℤ x zero-ℤ)
          by
          ap
            ( λ p → add-ℤ-Mod x (mod-ℤ x (int-ℕ z)) (mod-ℤ x p))
            ( right-zero-law-mul-ℤ (int-ℕ k))
        ＝ mod-ℤ x ((int-ℕ z) +ℤ zero-ℤ)
          by inv (preserves-add-mod-ℤ x (int-ℕ z) zero-ℤ)
        ＝ mod-ℤ x (int-ℕ z)
          by ap (mod-ℤ x) (right-unit-law-add-ℤ (int-ℕ z))
        ＝ mod-ℕ x z by mod-int-ℕ x z))
  kxly-case-split (inr lykx) =
    ( mod-ℤ x (neg-ℤ (int-ℕ l)) ,
      ( equational-reasoning
        mul-ℤ-Mod x (mod-ℤ x (neg-ℤ (int-ℕ l))) (mod-ℕ x y)
        ＝ mul-ℤ-Mod x (mod-ℤ x (neg-ℤ (int-ℕ l))) (mod-ℤ x (int-ℕ y))
          by
          inv
            ( ap
              ( mul-ℤ-Mod x (mod-ℤ x (neg-ℤ (int-ℕ l))))
              ( mod-int-ℕ x y))
        ＝ mod-ℤ x ((neg-ℤ (int-ℕ l)) *ℤ (int-ℕ y))
          by inv (preserves-mul-mod-ℤ x (neg-ℤ (int-ℕ l)) (int-ℕ y))
        ＝ mod-ℤ x (((neg-ℤ (int-ℕ l)) *ℤ (int-ℕ y)) +ℤ zero-ℤ)
          by
          ap
            ( mod-ℤ x)
            ( inv (right-unit-law-add-ℤ ((neg-ℤ (int-ℕ l)) *ℤ (int-ℕ y))))
        ＝ add-ℤ-Mod x
            ( mod-ℤ x ((neg-ℤ (int-ℕ l)) *ℤ (int-ℕ y)))
            ( mod-ℤ x zero-ℤ)
          by preserves-add-mod-ℤ x ((neg-ℤ (int-ℕ l)) *ℤ (int-ℕ y)) (zero-ℤ)
        ＝ add-ℤ-Mod x
            ( mod-ℤ x ((neg-ℤ (int-ℕ l)) *ℤ (int-ℕ y)))
            ( mod-ℤ x ((int-ℕ k) *ℤ zero-ℤ))
          by
          ap
            ( λ p →
              add-ℤ-Mod x
                ( mod-ℤ x ((neg-ℤ (int-ℕ l)) *ℤ (int-ℕ y)))
                ( mod-ℤ x p))
            ( inv (right-zero-law-mul-ℤ (int-ℕ k)))
        ＝ add-ℤ-Mod x
            ( mod-ℤ x ((neg-ℤ (int-ℕ l)) *ℤ (int-ℕ y)))
            ( mul-ℤ-Mod x (mod-ℤ x (int-ℕ k)) (mod-ℤ x zero-ℤ))
          by
          ap
            ( add-ℤ-Mod x (mod-ℤ x ((neg-ℤ (int-ℕ l)) *ℤ (int-ℕ y))))
            ( preserves-mul-mod-ℤ x (int-ℕ k) zero-ℤ)
        ＝ add-ℤ-Mod x
            ( mod-ℤ x ((neg-ℤ (int-ℕ l)) *ℤ (int-ℕ y)))
            ( mul-ℤ-Mod x (mod-ℤ x (int-ℕ k)) (mod-ℤ x (int-ℕ x)))
          by
          ap
            ( λ p →
              add-ℤ-Mod x
                ( mod-ℤ x ((neg-ℤ (int-ℕ l)) *ℤ (int-ℕ y)))
                ( mul-ℤ-Mod x (mod-ℤ x (int-ℕ k)) p))
            ( mod-zero-ℤ x ∙ (inv (mod-refl-ℕ x) ∙ inv (mod-int-ℕ x x)))
        ＝ add-ℤ-Mod x
            ( mod-ℤ x ((neg-ℤ (int-ℕ l)) *ℤ (int-ℕ y)))
            ( mod-ℤ x ((int-ℕ k) *ℤ (int-ℕ x)))
          by
          ap
            ( add-ℤ-Mod x (mod-ℤ x ((neg-ℤ (int-ℕ l)) *ℤ (int-ℕ y))))
            ( inv (preserves-mul-mod-ℤ x (int-ℕ k) (int-ℕ x)))
        ＝ mod-ℤ x
            ( ((neg-ℤ (int-ℕ l)) *ℤ (int-ℕ y)) +ℤ ((int-ℕ k) *ℤ (int-ℕ x)))
          by
          inv
            ( preserves-add-mod-ℤ x
              ( (neg-ℤ (int-ℕ l)) *ℤ (int-ℕ y))
              ( (int-ℕ k) *ℤ (int-ℕ x)))
        ＝ mod-ℤ x (int-ℕ z)
          by
          ap
            ( mod-ℤ x)
            ( equational-reasoning
              ((neg-ℤ (int-ℕ l)) *ℤ (int-ℕ y)) +ℤ ((int-ℕ k) *ℤ (int-ℕ x))
              ＝ (neg-ℤ ((int-ℕ l) *ℤ (int-ℕ y))) +ℤ ((int-ℕ k) *ℤ (int-ℕ x))
                by
                ap
                  ( _+ℤ ((int-ℕ k) *ℤ (int-ℕ x)))
                  ( left-negative-law-mul-ℤ (int-ℕ l) (int-ℕ y))
              ＝ ((int-ℕ k) *ℤ (int-ℕ x)) +ℤ (neg-ℤ ((int-ℕ l) *ℤ (int-ℕ y)))
                by
                commutative-add-ℤ
                  ( neg-ℤ ((int-ℕ l) *ℤ (int-ℕ y)))
                  ( (int-ℕ k) *ℤ (int-ℕ x))
              ＝ add-ℤ
                  ( (int-ℕ z) +ℤ ((int-ℕ l) *ℤ (int-ℕ y)))
                  ( neg-ℤ ((int-ℕ l) *ℤ (int-ℕ y)))
                by
                ap
                  ( _+ℤ (neg-ℤ ((int-ℕ l) *ℤ (int-ℕ y))))
                  ( inv
                    ( int-is-distance-between-multiples-ℕ y x z
                      ( is-distance-between-multiples-sym-ℕ x y z (k , l , p))
                    ( lykx)))
              ＝ int-ℕ z
                by
                is-retraction-right-add-neg-ℤ
                  ( (int-ℕ l) *ℤ (int-ℕ y))
                  ( int-ℕ z))
              ＝ mod-ℕ x z by mod-int-ℕ x z))
```

### If `[y] | [z]` in `ℤ-Mod x`, then `z = dist-ℕ (kx, ly)` for some `k` and `l`

If `x = 0`, then we can simply argue in `ℤ`. Otherwise, if `[y] | [z]` in
`ℤ-Mod x`, there exists some equivalence class `u` in `ℤ-Mod x` such that
`[u] [y] ≡ [z]` as a congruence mod `x`. This `u` can always be chosen such that
`x > u ≥ 0`. Therefore, there exists some integer `a ≥ 0` such that
`ax = uy - z`, or `ax = z - uy`. In the first case, we can extract the distance
condition we desire. In the other case, we have that `ax + uy = z`. This can be
written as `(a + y)x + (u - x)y = z`, so that the second term is nonpositive.
Then, in this case, we again can extract the distance condition we desire.

```agda
cong-div-mod-ℤ :
  (x y z : ℕ) (q : div-ℤ-Mod x (mod-ℕ x y) (mod-ℕ x z)) →
  cong-ℤ (int-ℕ x) ((int-ℤ-Mod x (pr1 q)) *ℤ (int-ℕ y)) (int-ℕ z)
cong-div-mod-ℤ x y z (u , p) =
  cong-eq-mod-ℤ x
    ( (int-ℤ-Mod x u) *ℤ (int-ℕ y))
    ( int-ℕ z)
    ( equational-reasoning
      mod-ℤ x ((int-ℤ-Mod x u) *ℤ (int-ℕ y))
      ＝ mul-ℤ-Mod x (mod-ℤ x (int-ℤ-Mod x u)) (mod-ℤ x (int-ℕ y))
        by preserves-mul-mod-ℤ x (int-ℤ-Mod x u) (int-ℕ y)
      ＝ mul-ℤ-Mod x u (mod-ℤ x (int-ℕ y))
        by
        ap
          ( λ p → mul-ℤ-Mod x p (mod-ℤ x (int-ℕ y)))
          ( is-section-int-ℤ-Mod x u)
      ＝ mul-ℤ-Mod x u (mod-ℕ x y)
        by ap (mul-ℤ-Mod x u) (mod-int-ℕ x y)
      ＝ mod-ℕ x z by p
      ＝ mod-ℤ x (int-ℕ z) by inv (mod-int-ℕ x z))

is-distance-between-multiples-div-mod-ℕ :
  (x y z : ℕ) →
  div-ℤ-Mod x (mod-ℕ x y) (mod-ℕ x z) → is-distance-between-multiples-ℕ x y z
is-distance-between-multiples-div-mod-ℕ zero-ℕ y z (u , p) =
  u-nonneg-case-split (decide-is-nonnegative-is-nonnegative-neg-ℤ {u})
  where
  u-nonneg-case-split :
    (is-nonnegative-ℤ u + is-nonnegative-ℤ (neg-ℤ u)) →
    is-distance-between-multiples-ℕ zero-ℕ y z
  u-nonneg-case-split (inl nonneg) =
    ( zero-ℕ ,
      abs-ℤ u ,
      is-injective-int-ℕ
        ( inv (mul-int-ℕ (abs-ℤ u) y) ∙
          ( ( ap
              ( _*ℤ (int-ℕ y))
              ( int-abs-is-nonnegative-ℤ u nonneg)) ∙
            ( p))))
  u-nonneg-case-split (inr neg) =
    ( zero-ℕ ,
      zero-ℕ ,
      is-injective-int-ℕ
        ( inv
          ( is-zero-is-nonnegative-neg-is-nonnegative-ℤ
            ( is-nonnegative-int-ℕ z)
            ( tr
              ( is-nonnegative-ℤ)
              ( left-negative-law-mul-ℤ u (int-ℕ y) ∙ ap (neg-ℤ) p)
              ( is-nonnegative-mul-ℤ neg (is-nonnegative-int-ℕ y))))))

is-distance-between-multiples-div-mod-ℕ (succ-ℕ x) y z (u , p) =
  uy-z-case-split (decide-is-nonnegative-is-nonnegative-neg-ℤ
    { ((int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y)) +ℤ (neg-ℤ (int-ℕ z))})
  where
  a : ℤ
  a = pr1 (cong-div-mod-ℤ (succ-ℕ x) y z (u , p))

  a-eqn-pos :
    add-ℤ
      ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))
      ( neg-ℤ (a *ℤ (int-ℕ (succ-ℕ x)))) ＝
    int-ℕ z
  a-eqn-pos =
    equational-reasoning
    add-ℤ
      ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))
      ( neg-ℤ (a *ℤ (int-ℕ (succ-ℕ x))))
    ＝ add-ℤ
        ( neg-ℤ (a *ℤ (int-ℕ (succ-ℕ x))))
        ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))
      by
      commutative-add-ℤ
        ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))
        ( neg-ℤ (a *ℤ (int-ℕ (succ-ℕ x))))
    ＝ add-ℤ
        ( (neg-ℤ a) *ℤ (int-ℕ (succ-ℕ x)))
        ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))
      by
      ap
        ( _+ℤ ((int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y)))
        ( inv (left-negative-law-mul-ℤ a (int-ℕ (succ-ℕ x))))
    ＝ add-ℤ
        ( (neg-ℤ a) *ℤ (int-ℕ (succ-ℕ x)))
        ( add-ℤ
          ( ((int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y)) +ℤ (neg-ℤ (int-ℕ z)))
          ( int-ℕ z))
      by
      ap
        ( ((neg-ℤ a) *ℤ (int-ℕ (succ-ℕ x))) +ℤ_)
        ( inv
          ( is-section-right-add-neg-ℤ
            ( int-ℕ z)
            ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))))
    ＝ add-ℤ
        ( add-ℤ
          ( (neg-ℤ a) *ℤ (int-ℕ (succ-ℕ x)))
          ( ((int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y)) +ℤ (neg-ℤ (int-ℕ z))))
        ( int-ℕ z)
      by
      inv
        ( associative-add-ℤ
          ( (neg-ℤ a) *ℤ (int-ℕ (succ-ℕ x)))
          ( ((int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y)) +ℤ (neg-ℤ (int-ℕ z)))
          ( int-ℕ z))
    ＝ add-ℤ
        ( add-ℤ
          ( (neg-ℤ a) *ℤ (int-ℕ (succ-ℕ x)))
          ( a *ℤ (int-ℕ (succ-ℕ x))))
        ( int-ℕ z)
      by
      ap
        ( λ p → (((neg-ℤ a) *ℤ (int-ℕ (succ-ℕ x))) +ℤ p) +ℤ (int-ℕ z))
        ( inv (pr2 (cong-div-mod-ℤ (succ-ℕ x) y z (u , p))))
    ＝ add-ℤ
        ( add-ℤ
          ( neg-ℤ (a *ℤ (int-ℕ (succ-ℕ x))))
          ( a *ℤ (int-ℕ (succ-ℕ x))))
        ( int-ℕ z)
      by
      ap
        ( λ p → (p +ℤ (a *ℤ (int-ℕ (succ-ℕ x)))) +ℤ (int-ℕ z))
        ( left-negative-law-mul-ℤ a (int-ℕ (succ-ℕ x)))
    ＝ zero-ℤ +ℤ (int-ℕ z)
      by
      ap
        ( _+ℤ (int-ℕ z))
        ( left-inverse-law-add-ℤ (a *ℤ (int-ℕ (succ-ℕ x))))
    ＝ int-ℕ z by left-unit-law-add-ℤ (int-ℕ z)

  a-extra-eqn-neg :
    add-ℤ
      ( ((neg-ℤ a) +ℤ (int-ℕ y)) *ℤ (int-ℕ (succ-ℕ x)))
      ( neg-ℤ
        ( mul-ℤ
          ( (int-ℕ (succ-ℕ x)) +ℤ (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))
          ( int-ℕ y))) ＝
    ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ int-ℕ y) +ℤ (neg-ℤ (a *ℤ int-ℕ (succ-ℕ x)))
  a-extra-eqn-neg =
    equational-reasoning
    add-ℤ
      ( ((neg-ℤ a) +ℤ (int-ℕ y)) *ℤ (int-ℕ (succ-ℕ x)))
      ( neg-ℤ
        ( mul-ℤ
          ( (int-ℕ (succ-ℕ x)) +ℤ (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))
          ( int-ℕ y)))
    ＝ add-ℤ
        ( ((neg-ℤ a) +ℤ (int-ℕ y)) *ℤ (int-ℕ (succ-ℕ x)))
        ( mul-ℤ
          ( neg-ℤ ((int-ℕ (succ-ℕ x)) +ℤ (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u))))
          ( int-ℕ y))
      by
      ap
        ( (((neg-ℤ a) +ℤ (int-ℕ y)) *ℤ (int-ℕ (succ-ℕ x))) +ℤ_)
        ( inv
          ( left-negative-law-mul-ℤ
            ( (int-ℕ (succ-ℕ x)) +ℤ (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))
            ( int-ℕ y)))
    ＝ add-ℤ
        ( ((neg-ℤ a) +ℤ (int-ℕ y)) *ℤ (int-ℕ (succ-ℕ x)))
        ( ((int-ℤ-Mod (succ-ℕ x) u) +ℤ (neg-ℤ (int-ℕ (succ-ℕ x)))) *ℤ (int-ℕ y))
      by
      ap
        ( λ p →
          add-ℤ
            ( ((neg-ℤ a) +ℤ (int-ℕ y)) *ℤ (int-ℕ (succ-ℕ x)))
            ( p *ℤ (int-ℕ y)))
        ( equational-reasoning
          neg-ℤ ((int-ℕ (succ-ℕ x)) +ℤ (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))
          ＝ neg-ℤ ((neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)) +ℤ (int-ℕ (succ-ℕ x)))
            by
            ap
              ( neg-ℤ)
              ( commutative-add-ℤ
                ( int-ℕ (succ-ℕ x))
                ( neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))
          ＝ add-ℤ
              ( neg-ℤ (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))
              ( neg-ℤ (int-ℕ (succ-ℕ x)))
            by
            distributive-neg-add-ℤ
              ( neg-ℤ (int-ℤ-Mod (succ-ℕ x) u))
              ( int-ℕ (succ-ℕ x))
          ＝ (int-ℤ-Mod (succ-ℕ x) u) +ℤ (neg-ℤ (int-ℕ (succ-ℕ x)))
            by
            ap
              ( _+ℤ (neg-ℤ (int-ℕ (succ-ℕ x))))
              ( neg-neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))
    ＝ add-ℤ
        ( ((neg-ℤ a) +ℤ (int-ℕ y)) *ℤ (int-ℕ (succ-ℕ x)))
        ( add-ℤ
          ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))
          ( (neg-ℤ (int-ℕ (succ-ℕ x))) *ℤ (int-ℕ y)))
      by
      ap
        ( (((neg-ℤ a) +ℤ (int-ℕ y)) *ℤ (int-ℕ (succ-ℕ x))) +ℤ_)
        ( right-distributive-mul-add-ℤ
          ( int-ℤ-Mod (succ-ℕ x) u)
          ( neg-ℤ (int-ℕ (succ-ℕ x)))
          ( int-ℕ y))
    ＝ add-ℤ
        ( ((neg-ℤ a) +ℤ (int-ℕ y)) *ℤ (int-ℕ (succ-ℕ x)))
        ( add-ℤ
          ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))
          ( neg-ℤ ((int-ℕ (succ-ℕ x)) *ℤ (int-ℕ y))))
      by
      ap
        ( λ p →
          add-ℤ
            ( ((neg-ℤ a) +ℤ (int-ℕ y)) *ℤ (int-ℕ (succ-ℕ x)))
            ( ((int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y)) +ℤ p))
        ( left-negative-law-mul-ℤ (int-ℕ (succ-ℕ x)) (int-ℕ y))
    ＝ add-ℤ
        ( add-ℤ
          ( (neg-ℤ a) *ℤ (int-ℕ (succ-ℕ x)))
          ( (int-ℕ y) *ℤ (int-ℕ (succ-ℕ x))))
        ( add-ℤ
          ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))
          ( neg-ℤ ((int-ℕ (succ-ℕ x)) *ℤ (int-ℕ y))))
      by
      ap
        ( _+ℤ
          ( add-ℤ
            ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))
            ( neg-ℤ ((int-ℕ (succ-ℕ x)) *ℤ (int-ℕ y)))))
        ( right-distributive-mul-add-ℤ (neg-ℤ a) (int-ℕ y) (int-ℕ (succ-ℕ x)))
    ＝ add-ℤ
        ( add-ℤ
          ( (neg-ℤ a) *ℤ (int-ℕ (succ-ℕ x)))
          ( (int-ℕ (succ-ℕ x)) *ℤ (int-ℕ y)))
        ( add-ℤ
          ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))
          ( neg-ℤ ((int-ℕ (succ-ℕ x)) *ℤ (int-ℕ y))))
      by
      ap
        ( λ p →
          add-ℤ
            ( ((neg-ℤ a) *ℤ (int-ℕ (succ-ℕ x))) +ℤ p)
            ( add-ℤ
              ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))
              ( neg-ℤ ((int-ℕ (succ-ℕ x)) *ℤ (int-ℕ y)))))
        ( commutative-mul-ℤ (int-ℕ y) (int-ℕ (succ-ℕ x)))
    ＝ add-ℤ
        ( add-ℤ
          ( (neg-ℤ a) *ℤ (int-ℕ (succ-ℕ x)))
          ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y)))
        ( add-ℤ
          ( (int-ℕ (succ-ℕ x)) *ℤ (int-ℕ y))
          ( neg-ℤ ((int-ℕ (succ-ℕ x)) *ℤ (int-ℕ y))))
      by
      interchange-law-add-add-ℤ
        ( (neg-ℤ a) *ℤ (int-ℕ (succ-ℕ x)))
        ( (int-ℕ (succ-ℕ x)) *ℤ (int-ℕ y))
        ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))
        ( neg-ℤ ((int-ℕ (succ-ℕ x)) *ℤ (int-ℕ y)))
    ＝ add-ℤ
        ( add-ℤ
          ( (neg-ℤ a) *ℤ (int-ℕ (succ-ℕ x)))
          ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y)))
        ( zero-ℤ)
      by
      ap
        ( add-ℤ
          ( add-ℤ
            ( (neg-ℤ a) *ℤ (int-ℕ (succ-ℕ x)))
            ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))))
          ( right-inverse-law-add-ℤ ((int-ℕ (succ-ℕ x)) *ℤ (int-ℕ y)))
    ＝ add-ℤ
        ( (neg-ℤ a) *ℤ (int-ℕ (succ-ℕ x)))
        ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))
      by
      right-unit-law-add-ℤ
        ( add-ℤ
          ( (neg-ℤ a) *ℤ (int-ℕ (succ-ℕ x)))
          ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y)))
    ＝ add-ℤ
        ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))
        ( (neg-ℤ a) *ℤ (int-ℕ (succ-ℕ x)))
      by
      commutative-add-ℤ
        ( (neg-ℤ a) *ℤ (int-ℕ (succ-ℕ x)))
        ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))
    ＝ add-ℤ
        ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))
        ( neg-ℤ (a *ℤ (int-ℕ (succ-ℕ x))))
      by
      ap
        ( ((int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y)) +ℤ_)
        ( left-negative-law-mul-ℤ a (int-ℕ (succ-ℕ x)))

  uy-z-case-split :
    ( ( is-nonnegative-ℤ
        ( ((int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y)) +ℤ (neg-ℤ (int-ℕ z)))) +
      ( is-nonnegative-ℤ
        ( neg-ℤ
          ( add-ℤ
            ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))
            ( neg-ℤ (int-ℕ z)))))) →
    is-distance-between-multiples-ℕ (succ-ℕ x) y z
  uy-z-case-split (inl uy-z) =
    ( abs-ℤ a ,
      nat-Fin (succ-ℕ x) u ,
      ( equational-reasoning
        dist-ℕ ((abs-ℤ a) *ℕ (succ-ℕ x)) ((nat-Fin (succ-ℕ x) u) *ℕ y)
        ＝ dist-ℕ ((nat-Fin (succ-ℕ x) u) *ℕ y) ((abs-ℤ a) *ℕ (succ-ℕ x))
          by
          symmetric-dist-ℕ
            ( (abs-ℤ a) *ℕ (succ-ℕ x))
            ( (nat-Fin (succ-ℕ x) u) *ℕ y)
        ＝ dist-ℤ
            ( int-ℕ ((nat-Fin (succ-ℕ x) u) *ℕ y))
            ( int-ℕ ((abs-ℤ a) *ℕ (succ-ℕ x)))
          by
          inv
            ( dist-int-ℕ
              ( (nat-Fin (succ-ℕ x) u) *ℕ y)
              ( (abs-ℤ a) *ℕ (succ-ℕ x)))
        ＝ dist-ℤ
            ( int-ℕ ((nat-Fin (succ-ℕ x) u) *ℕ y))
            ( (int-ℕ (abs-ℤ a)) *ℤ (int-ℕ (succ-ℕ x)))
          by
          ap
            ( dist-ℤ (int-ℕ ((nat-Fin (succ-ℕ x) u) *ℕ y)))
            ( inv (mul-int-ℕ (abs-ℤ a) (succ-ℕ x)))
        ＝ dist-ℤ
            ( (int-ℕ (nat-Fin (succ-ℕ x) u)) *ℤ (int-ℕ y))
            ( (int-ℕ (abs-ℤ a)) *ℤ (int-ℕ (succ-ℕ x)))
          by
          ap
            ( λ p → dist-ℤ p ((int-ℕ (abs-ℤ a)) *ℤ (int-ℕ (succ-ℕ x))))
            ( inv (mul-int-ℕ (nat-Fin (succ-ℕ x) u) y))
        ＝ dist-ℤ
            ( (int-ℕ (nat-Fin (succ-ℕ x) u)) *ℤ (int-ℕ y))
            ( a *ℤ (int-ℕ (succ-ℕ x)))
          by
          ap
            ( λ p →
              dist-ℤ
                ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))
                ( p *ℤ (int-ℕ (succ-ℕ x))))
            ( int-abs-is-nonnegative-ℤ a a-is-nonnegative-ℤ)
        ＝ abs-ℤ (int-ℕ z)
          by ap (abs-ℤ) a-eqn-pos
        ＝ z
          by abs-int-ℕ z))
    where
    a-is-nonnegative-ℤ : is-nonnegative-ℤ a
    a-is-nonnegative-ℤ =
      is-nonnegative-left-factor-mul-ℤ
        ( tr
          ( is-nonnegative-ℤ)
          ( inv
            ( pr2 (cong-div-mod-ℤ (succ-ℕ x) y z (u , p))))
          ( uy-z))
        ( is-nonnegative-int-ℕ (succ-ℕ x))

  uy-z-case-split (inr z-uy) =
    ( (abs-ℤ a) +ℕ y ,
      abs-ℤ ((int-ℕ (succ-ℕ x)) +ℤ (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u))) ,
      ( equational-reasoning
        dist-ℕ (((abs-ℤ a) +ℕ y) *ℕ (succ-ℕ x))
          (mul-ℕ (abs-ℤ ((int-ℕ (succ-ℕ x)) +ℤ
          (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))) y)
        ＝ dist-ℤ (int-ℕ (((abs-ℤ a) +ℕ y) *ℕ (succ-ℕ x)))
          (int-ℕ (mul-ℕ (abs-ℤ ((int-ℕ (succ-ℕ x)) +ℤ
          (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))) y))
        by inv (dist-int-ℕ (((abs-ℤ a) +ℕ y) *ℕ (succ-ℕ x))
          (mul-ℕ (abs-ℤ ((int-ℕ (succ-ℕ x)) +ℤ
          (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))) y))
        ＝ dist-ℤ ((int-ℕ ((abs-ℤ a) +ℕ y)) *ℤ (int-ℕ (succ-ℕ x)))
          (int-ℕ (mul-ℕ (abs-ℤ ((int-ℕ (succ-ℕ x)) +ℤ
          (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))) y))
        by ap (λ p → dist-ℤ p (int-ℕ (mul-ℕ (abs-ℤ ((int-ℕ (succ-ℕ x)) +ℤ
          (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))) y)))
          (inv (mul-int-ℕ ((abs-ℤ a) +ℕ y) (succ-ℕ x)))
        ＝ dist-ℤ (((int-ℕ (abs-ℤ a)) +ℤ (int-ℕ y)) *ℤ (int-ℕ (succ-ℕ x)))
          (int-ℕ (mul-ℕ (abs-ℤ ((int-ℕ (succ-ℕ x)) +ℤ
          (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))) y))
        by
          ap
            ( λ p →
              dist-ℤ
                ( p *ℤ (int-ℕ (succ-ℕ x)))
                ( int-ℕ (mul-ℕ (abs-ℤ ((int-ℕ (succ-ℕ x)) +ℤ
                  (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))) y)))
          (inv (add-int-ℕ (abs-ℤ a) y))
        ＝ dist-ℤ (((int-ℕ (abs-ℤ a)) +ℤ (int-ℕ y)) *ℤ (int-ℕ (succ-ℕ x)))
          (mul-ℤ (int-ℕ (abs-ℤ ((int-ℕ (succ-ℕ x)) +ℤ
          (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u))))) (int-ℕ y))
        by
          ap
            ( dist-ℤ (((int-ℕ (abs-ℤ a)) +ℤ (int-ℕ y)) *ℤ (int-ℕ (succ-ℕ x))))
            ( inv (mul-int-ℕ (abs-ℤ ((int-ℕ (succ-ℕ x)) +ℤ
              (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))) y))
        ＝ dist-ℤ (((int-ℕ (abs-ℤ a)) +ℤ (int-ℕ y)) *ℤ (int-ℕ (succ-ℕ x)))
          (mul-ℤ ((int-ℕ (succ-ℕ x)) +ℤ
            (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u))) (int-ℕ y))
          by ap (λ p → dist-ℤ (((int-ℕ (abs-ℤ a)) +ℤ (int-ℕ y)) *ℤ
              (int-ℕ (succ-ℕ x))) (p *ℤ (int-ℕ y)))
          (int-abs-is-nonnegative-ℤ ((int-ℕ (succ-ℕ x)) +ℤ
            (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u))) (int-ℤ-Mod-bounded x u))
        ＝ dist-ℤ
            ( ((int-ℕ (abs-ℤ (neg-ℤ a))) +ℤ (int-ℕ y)) *ℤ (int-ℕ (succ-ℕ x)))
            ( mul-ℤ
              ( (int-ℕ (succ-ℕ x)) +ℤ (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))
              ( int-ℕ y))
        by
          ap
            ( λ p →
              dist-ℤ
                ( ((int-ℕ p) +ℤ (int-ℕ y)) *ℤ (int-ℕ (succ-ℕ x)))
                ( mul-ℤ
                  ( (int-ℕ (succ-ℕ x)) +ℤ (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u)))
                  ( int-ℕ y)))
          (inv (abs-neg-ℤ a))
        ＝ dist-ℤ (((neg-ℤ a) +ℤ (int-ℕ y)) *ℤ (int-ℕ (succ-ℕ x)))
          (mul-ℤ
            ( (int-ℕ (succ-ℕ x)) +ℤ (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u))) (int-ℕ y))
        by ap (λ p → dist-ℤ ((p +ℤ (int-ℕ y)) *ℤ (int-ℕ (succ-ℕ x)))
          (((int-ℕ (succ-ℕ x)) +ℤ (neg-ℤ (int-ℤ-Mod (succ-ℕ x) u))) *ℤ
            (int-ℕ y)))
          (int-abs-is-nonnegative-ℤ (neg-ℤ a) neg-a-is-nonnegative-ℤ)
        ＝ abs-ℤ (int-ℕ z)
        by ap abs-ℤ (a-extra-eqn-neg ∙ a-eqn-pos)
        ＝ z by abs-int-ℕ z))
    where
    neg-a-is-nonnegative-ℤ : is-nonnegative-ℤ (neg-ℤ a)
    neg-a-is-nonnegative-ℤ =
      is-nonnegative-left-factor-mul-ℤ
        ( tr is-nonnegative-ℤ
          ( equational-reasoning
            ( neg-ℤ (((int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y)) +ℤ
              ( neg-ℤ (int-ℕ z))))
            ＝ ( neg-ℤ ((int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))) +ℤ
                ( neg-ℤ (neg-ℤ (int-ℕ z)))
              by
                ( distributive-neg-add-ℤ
                  ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))
                  ( neg-ℤ (int-ℕ z)))
            ＝ ( neg-ℤ ((int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))) +ℤ
                ( int-ℕ z)
              by
                ap
                  ( (neg-ℤ ((int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y))) +ℤ_)
                  ( neg-neg-ℤ (int-ℕ z))
            ＝ add-ℤ
              ( int-ℕ z)
              ( neg-ℤ ((int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y)))
              by
                commutative-add-ℤ
                  ( neg-ℤ ((int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y)))
                  ( int-ℕ z)
            ＝ (neg-ℤ a) *ℤ (int-ℕ (succ-ℕ x))
              by inv (pr2
                ( symmetric-cong-ℤ (int-ℕ (succ-ℕ x))
                ( (int-ℤ-Mod (succ-ℕ x) u) *ℤ (int-ℕ y)) (int-ℕ z)
                ( cong-div-mod-ℤ (succ-ℕ x) y z (u , p)))))
          ( z-uy))
          ( is-nonnegative-int-ℕ (succ-ℕ x))
```

### The type `is-distance-between-multiples-ℕ x y z` is decidable

```agda
is-decidable-is-distance-between-multiples-ℕ :
  (x y z : ℕ) → is-decidable (is-distance-between-multiples-ℕ x y z)
is-decidable-is-distance-between-multiples-ℕ x y z =
  decidable-div-ℤ-case-split
    (is-decidable-div-ℤ-Mod x (mod-ℕ x y) (mod-ℕ x z))
  where
  decidable-div-ℤ-case-split :
    ( div-ℤ-Mod x (mod-ℕ x y) (mod-ℕ x z) +
      ¬ ( div-ℤ-Mod x (mod-ℕ x y) (mod-ℕ x z))) →
    is-decidable (is-distance-between-multiples-ℕ x y z)
  decidable-div-ℤ-case-split (inl div-Mod) =
    inl (is-distance-between-multiples-div-mod-ℕ x y z div-Mod)
  decidable-div-ℤ-case-split (inr neg-div-Mod) =
    inr (λ dist → neg-div-Mod
      (div-mod-is-distance-between-multiples-ℕ x y z dist))
```

## Theorem

Since `is-distance-between-multiples-ℕ x y z` is decidable, we can prove
Bezout's lemma by the well-ordering principle. First, take the least positive
distance `d` between multiples of `x` and `y`.

```agda
pos-distance-between-multiples : (x y z : ℕ) → UU lzero
pos-distance-between-multiples x y z = is-nonzero-ℕ (x +ℕ y) →
  (is-nonzero-ℕ z) × (is-distance-between-multiples-ℕ x y z)

is-inhabited-pos-distance-between-multiples :
  (x y : ℕ) → Σ ℕ (pos-distance-between-multiples x y)
is-inhabited-pos-distance-between-multiples zero-ℕ zero-ℕ =
  pair zero-ℕ (λ H → ex-falso (H refl))
is-inhabited-pos-distance-between-multiples zero-ℕ (succ-ℕ y) =
  pair (succ-ℕ y) (λ H → pair' (is-nonzero-succ-ℕ y)
    (pair zero-ℕ (pair 1 (ap succ-ℕ (left-unit-law-add-ℕ y)))))
is-inhabited-pos-distance-between-multiples (succ-ℕ x) y = pair (succ-ℕ x)
  (λ H → pair' (is-nonzero-succ-ℕ x)
    (pair 1 (pair zero-ℕ (ap succ-ℕ (left-unit-law-add-ℕ x)))))

minimal-pos-distance-between-multiples :
  (x y : ℕ) → minimal-element-ℕ (pos-distance-between-multiples x y)
minimal-pos-distance-between-multiples x y =
  well-ordering-principle-ℕ
    ( pos-distance-between-multiples x y)
    ( λ z → is-decidable-function-type
      ( is-decidable-neg (is-decidable-is-zero-ℕ (x +ℕ y)))
      ( is-decidable-product (is-decidable-neg (is-decidable-is-zero-ℕ z))
        ( is-decidable-is-distance-between-multiples-ℕ x y z)))
    ( pr2 (is-inhabited-pos-distance-between-multiples x y))

minimal-positive-distance : (x y : ℕ) → ℕ
minimal-positive-distance x y = pr1 (minimal-pos-distance-between-multiples x y)
```

Then `d` divides both `x` and `y`. Since `gcd x y` divides any number of the
form `dist-ℕ (kx,ly)`, it follows that `gcd x y | d`, and hence that
`gcd x y ＝ d`.

```agda
minimal-positive-distance-is-distance :
  (x y : ℕ) → is-nonzero-ℕ (x +ℕ y) →
  (is-distance-between-multiples-ℕ x y (minimal-positive-distance x y))
minimal-positive-distance-is-distance x y nonzero =
  pr2 ((pr1 (pr2 (minimal-pos-distance-between-multiples x y))) nonzero)

minimal-positive-distance-is-minimal :
  (x y : ℕ) →
  is-lower-bound-ℕ
    ( pos-distance-between-multiples x y)
    ( minimal-positive-distance x y)
minimal-positive-distance-is-minimal x y =
  pr2 (pr2 (minimal-pos-distance-between-multiples x y))

minimal-positive-distance-nonzero :
  (x y : ℕ) →
  (is-nonzero-ℕ (x +ℕ y)) →
  (is-nonzero-ℕ (minimal-positive-distance x y))
minimal-positive-distance-nonzero x y nonzero =
  pr1 ((pr1 (pr2 (minimal-pos-distance-between-multiples x y))) nonzero)

minimal-positive-distance-leq-sym :
  (x y : ℕ) →
  leq-ℕ (minimal-positive-distance x y) (minimal-positive-distance y x)
minimal-positive-distance-leq-sym x y =
  minimal-positive-distance-is-minimal x y (minimal-positive-distance y x)
  (λ H →
    pair'
      ( minimal-positive-distance-nonzero
        ( y)
        ( x)
        ( λ K → H (commutative-add-ℕ x y ∙ K)))
      ( is-distance-between-multiples-sym-ℕ
        ( y)
        ( x)
        ( minimal-positive-distance y x)
        ( minimal-positive-distance-is-distance
          ( y)
          ( x)
          ( λ K → H (commutative-add-ℕ x y ∙ K)))))

minimal-positive-distance-sym :
  (x y : ℕ) → minimal-positive-distance x y ＝ minimal-positive-distance y x
minimal-positive-distance-sym x y = antisymmetric-leq-ℕ
  (minimal-positive-distance x y)
  (minimal-positive-distance y x)
  (minimal-positive-distance-leq-sym x y)
  (minimal-positive-distance-leq-sym y x)

minimal-positive-distance-x-coeff : (x y : ℕ) → (is-nonzero-ℕ (x +ℕ y)) → ℕ
minimal-positive-distance-x-coeff x y H =
  pr1 (minimal-positive-distance-is-distance x y H)

minimal-positive-distance-succ-x-coeff : (x y : ℕ) → ℕ
minimal-positive-distance-succ-x-coeff x y =
  minimal-positive-distance-x-coeff
    ( succ-ℕ x)
    ( y)
    ( tr
      ( is-nonzero-ℕ)
      ( inv (left-successor-law-add-ℕ x y))
      ( is-nonzero-succ-ℕ (x +ℕ y)))

minimal-positive-distance-y-coeff : (x y : ℕ) → (is-nonzero-ℕ (x +ℕ y)) → ℕ
minimal-positive-distance-y-coeff x y H =
  pr1 (pr2 (minimal-positive-distance-is-distance x y H))

minimal-positive-distance-succ-y-coeff : (x y : ℕ) → ℕ
minimal-positive-distance-succ-y-coeff x y =
  minimal-positive-distance-y-coeff
    ( succ-ℕ x)
    ( y)
    ( tr
      ( is-nonzero-ℕ)
      ( inv (left-successor-law-add-ℕ x y))
      ( is-nonzero-succ-ℕ (x +ℕ y)))

minimal-positive-distance-eqn :
  (x y : ℕ) (H : is-nonzero-ℕ (x +ℕ y)) →
  dist-ℕ
    ( (minimal-positive-distance-x-coeff x y H) *ℕ x)
    ( (minimal-positive-distance-y-coeff x y H) *ℕ y) ＝
  minimal-positive-distance x y
minimal-positive-distance-eqn x y H =
  pr2 (pr2 (minimal-positive-distance-is-distance x y H))

minimal-positive-distance-succ-eqn :
  (x y : ℕ) →
  dist-ℕ
    ( (minimal-positive-distance-succ-x-coeff x y) *ℕ (succ-ℕ x))
    ( (minimal-positive-distance-succ-y-coeff x y) *ℕ y) ＝
  minimal-positive-distance (succ-ℕ x) y
minimal-positive-distance-succ-eqn x y =
  minimal-positive-distance-eqn
    ( succ-ℕ x)
    ( y)
    ( tr
      ( is-nonzero-ℕ)
      ( inv (left-successor-law-add-ℕ x y))
      ( is-nonzero-succ-ℕ (x +ℕ y)))

minimal-positive-distance-div-succ-x-eqn :
  (x y : ℕ) →
  add-ℤ
    ( mul-ℤ
      ( int-ℕ
        ( quotient-euclidean-division-ℕ
          ( minimal-positive-distance (succ-ℕ x) y)
          ( succ-ℕ x)))
      ( int-ℕ (minimal-positive-distance (succ-ℕ x) y)))
    ( int-ℕ
      ( remainder-euclidean-division-ℕ
        ( minimal-positive-distance (succ-ℕ x) y)
        ( succ-ℕ x))) ＝
      int-ℕ (succ-ℕ x)
minimal-positive-distance-div-succ-x-eqn x y =
    equational-reasoning
      add-ℤ
        ( mul-ℤ
          ( int-ℕ
            ( quotient-euclidean-division-ℕ
              ( minimal-positive-distance (succ-ℕ x) y)
              ( succ-ℕ x)))
          ( int-ℕ (minimal-positive-distance (succ-ℕ x) y)))
        ( int-ℕ
          ( remainder-euclidean-division-ℕ
            ( minimal-positive-distance (succ-ℕ x) y)
            ( succ-ℕ x)))
      ＝ add-ℤ
          ( int-ℕ
            ( mul-ℕ
              ( quotient-euclidean-division-ℕ
                ( minimal-positive-distance (succ-ℕ x) y)
                ( succ-ℕ x))
              ( minimal-positive-distance (succ-ℕ x) y)))
          ( int-ℕ
            ( remainder-euclidean-division-ℕ
              ( minimal-positive-distance (succ-ℕ x) y)
              ( succ-ℕ x)))
          by
            ( ap
              ( _+ℤ
                ( int-ℕ
                  ( remainder-euclidean-division-ℕ
                    ( minimal-positive-distance (succ-ℕ x) y)
                    ( succ-ℕ x))))
              ( mul-int-ℕ
                ( quotient-euclidean-division-ℕ
                  ( minimal-positive-distance (succ-ℕ x) y)
                  ( succ-ℕ x))
                ( minimal-positive-distance (succ-ℕ x) y)))
      ＝ int-ℕ
            ( add-ℕ
              ( mul-ℕ
                ( quotient-euclidean-division-ℕ
                  ( minimal-positive-distance (succ-ℕ x) y)
                  ( succ-ℕ x))
                ( minimal-positive-distance (succ-ℕ x) y))
              ( remainder-euclidean-division-ℕ
                ( minimal-positive-distance (succ-ℕ x) y)
                ( succ-ℕ x)))
          by
            ( add-int-ℕ
              ( mul-ℕ
                ( quotient-euclidean-division-ℕ
                  ( minimal-positive-distance (succ-ℕ x) y)
                  ( succ-ℕ x))
                ( minimal-positive-distance (succ-ℕ x) y))
              ( remainder-euclidean-division-ℕ
                ( minimal-positive-distance (succ-ℕ x) y)
                ( succ-ℕ x)))
      ＝ int-ℕ (succ-ℕ x)
          by
            ap
              ( int-ℕ)
              ( eq-euclidean-division-ℕ
                ( minimal-positive-distance (succ-ℕ x) y)
                ( succ-ℕ x))

remainder-min-dist-succ-x-le-min-dist :
  (x y : ℕ) →
  le-ℕ
    ( remainder-euclidean-division-ℕ
      ( minimal-positive-distance (succ-ℕ x) y)
      ( succ-ℕ x))
    ( minimal-positive-distance (succ-ℕ x) y)
remainder-min-dist-succ-x-le-min-dist x y =
  strict-upper-bound-remainder-euclidean-division-ℕ
    ( minimal-positive-distance (succ-ℕ x) y)
    ( succ-ℕ x)
    ( minimal-positive-distance-nonzero
      ( succ-ℕ x)
      ( y)
      ( tr
        ( is-nonzero-ℕ)
        ( inv (left-successor-law-add-ℕ x y))
        ( is-nonzero-succ-ℕ (x +ℕ y))))

remainder-min-dist-succ-x-is-distance :
  (x y : ℕ) →
  (is-distance-between-multiples-ℕ
    ( succ-ℕ x)
    ( y)
    ( remainder-euclidean-division-ℕ
      ( minimal-positive-distance (succ-ℕ x) y)
      ( succ-ℕ x)))
remainder-min-dist-succ-x-is-distance x y =
  sx-ty-case-split (linear-leq-ℕ (s *ℕ (succ-ℕ x)) (t *ℕ y))
  where
  d : ℕ
  d = minimal-positive-distance (succ-ℕ x) y

  s : ℕ
  s = minimal-positive-distance-succ-x-coeff x y

  t : ℕ
  t = minimal-positive-distance-succ-y-coeff x y

  q : ℕ
  q = quotient-euclidean-division-ℕ d (succ-ℕ x)

  r : ℕ
  r = remainder-euclidean-division-ℕ d (succ-ℕ x)

  dist-sx-ty-eq-d : dist-ℕ (s *ℕ (succ-ℕ x)) (t *ℕ y) ＝ d
  dist-sx-ty-eq-d = minimal-positive-distance-succ-eqn x y

  sx-ty-case-split :
    ( leq-ℕ (s *ℕ (succ-ℕ x)) (t *ℕ y) +
      leq-ℕ (t *ℕ y) (s *ℕ (succ-ℕ x))) →
    is-distance-between-multiples-ℕ (succ-ℕ x) y r
  sx-ty-case-split (inl sxty) =
    ((q *ℕ s) +ℕ 1 , q *ℕ t , inv (dist-eqn))
    where
    add-dist-eqn :
      int-ℕ d ＝
      ((int-ℕ t) *ℤ (int-ℕ y)) +ℤ ((neg-ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x)))
    add-dist-eqn =
      equational-reasoning
        int-ℕ d
        ＝ ((int-ℕ d) +ℤ (int-ℕ (s *ℕ (succ-ℕ x)))) +ℤ
          (neg-ℤ (int-ℕ (s *ℕ (succ-ℕ x))))
          by
          inv
            ( is-retraction-right-add-neg-ℤ (int-ℕ (s *ℕ (succ-ℕ x))) (int-ℕ d))
        ＝ (int-ℕ (d +ℕ (s *ℕ (succ-ℕ x)))) +ℤ
          (neg-ℤ (int-ℕ (s *ℕ (succ-ℕ x))))
          by
          ap
            ( _+ℤ (neg-ℤ (int-ℕ (s *ℕ (succ-ℕ x)))))
            ( add-int-ℕ d (s *ℕ (succ-ℕ x)))
        ＝ (int-ℕ (t *ℕ y)) +ℤ (neg-ℤ (int-ℕ (s *ℕ (succ-ℕ x))))
          by ap (λ H → (int-ℕ H) +ℤ (neg-ℤ (int-ℕ (s *ℕ (succ-ℕ x)))))
            (rewrite-left-dist-add-ℕ d (s *ℕ (succ-ℕ x))
              (t *ℕ y) sxty (inv (dist-sx-ty-eq-d)))
        ＝ ((int-ℕ t) *ℤ (int-ℕ y)) +ℤ
          (neg-ℤ (int-ℕ (s *ℕ (succ-ℕ x))))
          by
          ap
            ( _+ℤ (neg-ℤ (int-ℕ (s *ℕ (succ-ℕ x)))))
            ( inv (mul-int-ℕ t y))
        ＝ ((int-ℕ t) *ℤ (int-ℕ y)) +ℤ
          (neg-ℤ ((int-ℕ s) *ℤ (int-ℕ (succ-ℕ x))))
          by
          ap
            ( λ H → ((int-ℕ t) *ℤ (int-ℕ y)) +ℤ (neg-ℤ H))
            ( inv (mul-int-ℕ s (succ-ℕ x)))
        ＝ ((int-ℕ t) *ℤ (int-ℕ y)) +ℤ
          ((neg-ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x)))
          by
          ap
            ( ((int-ℕ t) *ℤ (int-ℕ y)) +ℤ_)
            ( inv (left-negative-law-mul-ℤ (int-ℕ s) (int-ℕ (succ-ℕ x))))

    isolate-rem-eqn :
      int-ℕ r ＝
      add-ℤ
        ( neg-ℤ
          ( mul-ℤ
            ( int-ℕ q)
            ( add-ℤ
              ( (int-ℕ t) *ℤ (int-ℕ y))
              ( (neg-ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x))))))
        ( int-ℕ (succ-ℕ x))
    isolate-rem-eqn =
      equational-reasoning
        int-ℕ r
        ＝ add-ℤ (neg-ℤ ((int-ℕ q) *ℤ (((int-ℕ t) *ℤ (int-ℕ y)) +ℤ
            ((neg-ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x))))))
          (add-ℤ ((int-ℕ q) *ℤ (((int-ℕ t) *ℤ (int-ℕ y)) +ℤ
              ((neg-ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x)))))
          (int-ℕ r))
          by inv (is-retraction-left-add-neg-ℤ
            ((int-ℕ q) *ℤ (((int-ℕ t) *ℤ (int-ℕ y)) +ℤ
            ((neg-ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x)))))
            (int-ℕ r))
        ＝ add-ℤ (neg-ℤ ((int-ℕ q) *ℤ (((int-ℕ t) *ℤ (int-ℕ y)) +ℤ
            ((neg-ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x))))))
          (((int-ℕ q) *ℤ (int-ℕ d)) +ℤ (int-ℕ r))
          by
            ap
              ( λ H →
                add-ℤ
                  ( neg-ℤ
                    ( mul-ℤ
                      ( int-ℕ q)
                      ( add-ℤ
                        ( (int-ℕ t) *ℤ (int-ℕ y))
                        ( (neg-ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x))))))
                  ( ((int-ℕ q) *ℤ H) +ℤ (int-ℕ r)))
              ( inv add-dist-eqn)
        ＝ add-ℤ
            ( neg-ℤ
              ( mul-ℤ
                ( int-ℕ q)
                ( add-ℤ
                  ( (int-ℕ t) *ℤ (int-ℕ y))
                  ( (neg-ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x))))))
            ( int-ℕ (succ-ℕ x))
          by
            ap
              ( add-ℤ
                ( neg-ℤ
                  ( mul-ℤ
                    ( int-ℕ q)
                    ( add-ℤ
                      ( (int-ℕ t) *ℤ (int-ℕ y))
                      ( (neg-ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x)))))))
              ( minimal-positive-distance-div-succ-x-eqn x y)

    rearrange-arith-eqn :
      add-ℤ (neg-ℤ ((int-ℕ q) *ℤ (((int-ℕ t) *ℤ (int-ℕ y)) +ℤ
        ((neg-ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x)))))) (int-ℕ (succ-ℕ x))
      ＝ add-ℤ ((((int-ℕ q) *ℤ (int-ℕ s)) +ℤ one-ℤ) *ℤ
          (int-ℕ (succ-ℕ x)))
        (neg-ℤ (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)))
    rearrange-arith-eqn =
      equational-reasoning
        add-ℤ (neg-ℤ ((int-ℕ q) *ℤ (((int-ℕ t) *ℤ (int-ℕ y)) +ℤ
          ((neg-ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x)))))) (int-ℕ (succ-ℕ x))
        ＝ add-ℤ (neg-ℤ (((int-ℕ q) *ℤ ((int-ℕ t) *ℤ (int-ℕ y))) +ℤ
          ((int-ℕ q) *ℤ ((neg-ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x))))))
            (int-ℕ (succ-ℕ x))
          by (ap (λ H → (neg-ℤ H) +ℤ (int-ℕ (succ-ℕ x)))
            (left-distributive-mul-add-ℤ (int-ℕ q) ((int-ℕ t) *ℤ (int-ℕ y))
              ((neg-ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x)))))
        ＝ add-ℤ (neg-ℤ ((((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ
          ((int-ℕ q) *ℤ ((neg-ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x))))))
            (int-ℕ (succ-ℕ x))
          by (ap (λ H → add-ℤ (neg-ℤ (H +ℤ (mul-ℤ (int-ℕ q)
            ((neg-ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x)))))) (int-ℕ (succ-ℕ x)))
              (inv (associative-mul-ℤ (int-ℕ q) (int-ℕ t) (int-ℕ y))))
        ＝ add-ℤ (neg-ℤ ((((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ
          (neg-ℤ (((int-ℕ q) *ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x))))))
            (int-ℕ (succ-ℕ x))
          by
            ap
              ( λ H →
                add-ℤ
                  ( neg-ℤ
                    ( (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ H))
                  ( int-ℕ (succ-ℕ x)))
            ( equational-reasoning
                ((int-ℕ q) *ℤ ((neg-ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x))))
                ＝ ((int-ℕ q) *ℤ (neg-ℤ (int-ℕ s))) *ℤ (int-ℕ (succ-ℕ x))
                  by
                    inv
                      ( associative-mul-ℤ
                        ( int-ℕ q)
                        ( neg-ℤ (int-ℕ s))
                        ( int-ℕ (succ-ℕ x)))
                ＝ (neg-ℤ ((int-ℕ q) *ℤ (int-ℕ s))) *ℤ (int-ℕ (succ-ℕ x))
                  by ap (_*ℤ (int-ℕ (succ-ℕ x)))
                  (right-negative-law-mul-ℤ (int-ℕ q) (int-ℕ s))
                ＝ neg-ℤ (((int-ℕ q) *ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x)))
                  by
                    left-negative-law-mul-ℤ
                      ( (int-ℕ q) *ℤ (int-ℕ s))
                      ( int-ℕ (succ-ℕ x)))
        ＝ add-ℤ
            ( add-ℤ
              ( neg-ℤ (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)))
              ( neg-ℤ
                ( neg-ℤ
                  ( ((int-ℕ q) *ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x))))))
            (int-ℕ (succ-ℕ x))
          by
            ap
              ( _+ℤ (int-ℕ (succ-ℕ x)))
              ( distributive-neg-add-ℤ
                ( ((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y))
                ( neg-ℤ (((int-ℕ q) *ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x)))))
        ＝ add-ℤ
            ( add-ℤ
              ( neg-ℤ (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)))
              ( ((int-ℕ q) *ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x))))
            ( int-ℕ (succ-ℕ x))
          by
            ap
              ( λ H →
              add-ℤ
                ( (neg-ℤ (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y))) +ℤ H)
                ( int-ℕ (succ-ℕ x)))
              ( neg-neg-ℤ
                ( ((int-ℕ q) *ℤ ((int-ℕ s))) *ℤ (int-ℕ (succ-ℕ x))))
        ＝ (neg-ℤ (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y))) +ℤ
          ((((int-ℕ q) *ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x))) +ℤ
            (int-ℕ (succ-ℕ x)))
          by associative-add-ℤ
            (neg-ℤ (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)))
            (((int-ℕ q) *ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x)))
            (int-ℕ (succ-ℕ x))
        ＝ add-ℤ ((((int-ℕ q) *ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x))) +ℤ
          (int-ℕ (succ-ℕ x)))
          (neg-ℤ (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)))
          by commutative-add-ℤ
            (neg-ℤ (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)))
            ((((int-ℕ q) *ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x))) +ℤ
            (int-ℕ (succ-ℕ x)))
        ＝ add-ℤ
            ( mul-ℤ
              ( ((int-ℕ q) *ℤ (int-ℕ s)) +ℤ one-ℤ)
              ( int-ℕ (succ-ℕ x)))
            ( neg-ℤ (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)))
          by
            ap
              ( _+ℤ (neg-ℤ (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y))))
              ( ap
                ( (((int-ℕ q) *ℤ ((int-ℕ s))) *ℤ (int-ℕ (succ-ℕ x))) +ℤ_)
                ( left-unit-law-mul-ℤ (int-ℕ (succ-ℕ x))) ∙
                ( inv
                  ( right-distributive-mul-add-ℤ
                    ( (int-ℕ q) *ℤ (int-ℕ s))
                    ( one-ℤ)
                    ( int-ℕ (succ-ℕ x)))))

    dist-eqn :
      r ＝ dist-ℕ (((q *ℕ s) +ℕ 1) *ℕ (succ-ℕ x)) ((q *ℕ t) *ℕ y)
    dist-eqn =
      equational-reasoning
        r
        ＝ abs-ℤ (int-ℕ r)
          by (inv (abs-int-ℕ r))
        ＝ dist-ℤ ((((int-ℕ q) *ℤ (int-ℕ s)) +ℤ one-ℤ) *ℤ
            (int-ℕ (succ-ℕ x)))
          (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y))
          by (ap (abs-ℤ) (isolate-rem-eqn ∙ rearrange-arith-eqn))
        ＝ dist-ℤ
            ( ((int-ℕ (q *ℕ s)) +ℤ (int-ℕ 1)) *ℤ (int-ℕ (succ-ℕ x)))
            ( ((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y))
          by ap (λ H → dist-ℤ ((H +ℤ (int-ℕ 1)) *ℤ (int-ℕ (succ-ℕ x)))
            (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)))
            (mul-int-ℕ q s)
        ＝ dist-ℤ ((int-ℕ ((q *ℕ s) +ℕ 1)) *ℤ (int-ℕ (succ-ℕ x)))
          (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y))
          by ap (λ H → dist-ℤ (H *ℤ (int-ℕ (succ-ℕ x)))
            (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)))
            (add-int-ℕ (q *ℕ s) 1)
        ＝ dist-ℤ (int-ℕ (((q *ℕ s) +ℕ 1) *ℕ (succ-ℕ x)))
          (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y))
          by ap (λ H → dist-ℤ H (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)))
            (mul-int-ℕ ((q *ℕ s) +ℕ 1) (succ-ℕ x))
        ＝ dist-ℤ (int-ℕ (((q *ℕ s) +ℕ 1) *ℕ (succ-ℕ x)))
          ((int-ℕ (q *ℕ t)) *ℤ (int-ℕ y))
          by ap (λ H → dist-ℤ (int-ℕ (((q *ℕ s) +ℕ 1) *ℕ (succ-ℕ x)))
            (H *ℤ (int-ℕ y)))
            (mul-int-ℕ q t)
        ＝ dist-ℤ (int-ℕ (((q *ℕ s) +ℕ 1) *ℕ (succ-ℕ x)))
          (int-ℕ ((q *ℕ t) *ℕ y))
          by ap (dist-ℤ (int-ℕ (((q *ℕ s) +ℕ 1) *ℕ (succ-ℕ x))))
            (mul-int-ℕ (q *ℕ t) y)
        ＝ dist-ℕ (((q *ℕ s) +ℕ 1) *ℕ (succ-ℕ x))
          ((q *ℕ t) *ℕ y)
          by dist-int-ℕ (((q *ℕ s) +ℕ 1) *ℕ (succ-ℕ x))
            ((q *ℕ t) *ℕ y)

  sx-ty-case-split (inr tysx) =
    (abs-ℤ (((int-ℕ q) *ℤ (int-ℕ s)) +ℤ (neg-ℤ one-ℤ)) ,
      (q *ℕ t) , inv (dist-eqn))
    where
    rewrite-dist : (t *ℕ y) +ℕ d ＝ (s *ℕ (succ-ℕ x))
    rewrite-dist =
      rewrite-right-dist-add-ℕ
        ( t *ℕ y)
        ( d)
        ( s *ℕ (succ-ℕ x))
        ( tysx)
        ( inv (dist-sx-ty-eq-d) ∙
          symmetric-dist-ℕ (s *ℕ (succ-ℕ x)) (t *ℕ y))

    quotient-min-dist-succ-x-nonzero : is-nonzero-ℕ q
    quotient-min-dist-succ-x-nonzero iszero =
      contradiction-le-ℕ (succ-ℕ x) d le-x-d leq-d-x
      where
      x-r-equality : succ-ℕ x ＝ r
      x-r-equality =
        equational-reasoning
          succ-ℕ x
          ＝ (q *ℕ d) +ℕ r
            by (inv (eq-euclidean-division-ℕ d (succ-ℕ x)))
          ＝ (0 *ℕ d) +ℕ r
            by (ap (λ H → (H *ℕ d) +ℕ r) iszero)
          ＝ 0 +ℕ r
            by (ap (_+ℕ r) (left-zero-law-mul-ℕ d))
          ＝ r
            by (left-unit-law-add-ℕ r)

      le-x-d : le-ℕ (succ-ℕ x) d
      le-x-d =
        tr
          ( λ n → le-ℕ n d)
          ( inv (x-r-equality))
          ( remainder-min-dist-succ-x-le-min-dist x y)

      x-pos-dist : pos-distance-between-multiples (succ-ℕ x) y (succ-ℕ x)
      x-pos-dist H =
        pair'
          ( is-nonzero-succ-ℕ x)
          ( pair 1 (pair 0 (ap succ-ℕ (left-unit-law-add-ℕ x))))

      leq-d-x : leq-ℕ d (succ-ℕ x)
      leq-d-x =
        minimal-positive-distance-is-minimal (succ-ℕ x) y (succ-ℕ x) x-pos-dist

    min-dist-succ-x-coeff-nonzero : is-nonzero-ℕ s
    min-dist-succ-x-coeff-nonzero iszero =
      minimal-positive-distance-nonzero
        ( succ-ℕ x)
        ( y)
        ( tr
          ( is-nonzero-ℕ)
          ( inv (left-successor-law-add-ℕ x y))
          ( is-nonzero-succ-ℕ (x +ℕ y)))
        ( d-is-zero)
      where
      zero-addition : (t *ℕ y) +ℕ d ＝ 0
      zero-addition =
        equational-reasoning
          (t *ℕ y) +ℕ d
          ＝ (s *ℕ (succ-ℕ x))
            by rewrite-dist
          ＝ (zero-ℕ *ℕ (succ-ℕ x))
            by (ap (_*ℕ (succ-ℕ x)) iszero)
          ＝ zero-ℕ
            by (left-zero-law-mul-ℕ (succ-ℕ x))

      d-is-zero : is-zero-ℕ d
      d-is-zero = is-zero-right-is-zero-add-ℕ (t *ℕ y) d (zero-addition)

    coeff-nonnegative : leq-ℤ one-ℤ ((int-ℕ q) *ℤ (int-ℕ s))
    coeff-nonnegative = tr (leq-ℤ one-ℤ)
      (inv (mul-int-ℕ q s)) (leq-int-ℕ 1 (q *ℕ s)
        (leq-succ-le-ℕ 0 (q *ℕ s) (le-zero-is-nonzero-ℕ (q *ℕ s)
          (is-nonzero-mul-ℕ q s quotient-min-dist-succ-x-nonzero
            min-dist-succ-x-coeff-nonzero))))

    add-dist-eqn :
      int-ℕ d ＝
      ((neg-ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ ((int-ℕ s) *ℤ (int-ℕ (succ-ℕ x)))
    add-dist-eqn =
      equational-reasoning
        int-ℕ d
        ＝ (neg-ℤ (int-ℕ (t *ℕ y))) +ℤ ((int-ℕ (t *ℕ y)) +ℤ (int-ℕ d))
          by inv (is-retraction-left-add-neg-ℤ (int-ℕ (t *ℕ y)) (int-ℕ d))
        ＝ (neg-ℤ (int-ℕ (t *ℕ y))) +ℤ (int-ℕ ((t *ℕ y) +ℕ d))
          by ap ((neg-ℤ (int-ℕ (t *ℕ y))) +ℤ_) (add-int-ℕ (t *ℕ y) d)
        ＝ (neg-ℤ (int-ℕ (t *ℕ y))) +ℤ (int-ℕ (s *ℕ (succ-ℕ x)))
          by ap (λ H → (neg-ℤ (int-ℕ (t *ℕ y))) +ℤ (int-ℕ H)) rewrite-dist
        ＝ (neg-ℤ ((int-ℕ t) *ℤ (int-ℕ y))) +ℤ (int-ℕ (s *ℕ (succ-ℕ x)))
          by
            ap
              ( λ H → (neg-ℤ H) +ℤ (int-ℕ (s *ℕ (succ-ℕ x))))
              ( inv (mul-int-ℕ t y))
        ＝ ((neg-ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ (int-ℕ (s *ℕ (succ-ℕ x)))
          by
            ap
              ( _+ℤ (int-ℕ (s *ℕ (succ-ℕ x))))
              ( inv (left-negative-law-mul-ℤ (int-ℕ t) (int-ℕ y)))
        ＝ ((neg-ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ ((int-ℕ s) *ℤ (int-ℕ (succ-ℕ x)))
          by
            ap
              ( ((neg-ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ_)
              ( inv (mul-int-ℕ s (succ-ℕ x)))

    isolate-rem-eqn :
      int-ℕ r ＝
      add-ℤ
        ( neg-ℤ
          ( mul-ℤ
            ( int-ℕ q)
            ( add-ℤ
              ( (neg-ℤ (int-ℕ t)) *ℤ (int-ℕ y))
              ( (int-ℕ s) *ℤ (int-ℕ (succ-ℕ x))))))
        ( int-ℕ (succ-ℕ x))
    isolate-rem-eqn =
      equational-reasoning
        int-ℕ r
        ＝ add-ℤ
            ( neg-ℤ
              ( mul-ℤ
                ( int-ℕ q)
                ( add-ℤ
                  ( (neg-ℤ (int-ℕ t)) *ℤ (int-ℕ y))
                  ( ((int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x))))))
            ( add-ℤ
              ( mul-ℤ
                ( int-ℕ q)
                ( add-ℤ
                  ( (neg-ℤ (int-ℕ t)) *ℤ (int-ℕ y))
                  ( (int-ℕ s) *ℤ (int-ℕ (succ-ℕ x)))))
              ( int-ℕ r))
          by inv (is-retraction-left-add-neg-ℤ (mul-ℤ (int-ℕ q)
            (((neg-ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ
            ((int-ℕ s) *ℤ (int-ℕ (succ-ℕ x))))) (int-ℕ r))
        ＝ add-ℤ
            ( neg-ℤ
              ( mul-ℤ
                ( int-ℕ q)
                ( add-ℤ
                  ( (neg-ℤ (int-ℕ t)) *ℤ (int-ℕ y))
                  ( (int-ℕ s) *ℤ (int-ℕ (succ-ℕ x))))))
            ( ((int-ℕ q) *ℤ (int-ℕ d)) +ℤ (int-ℕ r))
          by
            ap
              ( λ H →
                add-ℤ
                  ( neg-ℤ
                    ( mul-ℤ
                      ( int-ℕ q)
                      ( add-ℤ
                        ( (neg-ℤ (int-ℕ t)) *ℤ (int-ℕ y))
                        ( (int-ℕ s) *ℤ (int-ℕ (succ-ℕ x))))))
                  ( ((int-ℕ q) *ℤ H) +ℤ (int-ℕ r)))
              ( inv add-dist-eqn)
        ＝ add-ℤ
            ( neg-ℤ
              ( ( int-ℕ q) *ℤ
                ( ( (neg-ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ
                  ( (int-ℕ s) *ℤ (int-ℕ (succ-ℕ x))))))
            ( int-ℕ (succ-ℕ x))
          by
            ap
              ( add-ℤ
                ( neg-ℤ
                  ( mul-ℤ
                    ( int-ℕ q)
                    ( add-ℤ
                      ( (neg-ℤ (int-ℕ t)) *ℤ (int-ℕ y))
                      ( (int-ℕ s) *ℤ (int-ℕ (succ-ℕ x)))))))
              ( minimal-positive-distance-div-succ-x-eqn x y)

    rearrange-arith :
      add-ℤ (neg-ℤ ((int-ℕ q) *ℤ (((neg-ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ
        ((int-ℕ s) *ℤ (int-ℕ (succ-ℕ x)))))) (int-ℕ (succ-ℕ x))
      ＝ (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ
        (neg-ℤ ((((int-ℕ q) *ℤ (int-ℕ s)) +ℤ (neg-ℤ one-ℤ)) *ℤ
          (int-ℕ (succ-ℕ x))))
    rearrange-arith =
      equational-reasoning
        add-ℤ (neg-ℤ ((int-ℕ q) *ℤ (((neg-ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ
          ((int-ℕ s) *ℤ (int-ℕ (succ-ℕ x)))))) (int-ℕ (succ-ℕ x))
        ＝ add-ℤ
            ( neg-ℤ
              ( add-ℤ
                ( (int-ℕ q) *ℤ ((neg-ℤ (int-ℕ t)) *ℤ (int-ℕ y)))
                ( (int-ℕ q) *ℤ ((int-ℕ s) *ℤ (int-ℕ (succ-ℕ x))))))
            ( int-ℕ (succ-ℕ x))
          by
            ap
              ( λ H → (neg-ℤ H) +ℤ (int-ℕ (succ-ℕ x)))
              ( left-distributive-mul-add-ℤ
                ( int-ℕ q)
                ( (neg-ℤ (int-ℕ t)) *ℤ (int-ℕ y))
                ( (int-ℕ s) *ℤ (int-ℕ (succ-ℕ x))))
        ＝ add-ℤ
            ( neg-ℤ
              ( add-ℤ
                ( ((int-ℕ q) *ℤ (neg-ℤ (int-ℕ t))) *ℤ (int-ℕ y))
                ( (int-ℕ q) *ℤ ((int-ℕ s) *ℤ (int-ℕ (succ-ℕ x))))))
            ( int-ℕ (succ-ℕ x))
          by
            ap
              ( λ H →
                add-ℤ
                  ( neg-ℤ
                    ( H +ℤ ((int-ℕ q) *ℤ ((int-ℕ s) *ℤ (int-ℕ (succ-ℕ x))))))
                  ( int-ℕ (succ-ℕ x)))
              ( inv (associative-mul-ℤ (int-ℕ q) (neg-ℤ (int-ℕ t)) (int-ℕ y)))
        ＝ add-ℤ
            ( neg-ℤ
              ( add-ℤ
                ( ((int-ℕ q) *ℤ (neg-ℤ (int-ℕ t))) *ℤ (int-ℕ y))
                ( ((int-ℕ q) *ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x)))))
            ( int-ℕ (succ-ℕ x))
          by
            ap
              ( λ H →
                add-ℤ
                  ( neg-ℤ
                    ( add-ℤ
                      ( ((int-ℕ q) *ℤ (neg-ℤ (int-ℕ t))) *ℤ (int-ℕ y))
                      ( H)))
                  ( int-ℕ (succ-ℕ x)))
            ( inv (associative-mul-ℤ (int-ℕ q) (int-ℕ s) (int-ℕ (succ-ℕ x))))
        ＝ add-ℤ
            ( neg-ℤ
              ( add-ℤ
                ( (neg-ℤ ((int-ℕ q) *ℤ (int-ℕ t))) *ℤ (int-ℕ y))
                ( ((int-ℕ q) *ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x)))))
            ( int-ℕ (succ-ℕ x))
          by
            ap
              ( λ H →
                add-ℤ
                  ( neg-ℤ
                    ( add-ℤ
                      ( H *ℤ (int-ℕ y))
                      ( mul-ℤ
                        ( (int-ℕ q) *ℤ (int-ℕ s))
                        ( int-ℕ (succ-ℕ x)))))
                  ( int-ℕ (succ-ℕ x)))
              ( right-negative-law-mul-ℤ (int-ℕ q) (int-ℕ t))
        ＝ add-ℤ
            ( add-ℤ
              ( neg-ℤ ((neg-ℤ ((int-ℕ q) *ℤ (int-ℕ t))) *ℤ (int-ℕ y)))
              ( neg-ℤ (((int-ℕ q) *ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x)))))
            ( int-ℕ (succ-ℕ x))
          by ap (_+ℤ (int-ℕ (succ-ℕ x)))
            (distributive-neg-add-ℤ
              ((neg-ℤ ((int-ℕ q) *ℤ (int-ℕ t))) *ℤ (int-ℕ y))
              (((int-ℕ q) *ℤ (int-ℕ s)) *ℤ
              (int-ℕ (succ-ℕ x))))
        ＝ add-ℤ
            ( add-ℤ
              ( (neg-ℤ (neg-ℤ ((int-ℕ q) *ℤ (int-ℕ t)))) *ℤ (int-ℕ y))
              ( neg-ℤ (((int-ℕ q) *ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x)))))
            ( int-ℕ (succ-ℕ x))
          by
            ap
            ( λ H →
              add-ℤ
                ( add-ℤ
                  ( H)
                  ( neg-ℤ
                    ( ((int-ℕ q) *ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x)))))
                ( int-ℕ (succ-ℕ x)))
            ( inv
              ( left-negative-law-mul-ℤ
                ( neg-ℤ ((int-ℕ q) *ℤ (int-ℕ t)))
                ( int-ℕ y)))
        ＝ add-ℤ ((((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ
            (neg-ℤ (((int-ℕ q) *ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x)))))
            (int-ℕ (succ-ℕ x))
          by ap (λ H → (add-ℤ ((H *ℤ (int-ℕ y)) +ℤ
            (neg-ℤ (((int-ℕ q) *ℤ (int-ℕ s)) *ℤ (int-ℕ (succ-ℕ x)))))
              (int-ℕ (succ-ℕ x))))
            (neg-neg-ℤ ((int-ℕ q) *ℤ (int-ℕ t)))
        ＝ add-ℤ ((((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ
            ((neg-ℤ ((int-ℕ q) *ℤ (int-ℕ s))) *ℤ (int-ℕ (succ-ℕ x))))
          (int-ℕ (succ-ℕ x))
          by
            ap
              ( λ H →
                add-ℤ
                  ( (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ H)
                  ( int-ℕ (succ-ℕ x)))
              ( inv
                ( left-negative-law-mul-ℤ
                  ( (int-ℕ q) *ℤ (int-ℕ s))
                  ( int-ℕ (succ-ℕ x))))
        ＝ (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ
          (((neg-ℤ ((int-ℕ q) *ℤ (int-ℕ s))) *ℤ (int-ℕ (succ-ℕ x))) +ℤ
            (int-ℕ (succ-ℕ x)))
          by associative-add-ℤ (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y))
            ((neg-ℤ ((int-ℕ q) *ℤ (int-ℕ s))) *ℤ (int-ℕ (succ-ℕ x)))
            (int-ℕ (succ-ℕ x))
        ＝ (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ
          (((neg-ℤ ((int-ℕ q) *ℤ (int-ℕ s))) *ℤ (int-ℕ (succ-ℕ x))) +ℤ
            ((neg-ℤ (neg-ℤ one-ℤ)) *ℤ (int-ℕ (succ-ℕ x))))
          by
            ap
              ( λ H →
                add-ℤ
                  ( ((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y))
                  ( add-ℤ
                    ( mul-ℤ
                      ( neg-ℤ ((int-ℕ q) *ℤ (int-ℕ s)))
                      ( int-ℕ (succ-ℕ x)))
                    ( H *ℤ (int-ℕ (succ-ℕ x)))))
              ( inv (neg-neg-ℤ one-ℤ))
        ＝ add-ℤ
            ( ((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y))
            ( mul-ℤ
              ( add-ℤ
                ( neg-ℤ ((int-ℕ q) *ℤ (int-ℕ s)))
                ( neg-ℤ (neg-ℤ one-ℤ)))
              ( int-ℕ (succ-ℕ x)))
          by
            ap
              ( (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ_)
              ( inv
                ( right-distributive-mul-add-ℤ
                  ( neg-ℤ ((int-ℕ q) *ℤ (int-ℕ s)))
                  ( neg-ℤ (neg-ℤ one-ℤ))
                  ( int-ℕ (succ-ℕ x))))
        ＝ add-ℤ
            ( ((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y))
            ( mul-ℤ (neg-ℤ (((int-ℕ q) *ℤ (int-ℕ s)) +ℤ
            (neg-ℤ one-ℤ))) (int-ℕ (succ-ℕ x)))
          by ap (λ H → ((((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ
              (H *ℤ (int-ℕ (succ-ℕ x)))))
              (inv (distributive-neg-add-ℤ
                ((int-ℕ q) *ℤ (int-ℕ s)) (neg-ℤ one-ℤ)))
        ＝ (((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ
          (neg-ℤ (mul-ℤ (((int-ℕ q) *ℤ (int-ℕ s)) +ℤ
            (neg-ℤ one-ℤ)) (int-ℕ (succ-ℕ x))))
          by ap ((((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ_)
            (left-negative-law-mul-ℤ
              (((int-ℕ q) *ℤ (int-ℕ s)) +ℤ (neg-ℤ one-ℤ))
              (int-ℕ (succ-ℕ x)))

    dist-eqn :
      r ＝
      dist-ℕ
        ( mul-ℕ
          ( abs-ℤ (((int-ℕ q) *ℤ (int-ℕ s)) +ℤ (neg-ℤ one-ℤ)))
          ( succ-ℕ x))
        ( (q *ℕ t) *ℕ y)
    dist-eqn =
      equational-reasoning
        r
        ＝ abs-ℤ (int-ℕ r) by (inv (abs-int-ℕ r))
        ＝ abs-ℤ ((((int-ℕ q) *ℤ (int-ℕ t)) *ℤ (int-ℕ y)) +ℤ
            (neg-ℤ ((((int-ℕ q) *ℤ (int-ℕ s)) +ℤ (neg-ℤ one-ℤ)) *ℤ
            (int-ℕ (succ-ℕ x)))))
          by (ap abs-ℤ (isolate-rem-eqn ∙ rearrange-arith))
        ＝ dist-ℤ ((int-ℕ (q *ℕ t)) *ℤ (int-ℕ y))
          ((((int-ℕ q) *ℤ (int-ℕ s)) +ℤ (neg-ℤ one-ℤ)) *ℤ
            (int-ℕ (succ-ℕ x)))
          by ap (λ H → (dist-ℤ (H *ℤ (int-ℕ y))
            ((((int-ℕ q) *ℤ (int-ℕ s)) +ℤ (neg-ℤ one-ℤ)) *ℤ
              (int-ℕ (succ-ℕ x)))))
              (mul-int-ℕ q t)
        ＝ dist-ℤ (int-ℕ ((q *ℕ t) *ℕ y))
          ((((int-ℕ q) *ℤ (int-ℕ s)) +ℤ (neg-ℤ one-ℤ)) *ℤ
          (int-ℕ (succ-ℕ x)))
          by
            ap
              ( λ H →
                dist-ℤ H
                  ( mul-ℤ
                    ( ((int-ℕ q) *ℤ (int-ℕ s)) +ℤ (neg-ℤ one-ℤ))
                    ( int-ℕ (succ-ℕ x))))
              ( mul-int-ℕ (q *ℕ t) y)
        ＝ dist-ℤ
            ( int-ℕ ((q *ℕ t) *ℕ y))
            ( mul-ℤ
              ( int-ℕ (abs-ℤ (((int-ℕ q) *ℤ (int-ℕ s)) +ℤ (neg-ℤ one-ℤ))))
              ( int-ℕ (succ-ℕ x)))
          by
            ap
              ( λ H →
                dist-ℤ
                  ( int-ℕ ((q *ℕ t) *ℕ y))
                  ( H *ℤ (int-ℕ (succ-ℕ x))))
              ( inv
                ( int-abs-is-nonnegative-ℤ
                  ( ((int-ℕ q) *ℤ (int-ℕ s)) +ℤ (neg-ℤ one-ℤ))
                  ( coeff-nonnegative)))
        ＝ dist-ℤ
            ( int-ℕ ((q *ℕ t) *ℕ y))
            ( int-ℕ
              ( mul-ℕ
                ( abs-ℤ (((int-ℕ q) *ℤ (int-ℕ s)) +ℤ (neg-ℤ one-ℤ)))
                ( succ-ℕ x)))
          by
            ap
              ( dist-ℤ (int-ℕ ((q *ℕ t) *ℕ y)))
              ( mul-int-ℕ
                ( abs-ℤ (((int-ℕ q) *ℤ (int-ℕ s)) +ℤ (neg-ℤ one-ℤ)))
                ( succ-ℕ x))
        ＝ dist-ℕ ((q *ℕ t) *ℕ y)
          ((abs-ℤ (((int-ℕ q) *ℤ (int-ℕ s)) +ℤ (neg-ℤ one-ℤ))) *ℕ
            (succ-ℕ x))
          by dist-int-ℕ
            ((q *ℕ t) *ℕ y)
            ((abs-ℤ (((int-ℕ q) *ℤ (int-ℕ s)) +ℤ (neg-ℤ one-ℤ))) *ℕ
              (succ-ℕ x))
        ＝ dist-ℕ
          ((abs-ℤ (((int-ℕ q) *ℤ (int-ℕ s)) +ℤ (neg-ℤ one-ℤ))) *ℕ
            (succ-ℕ x))
            ((q *ℕ t) *ℕ y)
          by symmetric-dist-ℕ
            ((q *ℕ t) *ℕ y)
            (mul-ℕ (abs-ℤ (add-ℤ (mul-ℤ (int-ℕ q)
              (int-ℕ s)) (neg-ℤ one-ℤ)))
            (succ-ℕ x))

remainder-min-dist-succ-x-is-not-nonzero :
  (x y : ℕ) →
  ¬ ( is-nonzero-ℕ
      ( remainder-euclidean-division-ℕ
        ( minimal-positive-distance (succ-ℕ x) y)
        ( succ-ℕ x)))
remainder-min-dist-succ-x-is-not-nonzero x y nonzero =
  contradiction-le-ℕ
    ( remainder-euclidean-division-ℕ
      ( minimal-positive-distance (succ-ℕ x) y)
      ( succ-ℕ x))
    ( minimal-positive-distance (succ-ℕ x) y)
    ( remainder-min-dist-succ-x-le-min-dist x y) d-leq-rem
  where
  rem-pos-dist :
    pos-distance-between-multiples
      ( succ-ℕ x)
      ( y)
      ( remainder-euclidean-division-ℕ
        ( minimal-positive-distance (succ-ℕ x) y)
        ( succ-ℕ x))
  rem-pos-dist H = pair' nonzero (remainder-min-dist-succ-x-is-distance x y)

  d-leq-rem :
    leq-ℕ
      ( minimal-positive-distance (succ-ℕ x) y)
      ( remainder-euclidean-division-ℕ
        ( minimal-positive-distance (succ-ℕ x) y)
        ( succ-ℕ x))
  d-leq-rem =
    minimal-positive-distance-is-minimal
      ( succ-ℕ x)
      ( y)
      ( remainder-euclidean-division-ℕ
        ( minimal-positive-distance (succ-ℕ x) y)
        ( succ-ℕ x))
      ( rem-pos-dist)

remainder-min-dist-succ-x-is-zero :
  (x y : ℕ) →
  is-zero-ℕ
    ( remainder-euclidean-division-ℕ
      ( minimal-positive-distance (succ-ℕ x) y)
      ( succ-ℕ x))
remainder-min-dist-succ-x-is-zero x y =
  is-zero-case-split
    ( is-decidable-is-zero-ℕ
      ( remainder-euclidean-division-ℕ
        ( minimal-positive-distance (succ-ℕ x) y)
        ( succ-ℕ x)))
  where
  is-zero-case-split :
    ( is-zero-ℕ
      ( remainder-euclidean-division-ℕ
        (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x)) +
      is-nonzero-ℕ
      ( remainder-euclidean-division-ℕ
        (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))) →
      is-zero-ℕ
        ( remainder-euclidean-division-ℕ
          (minimal-positive-distance (succ-ℕ x) y) (succ-ℕ x))
  is-zero-case-split (inl z) = z
  is-zero-case-split (inr nz) =
    ex-falso (remainder-min-dist-succ-x-is-not-nonzero x y nz)

minimal-positive-distance-div-fst :
  (x y : ℕ) → div-ℕ (minimal-positive-distance x y) x
minimal-positive-distance-div-fst zero-ℕ y =
  pair zero-ℕ (left-zero-law-mul-ℕ (minimal-positive-distance zero-ℕ y))
minimal-positive-distance-div-fst (succ-ℕ x) y =
  pair
    ( quotient-euclidean-division-ℕ
      ( minimal-positive-distance (succ-ℕ x) y)
      ( succ-ℕ x))
    ( eqn)
  where
  eqn :
    ( mul-ℕ
      ( quotient-euclidean-division-ℕ
        ( minimal-positive-distance (succ-ℕ x) y)
        ( succ-ℕ x))
      ( minimal-positive-distance (succ-ℕ x) y)) ＝
    ( succ-ℕ x)
  eqn =
    equational-reasoning
      mul-ℕ
        ( quotient-euclidean-division-ℕ
          ( minimal-positive-distance (succ-ℕ x) y)
          ( succ-ℕ x))
        ( minimal-positive-distance (succ-ℕ x) y)
      ＝ add-ℕ
          ( mul-ℕ
            ( quotient-euclidean-division-ℕ
              ( minimal-positive-distance (succ-ℕ x) y)
              ( succ-ℕ x))
            ( minimal-positive-distance (succ-ℕ x) y))
          ( zero-ℕ)
        by
          ( inv
            ( right-unit-law-add-ℕ
              ( ( quotient-euclidean-division-ℕ
                  ( minimal-positive-distance (succ-ℕ x) y)
                  ( succ-ℕ x)) *ℕ
                ( minimal-positive-distance (succ-ℕ x) y))))
      ＝ add-ℕ
        ( ( quotient-euclidean-division-ℕ
            ( minimal-positive-distance (succ-ℕ x) y)
            ( succ-ℕ x)) *ℕ
          ( minimal-positive-distance (succ-ℕ x) y))
        ( remainder-euclidean-division-ℕ
          ( minimal-positive-distance (succ-ℕ x) y)
          ( succ-ℕ x))
        by
          ( ap
            ( add-ℕ
              ( mul-ℕ
                ( quotient-euclidean-division-ℕ
                  ( minimal-positive-distance (succ-ℕ x) y)
                  ( succ-ℕ x))
                ( minimal-positive-distance (succ-ℕ x) y)))
            ( inv (remainder-min-dist-succ-x-is-zero x y)))
      ＝ succ-ℕ x
        by
          eq-euclidean-division-ℕ
            ( minimal-positive-distance (succ-ℕ x) y)
            ( succ-ℕ x)

minimal-positive-distance-div-snd :
  (x y : ℕ) → div-ℕ (minimal-positive-distance x y) y
minimal-positive-distance-div-snd x y =
  concatenate-eq-div-ℕ
    ( minimal-positive-distance-sym x y)
    ( minimal-positive-distance-div-fst y x)

minimal-positive-distance-div-gcd-ℕ :
  (x y : ℕ) → div-ℕ (minimal-positive-distance x y) (gcd-ℕ x y)
minimal-positive-distance-div-gcd-ℕ x y =
  div-gcd-is-common-divisor-ℕ
    ( x)
    ( y)
    ( minimal-positive-distance x y)
    ( pair'
      ( minimal-positive-distance-div-fst x y)
      ( minimal-positive-distance-div-snd x y))

gcd-ℕ-div-x-mults :
  (x y z : ℕ)
  (d : is-distance-between-multiples-ℕ x y z) →
  div-ℕ (gcd-ℕ x y) ((is-distance-between-multiples-fst-coeff-ℕ d) *ℕ x)
gcd-ℕ-div-x-mults x y z d =
  div-mul-ℕ
    ( is-distance-between-multiples-fst-coeff-ℕ d)
    ( gcd-ℕ x y)
    ( x)
    ( pr1 (is-common-divisor-gcd-ℕ x y))

gcd-ℕ-div-y-mults :
  (x y z : ℕ)
  (d : is-distance-between-multiples-ℕ x y z) →
  div-ℕ (gcd-ℕ x y) ((is-distance-between-multiples-snd-coeff-ℕ d) *ℕ y)
gcd-ℕ-div-y-mults x y z d =
  div-mul-ℕ
    ( is-distance-between-multiples-snd-coeff-ℕ d)
    ( gcd-ℕ x y)
    ( y)
    ( pr2 (is-common-divisor-gcd-ℕ x y))

gcd-ℕ-div-dist-between-mult :
  (x y z : ℕ) → is-distance-between-multiples-ℕ x y z → div-ℕ (gcd-ℕ x y) z
gcd-ℕ-div-dist-between-mult x y z dist =
  sx-ty-case-split (linear-leq-ℕ (s *ℕ x) (t *ℕ y))
  where
  s : ℕ
  s = is-distance-between-multiples-fst-coeff-ℕ dist
  t : ℕ
  t = is-distance-between-multiples-snd-coeff-ℕ dist

  sx-ty-case-split :
    (leq-ℕ (s *ℕ x) (t *ℕ y) + leq-ℕ (t *ℕ y) (s *ℕ x)) →
    div-ℕ (gcd-ℕ x y) z
  sx-ty-case-split (inl sxty) =
    div-right-summand-ℕ (gcd-ℕ x y) (s *ℕ x) z
      (gcd-ℕ-div-x-mults x y z dist)
      (concatenate-div-eq-ℕ (gcd-ℕ-div-y-mults x y z dist)
        (inv rewrite-dist))
    where
    rewrite-dist : (s *ℕ x) +ℕ z ＝ t *ℕ y
    rewrite-dist = rewrite-right-dist-add-ℕ
      (s *ℕ x) z (t *ℕ y) sxty
      (inv (is-distance-between-multiples-eqn-ℕ dist))

  sx-ty-case-split (inr tysx) =
    div-right-summand-ℕ (gcd-ℕ x y) (t *ℕ y) z
      (gcd-ℕ-div-y-mults x y z dist)
      (concatenate-div-eq-ℕ (gcd-ℕ-div-x-mults x y z dist) (inv rewrite-dist))
    where
    rewrite-dist : (t *ℕ y) +ℕ z ＝ s *ℕ x
    rewrite-dist =
      rewrite-right-dist-add-ℕ (t *ℕ y) z (s *ℕ x) tysx
        ( inv (is-distance-between-multiples-eqn-ℕ dist) ∙
          symmetric-dist-ℕ (s *ℕ x) (t *ℕ y))

    div-gcd-x : div-ℕ (gcd-ℕ x y) (s *ℕ x)
    div-gcd-x = div-mul-ℕ s (gcd-ℕ x y) x (pr1 (is-common-divisor-gcd-ℕ x y))

gcd-ℕ-div-minimal-positive-distance :
  (x y : ℕ) → is-nonzero-ℕ (x +ℕ y) →
  div-ℕ (gcd-ℕ x y) (minimal-positive-distance x y)
gcd-ℕ-div-minimal-positive-distance x y H =
  gcd-ℕ-div-dist-between-mult
    ( x)
    ( y)
    ( minimal-positive-distance x y)
    ( minimal-positive-distance-is-distance x y H)

bezouts-lemma-ℕ :
  (x y : ℕ) → is-nonzero-ℕ (x +ℕ y) →
  minimal-positive-distance x y ＝ gcd-ℕ x y
bezouts-lemma-ℕ x y H =
  antisymmetric-div-ℕ
    ( minimal-positive-distance x y)
    ( gcd-ℕ x y)
    ( minimal-positive-distance-div-gcd-ℕ x y)
    ( gcd-ℕ-div-minimal-positive-distance x y H)

bezouts-lemma-eqn-ℕ :
  (x y : ℕ)
  (H : is-nonzero-ℕ (x +ℕ y)) →
  dist-ℕ
    ( (minimal-positive-distance-x-coeff x y H) *ℕ x)
    ( (minimal-positive-distance-y-coeff x y H) *ℕ y) ＝
  gcd-ℕ x y
bezouts-lemma-eqn-ℕ x y H =
  minimal-positive-distance-eqn x y H ∙ bezouts-lemma-ℕ x y H
```

## References

{{#bibliography}}
