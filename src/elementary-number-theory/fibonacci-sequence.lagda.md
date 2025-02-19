# The Fibonacci sequence

```agda
module elementary-number-theory.fibonacci-sequence where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.divisibility-natural-numbers
open import elementary-number-theory.greatest-common-divisor-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.relatively-prime-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers
open import elementary-number-theory.squares-natural-numbers
open import elementary-number-theory.sums-of-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.unit-type
```

</details>

## Idea

The
{{#concept "Fibonacci sequence" WD="Fibonacci sequence" WDID=Q23835349 Agda=fibonacci-ℕ OEIS=A000045}}
is a recursively defined [sequence](foundation.sequences.md) of
[natural numbers](elementary-number-theory.natural-numbers.md) given by the
equations

```text
  Fₙ₊₂ = Fₙ₊₁ + Fₙ,   where F₀ = 0 and F₁ = 1
```

A number in this sequence is called a
{{#concept "Fibonacci number" WD="Fibonacci number" WDID=Q47577}}. The first few
Fibonacci numbers are

```text
  n    0   1   2   3   4   5   6   7   8   9
  Fₙ   0   1   1   2   3   5   8  13  21  34
```

The Fibonacci sequence was introduced by
[Leonardo Fibonacci](https://en.wikipedia.org/wiki/Fibonacci) in 1202 in his
book _Liber Abaci_ {{#cite Fibonacci1202}}.

## Definitions

### The Fibonacci sequence

```agda
fibonacci-ℕ : ℕ → ℕ
fibonacci-ℕ 0 = 0
fibonacci-ℕ (succ-ℕ 0) = 1
fibonacci-ℕ (succ-ℕ (succ-ℕ n)) = fibonacci-ℕ (succ-ℕ n) +ℕ fibonacci-ℕ n
```

### The Fibonacci sequence in the integers

```agda
fibonacci-ℤ : ℕ → ℤ
fibonacci-ℤ = int-ℕ ∘ fibonacci-ℕ
```

### The Fibonacci sequence defined directly with the induction principle of `ℕ`

The above definition of the Fibonacci sequence uses Agda's powerful pattern
matching definitions. Below, we will give a definition of the Fibonacci sequence
in terms of `ind-ℕ`.

The problem with defining the Fibonacci sequence using `ind-ℕ`, is that `ind-ℕ`
doesn't give us a way to refer to both `(F n)` and `(F (succ-ℕ n))`. So, we have
to give a workaround, where we store two values in the Fibonacci sequence at
once.

The basic idea is that we define a sequence of pairs of integers, which will be
consecutive Fibonacci numbers. This would be a function of type $ℕ → ℕ²$.

Such a function is easy to give with induction, using the map $ℕ² → ℕ²$ that
takes a pair `(m,n)` to the pair `(n,n+m)`. Starting the iteration with `(0,1)`
we obtain the Fibonacci sequence by taking the first projection.

Furthermore, it is possible to define the fibonacci sequence without using
cartesian products, mimicing the above idea using $\mathbb{N} \to \matbb{N}$
instead of $\mathbb{N}^2$.

```agda
shift-one :
  ℕ → (ℕ → ℕ) → (ℕ → ℕ)
shift-one n f =
  ind-ℕ n (λ x y → f x)

shift-two :
  ℕ → ℕ → (ℕ → ℕ) → (ℕ → ℕ)
shift-two m n f =
  shift-one m (shift-one n f)

fibo-zero-ℕ :
  ℕ → ℕ
fibo-zero-ℕ =
  shift-two 0 1 (λ x → 0)

fibo-succ-ℕ :
  (ℕ → ℕ) → (ℕ → ℕ)
fibo-succ-ℕ f =
  shift-two (f 1) ((f 1) +ℕ (f 0)) (λ x → 0)

fibo-function :
  ℕ → ℕ → ℕ
fibo-function =
  ind-ℕ
    ( fibo-zero-ℕ)
    ( λ n → fibo-succ-ℕ)

fibo-ℕ :
  ℕ → ℕ
fibo-ℕ k =
  fibo-function k 0
```

## Properties

### `F(m+n+1) ＝ F(m+1)F(n+1) + F(m)F(n)`

```agda
fibonacci-add-ℕ :
  (m n : ℕ) →
  fibonacci-ℕ (m +ℕ succ-ℕ n) ＝
  fibonacci-ℕ (succ-ℕ m) *ℕ fibonacci-ℕ (succ-ℕ n) +ℕ
  fibonacci-ℕ m *ℕ fibonacci-ℕ n
fibonacci-add-ℕ m zero-ℕ =
  ap-add-ℕ
    ( inv (right-unit-law-mul-ℕ (fibonacci-ℕ (succ-ℕ m))))
    ( inv (right-zero-law-mul-ℕ (fibonacci-ℕ m)))
fibonacci-add-ℕ m (succ-ℕ n) =
  ( ap fibonacci-ℕ (inv (left-successor-law-add-ℕ m (succ-ℕ n)))) ∙
  ( fibonacci-add-ℕ (succ-ℕ m) n) ∙
  ( ap
    ( _+ℕ fibonacci-ℕ (succ-ℕ m) *ℕ fibonacci-ℕ n)
    ( right-distributive-mul-add-ℕ
      ( fibonacci-ℕ (succ-ℕ m))
      ( fibonacci-ℕ m)
      ( fibonacci-ℕ (succ-ℕ n)))) ∙
  ( associative-add-ℕ
    ( fibonacci-ℕ (succ-ℕ m) *ℕ fibonacci-ℕ (succ-ℕ n))
    ( fibonacci-ℕ m *ℕ fibonacci-ℕ (succ-ℕ n))
    ( fibonacci-ℕ (succ-ℕ m) *ℕ fibonacci-ℕ n)) ∙
  ( ap
    ( fibonacci-ℕ (succ-ℕ m) *ℕ fibonacci-ℕ (succ-ℕ n) +ℕ_)
    ( commutative-add-ℕ
      ( fibonacci-ℕ m *ℕ fibonacci-ℕ (succ-ℕ n))
      ( fibonacci-ℕ (succ-ℕ m) *ℕ fibonacci-ℕ n))) ∙
  ( inv
    ( associative-add-ℕ
      ( fibonacci-ℕ (succ-ℕ m) *ℕ fibonacci-ℕ (succ-ℕ n))
      ( fibonacci-ℕ (succ-ℕ m) *ℕ fibonacci-ℕ n)
      ( fibonacci-ℕ m *ℕ fibonacci-ℕ (succ-ℕ n)))) ∙
  ( ap
    ( _+ℕ fibonacci-ℕ m *ℕ fibonacci-ℕ (succ-ℕ n))
    ( inv
      ( left-distributive-mul-add-ℕ
        ( fibonacci-ℕ (succ-ℕ m))
        ( fibonacci-ℕ (succ-ℕ n))
        ( fibonacci-ℕ n))))
```

### Consecutive Fibonacci numbers are relatively prime

```agda
is-one-div-fibonacci-succ-div-fibonacci-ℕ :
  (d n : ℕ) → div-ℕ d (fibonacci-ℕ n) → div-ℕ d (fibonacci-ℕ (succ-ℕ n)) →
  is-one-ℕ d
is-one-div-fibonacci-succ-div-fibonacci-ℕ d zero-ℕ H K =
  is-one-div-one-ℕ d K
is-one-div-fibonacci-succ-div-fibonacci-ℕ d (succ-ℕ n) H K =
  is-one-div-fibonacci-succ-div-fibonacci-ℕ d n
    ( div-right-summand-ℕ d (fibonacci-ℕ (succ-ℕ n)) (fibonacci-ℕ n) H K)
    ( H)

relatively-prime-fibonacci-fibonacci-succ-ℕ :
  (n : ℕ) → is-relatively-prime-ℕ (fibonacci-ℕ n) (fibonacci-ℕ (succ-ℕ n))
relatively-prime-fibonacci-fibonacci-succ-ℕ n =
  is-one-div-fibonacci-succ-div-fibonacci-ℕ
    ( gcd-ℕ (fibonacci-ℕ n) (fibonacci-ℕ (succ-ℕ n)))
    ( n)
    ( div-left-factor-gcd-ℕ (fibonacci-ℕ n) (fibonacci-ℕ (succ-ℕ n)))
    ( div-right-factor-gcd-ℕ (fibonacci-ℕ n) (fibonacci-ℕ (succ-ℕ n)))
```

### A 3-for-2 property of divisibility of Fibonacci numbers

We prove that if an two of the following three properties hold, then so does the
third:

1. `d | fibonacci-ℕ m`
2. `d | fibonacci-ℕ n`
3. `d | fibonacci-ℕ (m +ℕ n)`.

```agda
div-fibonacci-add-ℕ :
  (d m n : ℕ) → div-ℕ d (fibonacci-ℕ m) → div-ℕ d (fibonacci-ℕ n) →
  div-ℕ d (fibonacci-ℕ (m +ℕ n))
div-fibonacci-add-ℕ d m zero-ℕ H1 H2 =
  H1
div-fibonacci-add-ℕ d m (succ-ℕ n) H1 H2 =
  tr
    ( div-ℕ d)
    ( inv (fibonacci-add-ℕ m n))
    ( div-add-ℕ d
      ( fibonacci-ℕ (succ-ℕ m) *ℕ fibonacci-ℕ (succ-ℕ n))
      ( fibonacci-ℕ m *ℕ fibonacci-ℕ n)
      ( div-mul-ℕ (fibonacci-ℕ (succ-ℕ m)) d (fibonacci-ℕ (succ-ℕ n)) H2)
      ( tr
        ( div-ℕ d)
        ( commutative-mul-ℕ (fibonacci-ℕ n) (fibonacci-ℕ m))
        ( div-mul-ℕ (fibonacci-ℕ n) d (fibonacci-ℕ m) H1)))
```

### If `m | n`, then `d | F(m)` implies `d | F(n)`

```agda
div-fibonacci-div-ℕ :
  (d m n : ℕ) → div-ℕ m n → div-ℕ d (fibonacci-ℕ m) → div-ℕ d (fibonacci-ℕ n)
div-fibonacci-div-ℕ d m .zero-ℕ (zero-ℕ , refl) H =
  div-zero-ℕ d
div-fibonacci-div-ℕ d zero-ℕ .(k *ℕ zero-ℕ) (succ-ℕ k , refl) H =
  tr
    ( div-ℕ d)
    ( ap fibonacci-ℕ (inv (right-zero-law-mul-ℕ (succ-ℕ k))))
    ( div-zero-ℕ d)
div-fibonacci-div-ℕ d (succ-ℕ m) ._ (succ-ℕ k , refl) H =
  div-fibonacci-add-ℕ d
    ( k *ℕ succ-ℕ m)
    ( succ-ℕ m)
    ( div-fibonacci-div-ℕ d (succ-ℕ m) (k *ℕ succ-ℕ m) (k , refl) H)
    ( H)
```

### The function `fibonacci-ℕ` is an order preserving map on the natural numbers ordered by divisibility

```agda
preserves-div-fibonacci-ℕ :
  (m n : ℕ) → div-ℕ m n → div-ℕ (fibonacci-ℕ m) (fibonacci-ℕ n)
preserves-div-fibonacci-ℕ m n H =
  div-fibonacci-div-ℕ (fibonacci-ℕ m) m n H (refl-div-ℕ (fibonacci-ℕ m))
```

### The sum of the first $n + 1$ Fibonacci numbers

We show that

$$
  \sum_{k=0}^n F_k = F_{n+2}-1
$$

```agda
sum-of-fibonacci-ℕ :
  ℕ → ℕ
sum-of-fibonacci-ℕ n =
  bounded-sum-ℕ n (λ k _ → fibonacci-ℕ k)

compute-sum-of-fibonacci-ℕ' :
  (n : ℕ) → succ-ℕ (sum-of-fibonacci-ℕ n) ＝ fibonacci-ℕ (n +ℕ 2)
compute-sum-of-fibonacci-ℕ' zero-ℕ =
  refl
compute-sum-of-fibonacci-ℕ' (succ-ℕ n) =
  ( inv
    ( left-successor-law-add-ℕ
      ( bounded-sum-ℕ n (λ k _ → fibonacci-ℕ k))
      ( fibonacci-ℕ (succ-ℕ n)))) ∙
  ( ap (_+ℕ fibonacci-ℕ (succ-ℕ n)) (compute-sum-of-fibonacci-ℕ' n))

compute-sum-of-fibonacci-ℕ :
  (n : ℕ) → sum-of-fibonacci-ℕ n ＝ dist-ℕ (fibonacci-ℕ (n +ℕ 2)) 1
compute-sum-of-fibonacci-ℕ n =
  ( rewrite-left-add-dist-ℕ
    ( bounded-sum-ℕ n (λ k _ → fibonacci-ℕ k))
    ( 1)
    ( fibonacci-ℕ (n +ℕ 2))
    ( compute-sum-of-fibonacci-ℕ' n)) ∙
  ( symmetric-dist-ℕ 1 (fibonacci-ℕ (n +ℕ 2)))

le-sum-of-fibonacci-ℕ :
  (n : ℕ) → sum-of-fibonacci-ℕ n <-ℕ fibonacci-ℕ (n +ℕ 2)
le-sum-of-fibonacci-ℕ n =
  concatenate-le-eq-ℕ
    ( sum-of-fibonacci-ℕ n)
    ( succ-ℕ (sum-of-fibonacci-ℕ n))
    ( fibonacci-ℕ (n +ℕ 2))
    ( succ-le-ℕ (sum-of-fibonacci-ℕ n))
    ( compute-sum-of-fibonacci-ℕ' n)
```

### The sum of the first $n$ oddly indexed Fibonacci numbers

We show that

$$
  \sum_{k=0}^{n-1} F_{2k+1} = F_{2n}.
$$

```agda
strictly-bounded-sum-fibonacci-odd-number-ℕ :
  ℕ → ℕ
strictly-bounded-sum-fibonacci-odd-number-ℕ n =
  strictly-bounded-sum-ℕ n (λ k _ → fibonacci-ℕ (odd-number-ℕ k))

compute-strictly-bounded-sum-fibonacci-odd-number-ℕ :
  (n : ℕ) →
  strictly-bounded-sum-fibonacci-odd-number-ℕ n ＝ fibonacci-ℕ (2 *ℕ n)
compute-strictly-bounded-sum-fibonacci-odd-number-ℕ zero-ℕ =
  refl
compute-strictly-bounded-sum-fibonacci-odd-number-ℕ (succ-ℕ n) =
  ( ap
    ( _+ℕ fibonacci-ℕ (odd-number-ℕ n))
    ( compute-strictly-bounded-sum-fibonacci-odd-number-ℕ n)) ∙
  ( commutative-add-ℕ
    ( fibonacci-ℕ (2 *ℕ n))
    ( fibonacci-ℕ (odd-number-ℕ n))) ∙
  ( inv (ap fibonacci-ℕ (left-distributive-mul-add-ℕ 2 n 1)))
```

### The sum of the first $n + 1$ evenly indexed Fibonacci numbers

We show that

$$
  \sum_{k=0}^{n} F_{2k} = F_{2n+1} - 1.
$$

```agda
bounded-sum-fibonacci-even-ℕ :
  ℕ → ℕ
bounded-sum-fibonacci-even-ℕ n =
  bounded-sum-ℕ n (λ k _ → fibonacci-ℕ (even-number-ℕ k))

compute-bounded-sum-fibonacci-even-ℕ' :
  (n : ℕ) →
  succ-ℕ (bounded-sum-fibonacci-even-ℕ n) ＝ fibonacci-ℕ (odd-number-ℕ n)
compute-bounded-sum-fibonacci-even-ℕ' zero-ℕ =
  refl
compute-bounded-sum-fibonacci-even-ℕ' (succ-ℕ n) =
  ( right-swap-add-ℕ
    ( bounded-sum-fibonacci-even-ℕ n)
    ( fibonacci-ℕ (even-number-ℕ (succ-ℕ n)))
    ( 1)) ∙
  ( ap-add-ℕ
    ( compute-bounded-sum-fibonacci-even-ℕ' n)
    ( ap fibonacci-ℕ (even-number-succ-ℕ n))) ∙
  ( commutative-add-ℕ
    ( fibonacci-ℕ (odd-number-ℕ n))
    ( fibonacci-ℕ (succ-ℕ (odd-number-ℕ n)))) ∙
  ( inv (ap fibonacci-ℕ (odd-number-succ-ℕ n)))

compute-bounded-sum-fibonacci-even-ℕ :
  (n : ℕ) →
  bounded-sum-fibonacci-even-ℕ n ＝ dist-ℕ (fibonacci-ℕ (odd-number-ℕ n)) 1
compute-bounded-sum-fibonacci-even-ℕ n =
  ( rewrite-left-add-dist-ℕ
    ( bounded-sum-fibonacci-even-ℕ n)
    ( 1)
    ( fibonacci-ℕ (odd-number-ℕ n))
    ( compute-bounded-sum-fibonacci-even-ℕ' n)) ∙
  ( symmetric-dist-ℕ 1 (fibonacci-ℕ (odd-number-ℕ n)))

le-bounded-sum-fibonacci-even-ℕ :
  (n : ℕ) → bounded-sum-fibonacci-even-ℕ n <-ℕ fibonacci-ℕ (odd-number-ℕ n)
le-bounded-sum-fibonacci-even-ℕ n =
  concatenate-le-eq-ℕ
    ( bounded-sum-fibonacci-even-ℕ n)
    ( succ-ℕ (bounded-sum-fibonacci-even-ℕ n))
    ( fibonacci-ℕ (odd-number-ℕ n))
    ( succ-le-ℕ (bounded-sum-fibonacci-even-ℕ n))
    ( compute-bounded-sum-fibonacci-even-ℕ' n)
```

### A strict bound on the growth of the Fibonacci numbers

The $n$th Fibonacci number is always strictly less than $\phi^n$, where $\phi$
is the golden ratio. This strict inequality is due to Édouard Lucas, who proved
it in the late 19th century {{#cite lucas1891}}. We will prove a rational
version of this claim by showing that $F_n<(\frac{b}{a})^n$ for any rational
number $\frac{b}{a}>\phi$

A variation of this claim also appears on pages 7 and 8 in section 1.2 of
{{#cite Leveque12volI}} as an instructive example of a proof by induction, where
he shows that $F_n<(\frac{7}{4})^n$. This upper bound works for any fraction
$\frac{b}{a}$ where $a(b+a)<b^2$, i.e., any fraction that is larger than the
golden ratio. Another close estimate is

$$
  F_n < \left(\frac{13}{8}\right)^n,
$$

because $13^2-8\cdot 21=169-168=1$ by Cassini's identity. More generally, for
any $n$ the ratio $F_{2n+1}/F_{2n}$ is greater than the golden ratio, because
$F_{2n+1}^2-F_{2n}F_{2n+2}=1$. Therefore it follows that

$$
 F_k < \left(\frac{F_{2n+1}}{F_{2n}}\right)^k
$$

As a corollary, we obtain that $F_{2n}^n F_n < F_{2n+1}^n$ for all $n$, which in
fact are terms in ratios that converge to $\sqrt{5}$, and that
$F_{2n}^{2n+1}<F_{2n+1}^{2n}$.

**Proof.** Suppose that $a(b + a) < b^2$. We will show by induction that
$a^n F(n) < b^n$. In the base case $n=0$ the claim reduces to the strict
inequality $0 < 1$, which is true. In the base case $n=1$ we have to show that
$a\cdot F(1) = a < b$. To see this, note recall that squaring reflects the
strict ordering of the natural numbers (this means that $x^2<y^2$ implies
$x<y$), and we have $a^2\leq a(b+a)<b^2$. For the inductive step, assume that
$a^n F(n) < b^n$ and that $a^{n+1} F(n+1) < b^{n+1}$. Then we have

$$
  a^{n+2} F(n+2) = a^{n+2} F(n+1) + a^{n+2} F(n) < a\cdot b^{n+1} + a^2\cdot b^n = (a\cdot(b+a))\cdot b^n < b^{n+2}.
$$

```agda
lucas-strict-exponential-bound-fibonacci-ℕ :
  (n a b : ℕ) → a *ℕ (b +ℕ a) <-ℕ b ^ℕ 2 →
  exp-ℕ a n *ℕ fibonacci-ℕ n <-ℕ exp-ℕ b n
lucas-strict-exponential-bound-fibonacci-ℕ zero-ℕ a b H = star
lucas-strict-exponential-bound-fibonacci-ℕ (succ-ℕ zero-ℕ) a b H =
  concatenate-eq-le-ℕ
    ( exp-ℕ a 1 *ℕ 1)
    ( a)
    ( exp-ℕ b 1)
    ( right-unit-law-mul-ℕ (exp-ℕ a 1))
    ( reflects-strict-order-square-ℕ a b
      ( concatenate-leq-le-ℕ
        ( a ^ℕ 2)
        ( a *ℕ (b +ℕ a))
        ( b ^ℕ 2)
        ( preserves-order-right-mul-ℕ a a (b +ℕ a) (leq-add-ℕ' a b))
        ( H)))
lucas-strict-exponential-bound-fibonacci-ℕ (succ-ℕ (succ-ℕ n)) zero-ℕ b H =
  concatenate-eq-le-ℕ
    ( exp-ℕ 0 (n +ℕ 2) *ℕ fibonacci-ℕ (n +ℕ 2))
    ( 0)
    ( exp-ℕ b (n +ℕ 2))
    ( ( right-swap-mul-ℕ (exp-ℕ 0 (n +ℕ 1)) 0 (fibonacci-ℕ (n +ℕ 2))) ∙
      ( right-zero-law-mul-ℕ (exp-ℕ 0 (n +ℕ 1) *ℕ fibonacci-ℕ (n +ℕ 2))))
    ( le-zero-exp-ℕ b
      ( n +ℕ 2)
      ( reflects-strict-order-square-ℕ 0 b
        ( le-zero-le-ℕ (0 *ℕ (b +ℕ 0)) (b ^ℕ 2) H)))
lucas-strict-exponential-bound-fibonacci-ℕ
  ( succ-ℕ (succ-ℕ n))
  ( succ-ℕ a)
  ( b)
  ( H) =
  concatenate-eq-le-ℕ
    ( exp-ℕ (succ-ℕ a) (n +ℕ 2) *ℕ fibonacci-ℕ (n +ℕ 2))
    ( succ-ℕ a *ℕ (exp-ℕ (succ-ℕ a) (n +ℕ 1) *ℕ fibonacci-ℕ (n +ℕ 1)) +ℕ
      succ-ℕ a ^ℕ 2 *ℕ (exp-ℕ (succ-ℕ a) n *ℕ fibonacci-ℕ n))
    ( exp-ℕ b (n +ℕ 2))
    ( ( left-distributive-mul-add-ℕ
        ( exp-ℕ (succ-ℕ a) (n +ℕ 2))
        ( fibonacci-ℕ (succ-ℕ n))
        ( fibonacci-ℕ n)) ∙
      ( ap-add-ℕ
        ( ( ap
            ( _*ℕ fibonacci-ℕ (succ-ℕ n))
            ( commutative-mul-ℕ (exp-ℕ (succ-ℕ a) (n +ℕ 1)) (succ-ℕ a))) ∙
          ( associative-mul-ℕ
            ( succ-ℕ a)
            ( exp-ℕ (succ-ℕ a) (n +ℕ 1))
            ( fibonacci-ℕ (succ-ℕ n))))
        ( ( ap
            ( _*ℕ fibonacci-ℕ n)
            ( ( left-distributive-exp-add-ℕ n 2) ∙
              ( commutative-mul-ℕ
                ( exp-ℕ (succ-ℕ a) n)
                ( succ-ℕ a ^ℕ 2)))) ∙
          ( associative-mul-ℕ
            ( succ-ℕ a ^ℕ 2)
            ( exp-ℕ (succ-ℕ a) n)
            ( fibonacci-ℕ n)))))
    ( concatenate-le-eq-le-ℕ
      ( succ-ℕ a *ℕ (exp-ℕ (succ-ℕ a) (n +ℕ 1) *ℕ fibonacci-ℕ (succ-ℕ n)) +ℕ
        succ-ℕ a ^ℕ 2 *ℕ (exp-ℕ (succ-ℕ a) n *ℕ fibonacci-ℕ n))
      ( succ-ℕ a *ℕ exp-ℕ b (succ-ℕ n) +ℕ succ-ℕ a ^ℕ 2 *ℕ exp-ℕ b n)
      ( (succ-ℕ a *ℕ (b +ℕ succ-ℕ a)) *ℕ exp-ℕ b n)
      ( exp-ℕ b (n +ℕ 2))
      ( preserves-strict-order-add-ℕ
        ( succ-ℕ a *ℕ (exp-ℕ (succ-ℕ a) (n +ℕ 1) *ℕ fibonacci-ℕ (succ-ℕ n)))
        ( succ-ℕ a *ℕ exp-ℕ b (succ-ℕ n))
        ( succ-ℕ a ^ℕ 2 *ℕ (exp-ℕ (succ-ℕ a) n *ℕ fibonacci-ℕ n))
        ( succ-ℕ a ^ℕ 2 *ℕ exp-ℕ b n)
        ( preserves-strict-order-left-mul-ℕ
          ( succ-ℕ a)
          ( exp-ℕ (succ-ℕ a) (n +ℕ 1) *ℕ fibonacci-ℕ (succ-ℕ n))
          ( exp-ℕ b (succ-ℕ n))
          ( is-nonzero-succ-ℕ a)
          ( lucas-strict-exponential-bound-fibonacci-ℕ
            ( succ-ℕ n)
            ( succ-ℕ a)
            ( b)
            ( H)))
        ( preserves-strict-order-left-mul-ℕ (succ-ℕ a ^ℕ 2)
          ( exp-ℕ (succ-ℕ a) n *ℕ fibonacci-ℕ n)
          ( exp-ℕ b n)
          ( is-nonzero-square-is-nonzero-ℕ (succ-ℕ a) (is-nonzero-succ-ℕ a))
          ( lucas-strict-exponential-bound-fibonacci-ℕ n (succ-ℕ a) b H)))
      ( ( ap
          ( _+ℕ succ-ℕ a ^ℕ 2 *ℕ (b ^ℕ n))
          ( ap (succ-ℕ a *ℕ_) (exp-succ-ℕ b n))) ∙
        ( ap
          ( _+ℕ succ-ℕ a ^ℕ 2 *ℕ exp-ℕ b n)
          ( ap (succ-ℕ a *ℕ_) (commutative-mul-ℕ (exp-ℕ b n) b) ∙
            inv (associative-mul-ℕ (succ-ℕ a) b (exp-ℕ b n)))) ∙
        ( inv
          ( right-distributive-mul-add-ℕ
            ( succ-ℕ a *ℕ b)
            ( succ-ℕ a ^ℕ 2)
            ( exp-ℕ b n))) ∙
        ( ap
          ( _*ℕ exp-ℕ b n)
          ( inv (left-distributive-mul-add-ℕ (succ-ℕ a) b (succ-ℕ a)))))
      ( concatenate-le-eq-ℕ
        ( (succ-ℕ a *ℕ (b +ℕ succ-ℕ a)) *ℕ exp-ℕ b n)
        ( b ^ℕ 2 *ℕ exp-ℕ b n)
        ( exp-ℕ b (n +ℕ 2))
        ( preserves-strict-order-right-mul-ℕ
          ( exp-ℕ b n)
          ( succ-ℕ a *ℕ (b +ℕ succ-ℕ a))
          ( b ^ℕ 2)
          ( is-nonzero-exp-ℕ b n
            ( is-nonzero-le-ℕ 0 b
              ( reflects-strict-order-square-ℕ 0 b
                ( le-zero-le-ℕ (succ-ℕ a *ℕ (b +ℕ succ-ℕ a)) (b ^ℕ 2) H))))
          ( H))
        ( ( commutative-mul-ℕ (b ^ℕ 2) (b ^ℕ n)) ∙
          ( inv (left-distributive-exp-add-ℕ n 2)))))

instance-7/4-lucas-strict-exponential-bound-fibonacci-ℕ :
  (n : ℕ) → exp-ℕ 4 n *ℕ fibonacci-ℕ n <-ℕ exp-ℕ 7 n
instance-7/4-lucas-strict-exponential-bound-fibonacci-ℕ n =
  lucas-strict-exponential-bound-fibonacci-ℕ n 4 7 star
```

## External links

- [Fibonacci sequence](https://en.wikipedia.org/wiki/Fibonacci_sequence) at
  Wikipedia
- [A000045](https://oeis.org/A000045) in the OEIS

## References

{{#bibliography}}
