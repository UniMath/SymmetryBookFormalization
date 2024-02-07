# The type checking monad

```agda
{-# OPTIONS --no-exact-split #-}

module reflection.type-checking-monad where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import lists.lists

open import primitives.strings

open import reflection.arguments
open import reflection.definitions
open import reflection.metavariables
open import reflection.names
open import reflection.terms
```

</details>

## Idea

The type-checking monad `TC` allows us to interact directly with Agda's type
checking mechanism. Additionally to primitives (see below), Agda includes the
the keyword `unquote` to manually unquote an element from `TC unit`.

## Definition

```agda
data ErrorPart : UU lzero where
  strErr : String → ErrorPart
  termErr : Term-Agda → ErrorPart
  pattErr : Pattern-Agda → ErrorPart
  nameErr : Name-Agda → ErrorPart

postulate
  -- The type checking monad
  TC : ∀ {a} → UU a → UU a
  returnTC : ∀ {a} {A : UU a} → A → TC A
  bindTC : ∀ {a b} {A : UU a} {B : UU b} → TC A → (A → TC B) → TC B
  -- Tries the unify the first term with the second
  unify : Term-Agda → Term-Agda → TC unit
  -- Gives an error
  typeError : ∀ {a} {A : UU a} → list ErrorPart → TC A
  -- Infers the type of a goal
  inferType : Term-Agda → TC Term-Agda
  checkType : Term-Agda → Term-Agda → TC Term-Agda
  normalise : Term-Agda → TC Term-Agda
  reduce : Term-Agda → TC Term-Agda
  -- Tries the first computation, if it fails tries the second
  catchTC : ∀ {a} {A : UU a} → TC A → TC A → TC A
  quoteTC : ∀ {a} {A : UU a} → A → TC Term-Agda
  unquoteTC : ∀ {a} {A : UU a} → Term-Agda → TC A
  quoteωTC : ∀ {A : UUω} → A → TC Term-Agda
  getContext : TC Telescope-Agda
  extendContext :
    ∀ {a} {A : UU a} → String → Argument-Agda Term-Agda → TC A → TC A
  inContext : ∀ {a} {A : UU a} → Telescope-Agda → TC A → TC A
  freshName : String → TC Name-Agda
  declareDef : Argument-Agda Name-Agda → Term-Agda → TC unit
  declarePostulate : Argument-Agda Name-Agda → Term-Agda → TC unit
  defineFun : Name-Agda → list Clause-Agda → TC unit
  getType : Name-Agda → TC Term-Agda
  getDefinition : Name-Agda → TC Definition-Agda
  blockTC : ∀ {a} {A : UU a} → Blocker-Agda → TC A
  commitTC : TC unit
  isMacro : Name-Agda → TC bool

  formatErrorParts : list ErrorPart → TC String

  -- Prints the third argument if the corresponding verbosity level is turned
  -- on (with the -v flag to Agda).
  debugPrint : String → ℕ → list ErrorPart → TC unit

  -- If 'true', makes the following primitives also normalise
  -- their results: inferType, checkType, quoteTC, getType, and getContext
  withNormalisation : ∀ {a} {A : UU a} → bool → TC A → TC A
  askNormalisation : TC bool

  -- If 'true', makes the following primitives to reconstruct hidden arguments:
  -- getDefinition, normalise, reduce, inferType, checkType and getContext
  withReconstructed : ∀ {a} {A : UU a} → bool → TC A → TC A
  askReconstructed : TC bool

  -- Whether implicit arguments at the end should be turned into metavariables
  withExpandLast : ∀ {a} {A : UU a} → bool → TC A → TC A
  askExpandLast : TC bool

  -- White/blacklist specific definitions for reduction while executing the TC computation
  -- 'true' for whitelist, 'false' for blacklist
  withReduceDefs :
    ∀ {a} {A : UU a} → (Σ bool λ _ → list Name-Agda) → TC A → TC A
  askReduceDefs : TC (Σ bool λ _ → list Name-Agda)

  -- Fail if the given computation gives rise to new, unsolved
  -- "blocking" constraints.
  noConstraints : ∀ {a} {A : UU a} → TC A → TC A

  -- Run the given TC action and return the first component. Resets to
  -- the old TC state if the second component is 'false', or keep the
  -- new TC state if it is 'true'.
  runSpeculative : ∀ {a} {A : UU a} → TC (Σ A λ _ → bool) → TC A

  -- Get a list of all possible instance candidates for the given metavariable-Term-Agda
  -- variable (it does not have to be an instance metavariable-Term-Agda).
  getInstances : Metavariable-Agda → TC (list Term-Agda)

  declareData : Name-Agda → ℕ → Term-Agda → TC unit
  defineData : Name-Agda → list (Σ Name-Agda (λ _ → Term-Agda)) → TC unit
```

<details><summary>Bindings</summary>

```agda
{-# BUILTIN AGDAERRORPART ErrorPart #-}
{-# BUILTIN AGDAERRORPARTSTRING strErr #-}
{-# BUILTIN AGDAERRORPARTTERM termErr #-}
{-# BUILTIN AGDAERRORPARTPATT pattErr #-}
{-# BUILTIN AGDAERRORPARTNAME nameErr #-}

{-# BUILTIN AGDATCM TC #-}
{-# BUILTIN AGDATCMRETURN returnTC #-}
{-# BUILTIN AGDATCMBIND bindTC #-}
{-# BUILTIN AGDATCMUNIFY unify #-}
{-# BUILTIN AGDATCMTYPEERROR typeError #-}
{-# BUILTIN AGDATCMINFERTYPE inferType #-}
{-# BUILTIN AGDATCMCHECKTYPE checkType #-}
{-# BUILTIN AGDATCMNORMALISE normalise #-}
{-# BUILTIN AGDATCMREDUCE reduce #-}
{-# BUILTIN AGDATCMCATCHERROR catchTC #-}
{-# BUILTIN AGDATCMQUOTETERM quoteTC #-}
{-# BUILTIN AGDATCMUNQUOTETERM unquoteTC #-}
{-# BUILTIN AGDATCMQUOTEOMEGATERM quoteωTC #-}
{-# BUILTIN AGDATCMGETCONTEXT getContext #-}
{-# BUILTIN AGDATCMEXTENDCONTEXT extendContext #-}
{-# BUILTIN AGDATCMINCONTEXT inContext #-}
{-# BUILTIN AGDATCMFRESHNAME freshName #-}
{-# BUILTIN AGDATCMDECLAREDEF declareDef #-}
{-# BUILTIN AGDATCMDECLAREPOSTULATE declarePostulate #-}
{-# BUILTIN AGDATCMDEFINEFUN defineFun #-}
{-# BUILTIN AGDATCMGETTYPE getType #-}
{-# BUILTIN AGDATCMGETDEFINITION getDefinition #-}
{-# BUILTIN AGDATCMBLOCK blockTC #-}
{-# BUILTIN AGDATCMCOMMIT commitTC #-}
{-# BUILTIN AGDATCMISMACRO isMacro #-}
{-# BUILTIN AGDATCMWITHNORMALISATION withNormalisation #-}
{-# BUILTIN AGDATCMFORMATERRORPARTS formatErrorParts #-}
{-# BUILTIN AGDATCMDEBUGPRINT debugPrint #-}
{-# BUILTIN AGDATCMWITHRECONSTRUCTED withReconstructed #-}
{-# BUILTIN AGDATCMWITHEXPANDLAST withExpandLast #-}
{-# BUILTIN AGDATCMWITHREDUCEDEFS withReduceDefs #-}
{-# BUILTIN AGDATCMASKNORMALISATION askNormalisation #-}
{-# BUILTIN AGDATCMASKRECONSTRUCTED askReconstructed #-}
{-# BUILTIN AGDATCMASKEXPANDLAST askExpandLast #-}
{-# BUILTIN AGDATCMASKREDUCEDEFS askReduceDefs #-}
{-# BUILTIN AGDATCMNOCONSTRAINTS noConstraints #-}
{-# BUILTIN AGDATCMRUNSPECULATIVE runSpeculative #-}
{-# BUILTIN AGDATCMGETINSTANCES getInstances #-}
{-# BUILTIN AGDATCMDECLAREDATA declareData #-}
{-# BUILTIN AGDATCMDEFINEDATA defineData #-}
```

</details>

## Monad syntax

```agda
infixl 15 _<|>_
_<|>_ : {l : Level} {A : UU l} → TC A → TC A → TC A
_<|>_ = catchTC

infixl 10 _>>=_ _>>_ _<&>_
_>>=_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  TC A → (A → TC B) → TC B
_>>=_ = bindTC

_>>_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  TC A → TC B → TC B
xs >> ys = bindTC xs (λ _ → ys)

_<&>_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  TC A → (A → B) → TC B
xs <&> f = bindTC xs (λ x → returnTC (f x))
```

## Examples

The following examples show how the type-checking monad can be used. They were
adapted from alhassy's
[_gentle intro to reflection_](https://github.com/alhassy/gentle-intro-to-reflection).

### Unifying a goal with a constant

#### Manually

```agda
private
  numTCM : Term-Agda → TC unit
  numTCM h = unify (quoteTerm 314) h

  _ : unquote numTCM ＝ 314
  _ = refl
```

#### By use of a macro

```agda
  macro
    numTCM' : Term-Agda → TC unit
    numTCM' h = unify (quoteTerm 1) h

  _ : numTCM' ＝ 1
  _ = refl
```

### Modifying a term

```agda
  macro
    swap-add : Term-Agda → Term-Agda → TC unit
    swap-add (definition-Term-Agda (quote add-ℕ) (cons a (cons b nil))) hole =
      unify hole (definition-Term-Agda (quote add-ℕ) (cons b (cons a nil)))
    {-# CATCHALL #-}
    swap-add v hole = unify hole v

  ex1 : (a b : ℕ) → swap-add (add-ℕ a b) ＝ (add-ℕ b a)
  ex1 a b = refl

  ex2 : (a b : ℕ) → swap-add a ＝ a
  ex2 a b = refl
```

### Trying a path

The following example tries to solve a goal by using path `p` or `inv p`. This
example was addapted from

```agda
  private
    infixr 10 _∷_
    pattern _∷_ x xs = cons x xs

  ＝-type-info :
    Term-Agda →
    TC
      ( Argument-Agda Term-Agda ×
        ( Argument-Agda Term-Agda ×
          ( Term-Agda × Term-Agda)))
  ＝-type-info
    ( definition-Term-Agda (quote _＝_) (𝓁 ∷ 𝒯 ∷ (arg _ l) ∷ (arg _ r) ∷ nil)) =
    returnTC (𝓁 , 𝒯 , l , r)
  ＝-type-info _ = typeError (unit-list (strErr "Term-Agda is not a ＝-type."))

  macro
    try-path! : Term-Agda → Term-Agda → TC unit
    try-path! p goal =
      ( unify goal p) <|>
      ( do
        p-type ← inferType p
        𝓁 , 𝒯 , l , r ← ＝-type-info p-type
        unify goal
          ( definition-Term-Agda (quote inv)
            ( 𝓁 ∷
              𝒯 ∷
              hidden-Argument-Agda l ∷
              hidden-Argument-Agda r ∷
              visible-Argument-Agda p ∷
              nil)))

  module _ (a b : ℕ) (p : a ＝ b) where
    ex3 : Id a b
    ex3 = try-path! p

    ex4 : Id b a
    ex4 = try-path! p
```

### Getting the lhs and rhs of a goal

```agda
boundary-TCM : Term-Agda → TC (Term-Agda × Term-Agda)
boundary-TCM
  ( definition-Term-Agda
    ( quote Id)
    ( 𝓁 ∷ 𝒯 ∷ arg _ l ∷ arg _ r ∷ nil)) =
  returnTC (l , r)
boundary-TCM t =
  typeError
    ( strErr "The term\n " ∷
      termErr t ∷
      strErr "\nis not a ＝-type." ∷
      nil)
```
