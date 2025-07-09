	-*- mode: agda2;-*-

```
module Lecture11 where
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; _≟_)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Nullary.Decidable using (Dec; yes; no; False; toWitnessFalse; ¬?)

```


# Alternative styles of semantics

So far, we considered *small-step reduction semantics*:

* a syntactic method (defined on the abstract syntax of expressions)
* breaks down computation into single steps that apply (mostly) local rewrites
* defined as a relation `_⟶_ : Term → Term → Set` and its reflexive-transitive closure
* scales to concurrent languages

Closest competitor: *big-step semantics*

* syntactic
* squeezes all computation in a single, structured step
* defined as a relation `_⇓_ : Term → Value → Set`
* here `Value` could be distinct from `Term`, but often `Value ⊆ Term`
* drawback: difficult to model non-terminating computations

Different beast: *denotational semantics*

* maps syntax to a *semantic domain* of our choosing
* no notion of reduction or computation, but a term is directly mapped to its value
* defined as a function `⟦_⟧ : Term → Domain`
* the definition is *compositional*, i.e., the semantics of a term is defined as a function of the semantics of its subterms.
* drawback: non-trivial domain construction required to model recursion and non-terminating computations

## Plan

We generally stick with the simply-typed lambda calculus.

* Define big-step semantics and relate to small-step semantics
* Define a terminating subset `λT` of our subject calculus
* Define denotational semantics for `λT` and relate






# Big step semantics

```
module big-step where
  open import Lecture10 renaming (_—→_ to _⟶_; _—↠_ to _⟹_)

  infix 2 _⇓_

  data _⇓_ : ∅ ⊢ A → ∅ ⊢ A → Set where

    ⇓-ƛ : ∀ {N : ∅ , A ⊢ B} → (ƛ N) ⇓ (ƛ N)

    ⇓-· : ∀ {M : ∅ ⊢ A ⇒ B} {M′ : ∅ , A ⊢ B} {N W : ∅ ⊢ A} {V : ∅ ⊢ B} →
          M ⇓ ƛ M′
        → N ⇓ W
        → M′ [ W ] ⇓ V
          --------------------
        → M · N ⇓ V

    ⇓-zero : `zero ⇓ `zero

    ⇓-suc : ∀ {M V : ∅ ⊢ `ℕ}
        →  M ⇓ V
          --------------------
        → `suc M ⇓ `suc V

    ⇓-case-zero : ∀ {L : ∅ ⊢ `ℕ} {M W : ∅ ⊢ A} {N : ∅ , `ℕ ⊢ A}
        → L ⇓ `zero
        → M ⇓ W
          --------------------
        → case L M N ⇓ W

    ⇓-case-suc : ∀ {L V : ∅ ⊢ `ℕ} {M W : ∅ ⊢ A} {N : ∅ , `ℕ ⊢ A}
        → L ⇓ `suc V
        → N [ V ] ⇓ W
          --------------------
        → case L M N ⇓ W

    ⇓-μ : ∀ {M : ∅ , A ⊢ A} {V : ∅ ⊢ A}
        → M [ μ M ] ⇓ V
        → μ M ⇓ V

```

Let's show that each outcome of the big-step relation is a syntactic value,
which is similar to a type safety result.

```
  ⇓-value : ∀ {M V : ∅ ⊢ A} → M ⇓ V → Value V
  ⇓-value ⇓-ƛ = ƛ _
  ⇓-value (⇓-· ⇓ ⇓₁ ⇓₂) = ⇓-value ⇓₂
  ⇓-value ⇓-zero = `zero
  ⇓-value (⇓-suc ⇓) = `suc (⇓-value ⇓)
  ⇓-value (⇓-case-zero ⇓ ⇓₁) = ⇓-value ⇓₁
  ⇓-value (⇓-case-suc ⇓ ⇓₁) = ⇓-value ⇓₁
  ⇓-value (⇓-μ ⇓) = ⇓-value ⇓
```

Important: this lemma says nothing about nonterminating computations.
If (small-step) reduction of `M` does not terminate,
then there is no `V` such that there is a (finite) derivation of `M ⇓ V`.


One way of fixing this issue is gas.

```
  data [_]_⇓_ : ℕ → ∅ ⊢ A → Maybe (∅ ⊢ A) → Set where

    out-of-gas : ∀ {M : ∅ ⊢ A}
               →  [ zero ] M ⇓ nothing

    ⇓-ƛ : ∀ {g}{N : ∅ , A ⊢ B} → [ g ] (ƛ N) ⇓ just (ƛ N)

    ⇓-·₁ : ∀ {g} {M : ∅ ⊢ A ⇒ B} {N : ∅ ⊢ A} →
          [ g ] M ⇓ nothing
          --------------------
        → [ suc g ] M · N ⇓ nothing

    ⇓-·₂ : ∀ {g}{M : ∅ ⊢ A ⇒ B} {M′ : ∅ , A ⊢ B} {N : ∅ ⊢ A} →
          [ g ] M ⇓ just (ƛ M′)
        → [ g ] N ⇓ nothing
          --------------------
        → [ suc g ] M · N ⇓ nothing

    ⇓-·₃ : ∀ {g} {M : ∅ ⊢ A ⇒ B} {M′ : ∅ , A ⊢ B} {N W : ∅ ⊢ A} →
          [ g ] M ⇓ just (ƛ M′)
        → [ g ] N ⇓ just W
        → [ g ] M′ [ W ] ⇓ nothing
          --------------------
        → [ suc g ] M · N ⇓ nothing

    ⇓-· : ∀ {g} {M : ∅ ⊢ A ⇒ B} {M′ : ∅ , A ⊢ B} {N W : ∅ ⊢ A} {V : ∅ ⊢ B} →
          [ g ] M ⇓ just (ƛ M′)
        → [ g ] N ⇓ just W
        → [ g ] (M′ [ W ]) ⇓ just V
          --------------------
        → [ suc g ] M · N ⇓ just V

    ⇓-zero : ∀ {g} → [ g ] `zero ⇓ just `zero

    -- ⇓-suc : ∀ {M V : ∅ ⊢ `ℕ}
    --     →  M ⇓ V
    --       --------------------
    --     → `suc M ⇓ `suc V

    -- ⇓-case-zero : ∀ {L : ∅ ⊢ `ℕ} {M W : ∅ ⊢ A} {N : ∅ , `ℕ ⊢ A}
    --     → L ⇓ `zero
    --     → M ⇓ W
    --       --------------------
    --     → case L M N ⇓ W

    -- ⇓-case-suc : ∀ {L V : ∅ ⊢ `ℕ} {M W : ∅ ⊢ A} {N : ∅ , `ℕ ⊢ A}
    --     → L ⇓ `suc V
    --     → N [ V ] ⇓ W
    --       --------------------
    --     → case L M N ⇓ W

    -- ⇓-μ : ∀ {M : ∅ , A ⊢ A} {V : ∅ ⊢ A}
    --     → M [ μ M ] ⇓ V
    --     → μ M ⇓ V

```

Then we can say:

```
  ⇓-value′ : ∀ {n}{M V : ∅ ⊢ A} → [ n ] M ⇓ just V → Value V
  ⇓-value′ ⇓-ƛ = ƛ _
  ⇓-value′ (⇓-· x x₁ x₂) = ⇓-value′ x₂
  ⇓-value′ ⇓-zero = `zero
```

Big-step semantics are quite similar to interpreters.
In fact, the big-step relation is a (partial) function:

```
  ⇓-functional : ∀ {M V V′ : ∅ ⊢ A} → M ⇓ V → M ⇓ V′ → V ≡ V′
  ⇓-functional ⇓-ƛ ⇓-ƛ = refl
  ⇓-functional (⇓-· ⇓ ⇓₁ ⇓₂) (⇓-· ⇓₃ ⇓₄ ⇓₅)
    with refl ← ⇓-functional (⇓) ⇓₃
    with refl ← ⇓-functional ⇓₁ ⇓₄
    = ⇓-functional ⇓₂ ⇓₅
  ⇓-functional ⇓-zero ⇓-zero = refl
  ⇓-functional (⇓-suc ⇓) (⇓-suc ⇓₁)
    with refl ← ⇓-functional (⇓) ⇓₁
    = refl
  ⇓-functional (⇓-case-zero ⇓ ⇓₁) (⇓-case-zero ⇓₂ ⇓₃) = ⇓-functional ⇓₁ ⇓₃
  ⇓-functional (⇓-case-zero ⇓ ⇓₁) (⇓-case-suc ⇓₂ ⇓₃)
    with ⇓-functional (⇓) ⇓₂
  ... | ()
  ⇓-functional (⇓-case-suc ⇓ ⇓₁) (⇓-case-zero ⇓₂ ⇓₃)
    with ⇓-functional (⇓) ⇓₂
  ... | ()
  ⇓-functional (⇓-case-suc ⇓ ⇓₁) (⇓-case-suc ⇓₂ ⇓₃)
    with refl ← ⇓-functional (⇓) ⇓₂
    = ⇓-functional ⇓₁ ⇓₃
  ⇓-functional (⇓-μ ⇓) (⇓-μ ⇓₁)
    with refl ← ⇓-functional (⇓) ⇓₁
    = refl
```

Hence, we could implement it as a function, too.
TODO?

## Relation to small-step semantics

If the big-step semantics yields a value, we can reach that value in
a finite number of small-step reduction steps.

It requires a bunch of lemmas about multi-step reduction.

```
  ξ-suc* : ∀ {M N : ∅ ⊢ `ℕ } → M ⟹ N → `suc M ⟹ `suc N
  ξ-suc* (_ ∎) = `suc _ ∎
  ξ-suc* (_ —→⟨ x ⟩ M⟹N) = (`suc _ —→⟨ ξ-suc x ⟩ (ξ-suc* M⟹N))

  ξ-·₁* : ∀ {M N : ∅ ⊢ A ⇒ B } { L : ∅ ⊢ A } → M ⟹ N → M · L ⟹ N · L
  ξ-·₁* (_ ∎) = _ · _ ∎
  ξ-·₁* (_ —→⟨ x ⟩ M⟹N) = step—→ (_ · _) (ξ-·₁* M⟹N) (ξ-·₁ x)

  ξ-·₂* : ∀ {M N : ∅ ⊢ A } { L : ∅ ⊢ A ⇒ B } → M ⟹ N → Value L → L · M ⟹ L · N
  ξ-·₂* (_ ∎) v = _ · _ ∎
  ξ-·₂* (_ —→⟨ x ⟩ M⟹N) v = step—→ (_ · _) (ξ-·₂* M⟹N v) (ξ-·₂ v x)

  ξ-case* : ∀ {L L′ : ∅ ⊢ `ℕ}{M : ∅ ⊢ A} {N : ∅ , `ℕ ⊢ A} → L ⟹ L′ → case L M N ⟹ case L′ M N
  ξ-case* (_ ∎) = case _ _ _ ∎
  ξ-case* (_ —→⟨ x ⟩ L⟹L′) = step—→ (case _ _ _) (ξ-case* L⟹L′) (ξ-case x)

  _++_ : ∀ {L M N : ∅ ⊢ A} → L ⟹ M → M ⟹ N → L ⟹ N
  (_ ∎) ++ M⟹N = M⟹N
  (_ —→⟨ x ⟩ L⟹M) ++ M⟹N = (_ —→⟨ x ⟩ (L⟹M ++ M⟹N))

```

```
  big⇒small : ∀ {M V : ∅ ⊢ A} → M ⇓ V → M ⟹ V
  big⇒small ⇓-ƛ = ƛ _ ∎
  big⇒small (⇓-· M⇓V M⇓V₁ M⇓V₂) = 
    let r1 = ξ-·₁* (big⇒small M⇓V) in
    let r2 = ξ-·₂* (big⇒small M⇓V₁) (⇓-value M⇓V) in
    let r3 = r1 ++ r2 in
    let r4 = big⇒small M⇓V₂ in
    let r5 = (_ —→⟨ β-ƛ (⇓-value M⇓V₁) ⟩ r4) in
    r3 ++ r5
  big⇒small ⇓-zero = `zero ∎
  big⇒small (⇓-suc M⇓V) = ξ-suc* (big⇒small M⇓V)
  big⇒small (⇓-case-zero M⇓V M⇓V₁) =
    let r1 = ξ-case* (big⇒small M⇓V) in
    let r2 = (_ —→⟨ β-zero ⟩ big⇒small M⇓V₁) in
    r1 ++ r2
  big⇒small (⇓-case-suc M⇓V M⇓V₁)
    with ξ-case* (big⇒small M⇓V) | ⇓-value M⇓V
  ... | r1 | `suc v =
    let r2 = (_ —→⟨ β-suc v ⟩ big⇒small M⇓V₁) in
    r1 ++ r2
  big⇒small (⇓-μ M⇓V) = (_ —→⟨ β-μ ⟩ big⇒small M⇓V)
```

For the reverse direction a little more work is required.

```
  small⇒big : ∀ {M V : ∅ ⊢ A} → M ⟹ V → Value V → M ⇓ V
  small⇒big (_ ∎) (ƛ N) = ⇓-ƛ
  small⇒big (_ ∎) `zero = ⇓-zero
  small⇒big (_ ∎) (`suc val-V) = ⇓-suc (small⇒big (_ ∎) val-V)
  small⇒big (_ —→⟨ ξ-·₁ L⟶L′ ⟩ M⟹V) val-V = {!!}
  small⇒big (_ —→⟨ ξ-·₂ x x₁ ⟩ M⟹V) val-V = {!!}
  small⇒big (_ —→⟨ β-ƛ x ⟩ M⟹V) val-V = ⇓-· (small⇒big (_ ∎) (ƛ _)) (small⇒big (_ ∎) x) (small⇒big M⟹V val-V)
  small⇒big (_ —→⟨ ξ-suc x ⟩ M⟹V) val-V = {!!}
  small⇒big (_ —→⟨ ξ-case x ⟩ M⟹V) val-V = {!!}
  small⇒big (_ —→⟨ β-zero ⟩ M⟹V) val-V = ⇓-case-zero ⇓-zero (small⇒big M⟹V val-V)
  small⇒big (_ —→⟨ β-suc x ⟩ M⟹V) val-V = ⇓-case-suc (small⇒big (_ ∎) (`suc x)) (small⇒big M⟹V val-V)
  small⇒big (_ —→⟨ β-μ ⟩ M⟹V) val-V = ⇓-μ (small⇒big M⟹V val-V)
```

Lemma: L · M ⟹ V can be decomposed into
       ξ-·₁ (L ⟹ ƛ L′) ++ ξ-·₂ (M ⟹ WM) ++ β-ƛ ++ (L′ [ WM ] ⟹ V)

# Towards denotational semantics

To ensure that we can choose sets (i.e., plain Agda types) as semantics domains,
we remove the fixpoint operator `μ` from the calculus and replace the `case` on
natural numbers with a *recursor*. The recursor implements primitive recursion,
which ensures termination.

(we copy some definitions ...)

```
infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 S_
```

## Syntax

## Simple Types (as before)

```
data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

variable
  A B C : Type
```

## Contexts (as before)

```
data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context

variable
  Γ Δ : Context
```

## Variable lookup (as before)

```
data _∋_ : Context → Type → Set where

  Z : ∀ {Γ}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A
```

## Terms and typing

Same as before, except that we remove `μ` and replace `case` by `recnat`.

```
data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_  : ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  `zero : ∀ {Γ}
      ---------
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
      ------
    → Γ ⊢ `ℕ

  recnat : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , A , `ℕ ⊢ A
      ---------------
    → Γ ⊢ A
```

To explain `recnat`, we consider the reduction rules informally.

1.  `recnat zero M N` reduces to `M`
    ... just like `case`
2.  `recnat (suc V) M N` reduces to `(ƛ N [ V ]) · recnat V M N`
    we first pass the predecessor and then the result of the recursive call on the predecessor

## Denotational semantics

The semantic domain of a type is defined by induction.

```
𝓣⟦_⟧ : Type → Set
𝓣⟦ A ⇒ B ⟧ = 𝓣⟦ A ⟧ → 𝓣⟦ B ⟧
𝓣⟦ `ℕ ⟧ = ℕ
```

We also need a semantics of typing contexts.

```
𝓒⟦_⟧ : Context → Set
𝓒⟦ ∅ ⟧ = ⊤
𝓒⟦ Γ , A ⟧ = 𝓒⟦ Γ ⟧ × 𝓣⟦ A ⟧
```

The semantics of a term is also defined by induction on terms.
As the definition is compositional we have to provide semantics for
open terms.

```
recnat′ : ∀ {X : Set} → ℕ → X → (ℕ → X → X) → X
recnat′ zero x₀ xₛ = x₀
recnat′ (suc n) x₀ xₛ = xₛ n (recnat′ n x₀ xₛ)

𝓥⟦_⟧ : Γ ∋ A → 𝓒⟦ Γ ⟧ → 𝓣⟦ A ⟧
𝓥⟦ Z ⟧ ⟨ _ , x ⟩ = x
𝓥⟦ S x∈ ⟧ ⟨ γ , _ ⟩ = 𝓥⟦ x∈ ⟧ γ

𝓔⟦_⟧ : Γ ⊢ A → 𝓒⟦ Γ ⟧ → 𝓣⟦ A ⟧
𝓔⟦ ` x ⟧ γ = 𝓥⟦ x ⟧ γ
𝓔⟦ ƛ M ⟧ γ = λ x → 𝓔⟦ M ⟧ ⟨ γ , x ⟩
𝓔⟦ M · M₁ ⟧ γ = 𝓔⟦ M ⟧ γ (𝓔⟦ M₁ ⟧ γ)
𝓔⟦ `zero ⟧ γ = 0
𝓔⟦ `suc M ⟧ γ = suc (𝓔⟦ M ⟧ γ)
𝓔⟦ recnat M M₁ M₂ ⟧ γ = recnat′ (𝓔⟦ M ⟧ γ) (𝓔⟦ M₁ ⟧ γ) λ n x → 𝓔⟦ M₂ ⟧ ⟨ ⟨ γ , x ⟩ , n ⟩
```

To compare with an operational semantics, we need to recapitulate some of the definitions
of the last chapter.

## Revised small-step semantis


### Renaming

As before, a renaming is a mapping between variable lookups in different environments:

```
Ren : Context → Context → Set
Ren Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A
```

Extend a renaming to adapt to an extra binding.

```
extr : Ren Γ Δ → Ren (Γ , A) (Δ , A)
extr ρ Z = Z
extr ρ (S x) = S (ρ x)
```

We apply a renaming to a term.

```
rename : ∀ {Γ Δ}
  → Ren Γ Δ
  → Γ ⊢ A
  → Δ ⊢ A
rename ρ (` x) = ` (ρ x)
rename ρ (ƛ ⊢A) = ƛ rename (extr ρ) ⊢A
rename ρ (⊢A · ⊢A₁) = (rename ρ ⊢A) · (rename ρ ⊢A₁)
rename ρ `zero = `zero
rename ρ (`suc ⊢A) = `suc (rename ρ ⊢A)
rename ρ (recnat ⊢A ⊢A₁ ⊢A₂) = recnat (rename ρ ⊢A) (rename ρ ⊢A₁) {!!}
```

```
weaken : Γ ⊢ A → Γ , B ⊢ A
weaken M = rename S_ M
```

### Substitution

A substitution from Γ to Δ maps any variable of type `A` in an environment `Γ` to a term in environment Δ.

```
Sub : Context → Context → Set
Sub Γ Δ =  ∀ {A} → Γ ∋ A → Δ ⊢ A
```

Extension for substitution.

```
exts : Sub Γ Δ → Sub (Γ , A) (Δ , A)
exts σ Z = ` Z
exts σ (S x) = rename S_ (σ x)
```

We apply a substitution to a term.

```
subst : ∀ {Γ Δ}
  → Sub Γ Δ
  → Γ ⊢ A
  → Δ ⊢ A
subst σ (` x) = σ x
subst σ (ƛ ⊢A) = ƛ subst (exts σ) ⊢A
subst σ (⊢A · ⊢A₁) = (subst σ ⊢A) · (subst σ ⊢A₁)
subst σ `zero = `zero
subst σ (`suc ⊢A) = `suc (subst σ ⊢A)
subst σ (recnat ⊢A ⊢A₁ ⊢A₂) = recnat (subst σ ⊢A) (subst σ ⊢A₁) {!!}
```

### special case: single substitution

Required case for type preservation / β reduction

```
_[_] : ∀ {Γ A B}
  → Γ , B ⊢ A
  → Γ ⊢ B
    ---------
  → Γ ⊢ A
_[_] {Γ} {A} {B} N M = subst σ N
  where
    σ : Sub (Γ , B) Γ
    σ Z = M
    σ (S x) = ` x
```

### Values

```
data Value  {Γ} : ∀ {A} → Γ ⊢ A → Set where

  ƛ_ : (N : Γ , A ⊢ B)
      ---------------------------
    → Value (ƛ N)

  `zero : 
      -----------------
      Value `zero

  `suc_ : ∀ {V : Γ ⊢ `ℕ}
    → Value V
      --------------
    → Value (`suc V)
```


### Reduction

Due to intrinsic, Church-style encoding, reduction comes with proof of type preservation by construction!

```
infix 2 _⟶_

data _⟶_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L ⟶ L′
      ---------------
    → L · M ⟶ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M ⟶ M′
      ---------------
    → V · M ⟶ V · M′

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      --------------------
    → (ƛ N) · W ⟶ N [ W ]

  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M ⟶ M′
      -----------------
    → `suc M ⟶ `suc M′

  ξ-recnat : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , A , `ℕ ⊢ A}
    → L ⟶ L′
      -------------------------
    → recnat L M N ⟶ recnat L′ M N

  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , A , `ℕ ⊢ A}
      -------------------
    → recnat `zero M N ⟶ M

  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , A , `ℕ ⊢ A}
    → Value V
      ----------------------------
    → recnat (`suc V) M N ⟶ (ƛ N [ weaken V ]) · recnat V M N
```

## Relation of small-step reduction to the denotational semantics

Soundness of small-step reduction

```
sound⟶ : ∀ {M N : Γ ⊢ A} → (γ : 𝓒⟦ Γ ⟧) → 𝓔⟦ M ⟧ γ ≡ 𝓔⟦ N ⟧ γ
sound⟶ = {!!}
```

It is possible to show completeness, in the sense that
for all `M : ∅ ⊢ ℕ` it holds that `𝓔⟦ M ⟧ tt ≡ n` implies that `M ⟹ V`, `Value V`, and `V ∼ n`.
But it requires a new technique...

(BTW, this result implies that all closed terms of type ℕ terminate!)

