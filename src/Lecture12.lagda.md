	-*- mode: agda2;-*-

```
module Lecture12 where
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
    → Γ ⊢ `ℕ ⇒ A ⇒ A
      ---------------
    → Γ ⊢ A
```

To explain `recnat`, we consider the reduction rules informally.

1.  `recnat zero M N` reduces to `M`
    ... just like `case`
2.  `recnat (suc V) M N` reduces to `N · V · recnat V M N`
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
𝓔⟦ recnat M M₁ M₂ ⟧ γ = recnat′ (𝓔⟦ M ⟧ γ) (𝓔⟦ M₁ ⟧ γ) (𝓔⟦ M₂ ⟧ γ)
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
rename ρ (recnat ⊢A ⊢A₁ ⊢A₂) = recnat (rename ρ ⊢A) (rename ρ ⊢A₁) (rename ρ ⊢A₂)
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
subst σ (recnat ⊢A ⊢A₁ ⊢A₂) = recnat (subst σ ⊢A) (subst σ ⊢A₁) (subst σ ⊢A₂)
```

### special case: single substitution

Required case for type preservation / β reduction

```
σ₀ : (M : Γ ⊢ B) → Sub (Γ , B) Γ
σ₀ M Z = M
σ₀ M (S x) = ` x

_[_] : ∀ {Γ A B}
  → Γ , B ⊢ A
  → Γ ⊢ B
    ---------
  → Γ ⊢ A
_[_] {Γ} {A} {B} N M = subst (σ₀ M) N
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

  ξ-recnat : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ  ⊢ `ℕ ⇒ A ⇒ A}
    → L ⟶ L′
      -------------------------
    → recnat L M N ⟶ recnat L′ M N

  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ ⊢ `ℕ ⇒ A ⇒ A}
      -------------------
    → recnat `zero M N ⟶ M

  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ ⊢ `ℕ ⇒ A ⇒ A}
    → Value V
      ----------------------------
    → recnat (`suc V) M N ⟶ N · V · recnat V M N
```

## Relation of small-step reduction to the denotational semantics

Soundness of small-step reduction

Semantic substitution

```
postulate
  ext : ∀ {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

𝓢⟦_⟧ : Sub Γ Δ → 𝓒⟦ Δ ⟧ → 𝓒⟦ Γ ⟧
𝓢⟦_⟧ {Γ = ∅} σ δ = tt
𝓢⟦_⟧ {Γ = Γ , A} σ δ = ⟨ (𝓢⟦ (σ ∘ S_) ⟧ δ) , (𝓔⟦ σ Z ⟧ δ) ⟩

postulate
  𝓢-ext : ∀ {a : 𝓣⟦ A ⟧} (σ : Sub Γ Δ) (δ : 𝓒⟦ Δ ⟧) → ⟨ 𝓢⟦ σ ⟧ δ , a ⟩ ≡ 𝓢⟦ exts σ ⟧ ⟨ δ , a ⟩

subst-id : (γ : 𝓒⟦ Γ ⟧) → γ ≡ 𝓢⟦ `_ ⟧ γ
subst-id {Γ = ∅} tt = refl
subst-id {Γ = Γ , A} ⟨ γ , a ⟩ = (cong ⟨_, a ⟩) {!!}
```

Composing a substitution with a semantic substitution

```
sound-var : (x : Γ ∋ A) (σ : Sub Γ Δ) (δ : 𝓒⟦ Δ ⟧) → 𝓥⟦ x ⟧ (𝓢⟦ σ ⟧ δ) ≡ 𝓔⟦ σ x ⟧ δ
sound-var Z σ δ = refl
sound-var (S x) σ δ = sound-var x (σ ∘ S_) δ

sound-sub : (M : Γ ⊢ A) (σ : Sub Γ Δ) (δ : 𝓒⟦ Δ ⟧) → 𝓔⟦ M ⟧ (𝓢⟦ σ ⟧ δ) ≡ 𝓔⟦ subst σ M ⟧ δ
sound-sub (` x) σ δ = sound-var x σ δ
sound-sub (ƛ M) σ δ = ext λ a → trans (cong 𝓔⟦ M ⟧ (𝓢-ext σ δ)) {!!}
sound-sub (M · M₁) σ δ rewrite sound-sub M σ δ | sound-sub M₁ σ δ = refl
sound-sub `zero σ δ = refl
sound-sub (`suc M) σ δ rewrite sound-sub M σ δ = refl
sound-sub (recnat M M₁ M₂) σ δ rewrite sound-sub M σ δ | sound-sub M₁ σ δ | sound-sub M₂ σ δ = refl
```

Soundness of the small-step semantics: making a reduction does not change the semantics


```
sound⟶ : ∀ {M N : Γ ⊢ A} → M ⟶ N → (γ : 𝓒⟦ Γ ⟧) → 𝓔⟦ M ⟧ γ ≡ 𝓔⟦ N ⟧ γ
sound⟶ (ξ-·₁ M⟶N) γ              rewrite sound⟶ M⟶N γ = refl
sound⟶ (ξ-·₂ x M⟶N) γ            rewrite sound⟶ M⟶N γ = refl
sound⟶ (β-ƛ {N = N}{W = W} x) γ  rewrite sym (sound-sub N (σ₀ W) γ) | sym (subst-id γ) = refl
sound⟶ (ξ-suc M⟶N) γ             rewrite sound⟶ M⟶N γ = refl
sound⟶ (ξ-recnat M⟶N) γ          rewrite sound⟶ M⟶N γ = refl
sound⟶ β-zero γ = refl
sound⟶ (β-suc x) γ = refl
```

It is possible to show completeness, in the sense that
for all `M : ∅ ⊢ ℕ` it holds that `𝓔⟦ M ⟧ tt ≡ n` implies that `M ⟹ V`, `Value V`, and `V ∼ n`.
But it requires a new technique...

(BTW, this result implies that all closed terms of type ℕ terminate!)

