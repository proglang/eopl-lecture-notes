	-*- mode: agda2;-*-

```
module Lecture13 where
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_; T)
open import Data.Maybe
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_; _<ᵇ_; _+_; _≤_ ; _∸_ ; z≤n ; s≤s; _≤′_)
import Data.Nat.Properties as P
open import Data.Product
open import Data.String using (String; _≟_)
open import Data.Sum
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (id; _∘_; case_of_) renaming (case_return_of_ to case_ret_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; cong)
```

# Imperative programming

Syntax of the classical while language

    e ::= c | x | e ⊕ e
    b ::= e ∼ e | not b | b and b | b or b
    s ::=
      skip |
      x := e |
      if b then s else s |
      while b do s |
      s ; s















## formal syntax of the While language

```
Ident = String

Op : Set → Set
Op A = A → A → A

BOp : Set → Set
BOp A = A → A → Bool

data Expr : Set where
  `#_    : (n : ℕ) → Expr
  `_     : (x : Ident) → Expr
  _⟨_⟩_  : (e₁ : Expr) → (⊕ : Op ℕ) → (e₂ : Expr) → Expr

data BExpr : Set where
  `not      : (b : BExpr) → BExpr
  `and `or  : (b₁ : BExpr) → (b₂ : BExpr) → BExpr
  _⟨_⟩_     : (e₁ : Expr) → (∼ : BOp ℕ) → (e₂ : Expr) → BExpr

data Stmt : Set where
  Skp  : Stmt
  Ass  : (x : Ident) → (e : Expr) → Stmt
  Ite  : (b : BExpr) → (s₁ : Stmt) → (s₂ : Stmt) → Stmt
  Whl  : (b : BExpr) → (s : Stmt) → Stmt
  Seq  : (s₁ : Stmt) → (s₂ : Stmt) → Stmt
```

Example

```
example1 : Stmt
example1 = Ass "x" (`# 42)

example2 : Stmt
example2 = Ite ((` "x") ⟨ _≤ᵇ_ ⟩ (`# 5)) (Ass "x" (`# 0)) (Ass "x" (`# 5))

example3 : Stmt
example3 = Whl ((`# 0) ⟨ _<ᵇ_ ⟩ (` "x")) (Ass "x" ((` "x") ⟨ _∸_ ⟩ (`# 1)))
```




## Semantics I : small-step operational

A configuration of the semantics comprises two parts
1. the values of the variables: the state - a mapping of variables to values
2. the current statement

Idea of the semantics:
transform the statement, one atomic statement at a time
and keep track of the state as it is transformed by each statement

The state is initialized to all zeroes.
A program run corresponds to a sequence of configurations.















```
State = Ident → ℕ

update : Ident → ℕ → State → State
update x n σ y
  with x ≟ y
... | yes x≡y = n
... | no  _   = σ y
```

### Denotational semantics for expressions

Directly maps an expression to its denotation (i.e., a function from state to numbers).
Need the state to look up the values of variables.
(we could do it using small-step semantics, but it's not our focus today)
The bracket ⟦_⟧ usually encloses the syntactic phrase that is interpreted.
The definition is *compositional*, that is,
the semantics of an expression is defined as a function of the semantics of its subexpressions.


```
𝓔⟦_⟧ : Expr → State → ℕ
𝓔⟦ `# n ⟧ σ           = n
𝓔⟦ ` x ⟧ σ            = σ x
𝓔⟦ e₁ ⟨ _⊕_ ⟩ e₂ ⟧ σ  = 𝓔⟦ e₁ ⟧ σ ⊕ 𝓔⟦ e₂ ⟧ σ

𝓑⟦_⟧ : BExpr → State → Bool
𝓑⟦ `not b ⟧ σ    = not (𝓑⟦ b ⟧ σ)
𝓑⟦ `and b b₁ ⟧ σ = 𝓑⟦ b ⟧ σ ∧ 𝓑⟦ b₁ ⟧ σ
𝓑⟦ `or b b₁ ⟧ σ  = 𝓑⟦ b ⟧ σ ∨ 𝓑⟦ b₁ ⟧ σ
𝓑⟦ e₁ ⟨ _relop_ ⟩ e₂ ⟧ σ = 𝓔⟦ e₁ ⟧ σ relop 𝓔⟦ e₂ ⟧ σ
```

### Small-step reduction relation for statements

A configuration of the semantics is a pair of state and statement

```
data _—→_ : State × Stmt → State × Stmt → Set where

  Ass→ : ∀ {σ}{x}{e} →
        (σ , Ass x e) —→ (update x (𝓔⟦ e ⟧ σ) σ , Skp)

  Ite→₁ : ∀ {σ}{b}{s₁}{s₂} →
         𝓑⟦ b ⟧ σ ≡ true →
        (σ , Ite b s₁ s₂) —→ (σ , s₁)

  Ite→₂ : ∀ {σ}{b}{s₁}{s₂} →
         𝓑⟦ b ⟧ σ ≡ false →
        (σ , Ite b s₁ s₂) —→ (σ , s₂)

  Whl→ : ∀ {σ}{b}{s} →
       (σ , Whl b s) —→ (σ , Ite b (Seq s (Whl b s)) Skp)

  Seq→₁ : ∀ {σ σ′ s₁ s₁′ s₂} →
        (σ , s₁) —→ (σ′ , s₁′)
        ---------------------------------
      → (σ , Seq s₁ s₂) —→ (σ′ , Seq s₁′ s₂)

  Seq→₂ : ∀ {σ s₂}
      → (σ , Seq Skp s₂) —→ (σ , s₂)
```

### Program reduction (only terminating computations)

```
data _⇓_ : State × Stmt → State → Set where
  step : ∀ {σ}{σ′}{σ″}{s}{s′} →
    (σ , s) —→ (σ′ , s′) →
    (σ′ , s′) ⇓ σ″ →
    (σ , s) ⇓ σ″
  done : ∀ {σ} →
    (σ , Skp) ⇓ σ

⇓-trans : ∀ {σ}{σ₁}{σ₂}{s}{s₁} → (σ , s) ⇓ σ₁ → (σ₁ , s₁) ⇓ σ₂ → (σ , Seq s s₁) ⇓ σ₂
⇓-trans (step r ⇓) ⇓₁ = step (Seq→₁ r) (⇓-trans (⇓) ⇓₁)
⇓-trans done ⇓₁ = step Seq→₂ ⇓₁
```


## Verification of while programs

Hoare calculus is a logical calculus with judgments of the form

    { P } s { Q }        (a "Hoare triple")

    P - a precondition, a logical formula
    Q - a postcondition, a logical formula
    s - a statement

Intended meaning:
If we run s in a state σ such that P σ (σ satisfies the precondition)
and s terminates in state σ′, then Q σ′ (σ' satisfies the postcondition)


```
infixl 4 _∧∧_

Pred : Set → Set₁
Pred A = A → Set

𝕋 : ∀ {A : Set} → Pred A
𝕋 a = ⊤

_⇒_ : ∀ {A : Set } → Pred A → Pred A → Set
P ⇒ Q = ∀ a → P a → Q a

_∧∧_ : ∀ {A : Set} → Pred A → Pred A → Pred A
P ∧∧ Q = λ a → P a × Q a

Q⇒Q : ∀ {A : Set}{Q : Pred A} → Q ⇒ Q
Q⇒Q = λ a x → x
```

Hoare triples written as `⟪ P ⟫ s ⟪ Q ⟫`
where P and Q are semantic predicates of type `Pred State`.

```
TRUE : Bool → Set
TRUE b = b ≡ true
FALSE : Bool → Set
FALSE b = b ≡ false

data ⟪_⟫_⟪_⟫ : Pred State → Stmt → Pred State → Set₁ where

  H-Skp : ∀ {P} →
    ⟪ P ⟫ Skp ⟪ P ⟫

  H-Ass : ∀ {Q x e} →
    ⟪ (λ σ → Q (update x (𝓔⟦ e ⟧ σ) σ)) ⟫ (Ass x e) ⟪ Q ⟫

  H-Ite : ∀ {P Q b s₁ s₂} →
    ⟪ P ∧∧ TRUE ∘ 𝓑⟦ b ⟧ ⟫ s₁ ⟪ Q ⟫ →
    ⟪ P ∧∧ FALSE ∘ 𝓑⟦ b ⟧ ⟫ s₂ ⟪ Q ⟫ →
    ----------------------------------------------
    ⟪ P ⟫ (Ite b s₁ s₂) ⟪ Q ⟫

  H-Whl : ∀ {P b s} →
    ⟪ P ∧∧ TRUE ∘ 𝓑⟦ b ⟧ ⟫ s ⟪ P ⟫ →
    --------------------------------------------------
    ⟪ P ⟫ (Whl b s) ⟪ P ∧∧ FALSE ∘ 𝓑⟦ b ⟧ ⟫

  H-Seq : ∀ {P Q R s₁ s₂} →
    ⟪ P ⟫ s₁ ⟪ Q ⟫ →
    ⟪ Q ⟫ s₂ ⟪ R ⟫ →
    ----------------------
    ⟪ P ⟫ (Seq s₁ s₂) ⟪ R ⟫

  H-Wea : ∀ {P₁ P₂ Q₁ Q₂ s} →
    P₁ ⇒ P₂ → ⟪ P₂ ⟫ s ⟪ Q₁ ⟫ → Q₁ ⇒ Q₂ →
    ------------------------------------
    ⟪ P₁ ⟫ s ⟪ Q₂ ⟫
```

### Some example verifications

```
module Example where
  _is_ : Ident → ℕ → Pred State
  (x is n) σ = σ x ≡ n
  
  hoare1 : ⟪ 𝕋 ⟫
           example1
           ⟪ "x" is 42 ⟫
  hoare1 = H-Wea (λ σ x → refl) H-Ass Q⇒Q

  lemma3 : ∀ n → (0 <ᵇ n) ≡ false → n ≡ 0
  lemma3 zero ¬0<n = refl

  hoare3 : ⟪ 𝕋 ⟫
           example3
           ⟪ "x" is 0 ⟫
  hoare3 = H-Wea{P₂ = λ σ → (0 ≤ᵇ σ "x") ≡ true} (λ σ _ → refl)
             (H-Whl
               (H-Wea{Q₁ = 𝕋} (λ{ σ (refl , x) → tt})
                 H-Ass
                 λ σ x → refl))
             λ{ σ (refl , ¬0<x) → lemma3 (σ "x") ¬0<x}

  lemma0 : ∀ m n → (m <ᵇ suc n) ≡ true → (m ≤ᵇ n) ≡ true
  lemma0 zero n m<1+n = refl
  lemma0 (suc m) n m<1+n = m<1+n

  lemma : ∀ m n → (m ≤ᵇ n) ≡ true × (m <ᵇ n) ≡ false → m ≡ n
  lemma zero zero x = refl
  lemma zero (suc n) ()
  lemma (suc m) (suc n) (m<1+n , ¬m<n) = cong suc (lemma m n (lemma0 m n m<1+n , ¬m<n))

  prog : Stmt                                     -- ⟪ x <= 5 ⟫
  prog = Whl ((` "x") ⟨ _<ᵇ_ ⟩ (`# 5) )           --   while x < 5 { x = x + 1 }
           (Ass "x" ((`# 1) ⟨ _+_ ⟩ (` "x")))     -- ⟪ x = 5 ⟫

  hoare : ⟪ (λ σ → (σ "x" ≤ᵇ 5) ≡ true) ⟫
            prog
          ⟪ "x" is 5 ⟫
  hoare = H-Wea Q⇒Q
                (H-Whl {P = λ σ → (σ "x" ≤ᵇ 5) ≡ true}
                  (H-Wea (λ a (x≤5 , x<5) → x<5)
                         H-Ass
                         Q⇒Q))
                λ{ σ → lemma (σ "x") 5 }
```


### Denotational semantics of statements

The denotation of a statement is a state transformer, i.e., a function τ : State → State

```
module unsafe where
  postulate
    fix : ∀ {A : Set} → (A → A) → A

  ite : ∀ {A B : Set} → (A → Bool) → (A → B) → (A → B) → (A → B)
  ite fb ft ff = λ a → if (fb a) then (ft a) else (ff a)

  𝓢′⟦_⟧ : Stmt → State → State
  𝓢′⟦ Skp ⟧          = id
  𝓢′⟦ Ass x e ⟧      = λ σ → update x (𝓔⟦ e ⟧ σ) σ
  𝓢′⟦ Ite b s₁ s₂ ⟧  = ite (𝓑⟦ b ⟧) (𝓢′⟦ s₁ ⟧) (𝓢′⟦ s₂ ⟧)
  𝓢′⟦ Whl b s ⟧      = fix (λ f → ite (𝓑⟦ b ⟧) (f ∘ 𝓢′⟦ s ⟧) id)
  𝓢′⟦ Seq s₁ s₂ ⟧    = 𝓢′⟦ s₂ ⟧ ∘ 𝓢′⟦ s₁ ⟧
```

This attempt requires an unsafe postulate to complete the case for while,
because Agda does not let us use general recursion (aka `fix`)
which would be needed to define the semantics of while.
For this reason, the definition does not compute.

If we are not interested in diverging while programs, then we can get useful results by restricting
ourselves to arbitrary, finite numbers of unrolling of while statments.

Trick: instead of returning State, we return a function of type `ℕ → Maybe State`
Interpretation:
The number (gas) bounds the number of iterations of any nesting of while loops in the program.
If we run out of gas, then we return `nothing`.

Technically, we move the computation into a monad, which is a combination of `Maybe` and reader monads.
Preparation: return and bind operator for the Maybe monad

```
return : ∀ {A : Set} → A → Maybe A
return a = just a

_⟫=_ : ∀ {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
(m ⟫= f)
  with m
... | nothing = nothing
... | just a  = f a

-- if the result of a bind is `just`, then its first argument must be a `just`
maybe-just : ∀ {A B : Set} (m : Maybe A) {f : A → Maybe B} {x : B} → m ⟫= f ≡ just x → ∃[ y ] m ≡ just y
maybe-just (just y) mf=jx = y , refl
```



We write the denotational semantics

Compositional version (after lecture)

```
module compositional where
  Comp : Set → Set
  Comp X = ℕ → State → Maybe X

  -- a custom, indexed fixed point operator for loops
  mfix : ((State → Maybe State) → ℕ → State → Maybe State) → Comp State
  mfix f zero σ = nothing
  mfix f (suc i) σ = f (mfix f i) i σ

  mfix-just : ∀ {f} σ i σ′ → mfix f i σ ≡ just σ′ → ∃[ j ] i ≡ suc j
  mfix-just σ (suc i) σ′ mfix≡ = i , refl

  𝓢⟦_⟧ : Stmt → ℕ → State → Maybe State
  𝓢⟦ Skp         ⟧ i σ = return σ
  𝓢⟦ Ass x e     ⟧ i σ = return (update x (𝓔⟦ e ⟧ σ) σ)
  𝓢⟦ Ite b s₁ s₂ ⟧ i σ  = if 𝓑⟦ b ⟧ σ then 𝓢⟦ s₁ ⟧ i σ else 𝓢⟦ s₂ ⟧ i σ
  𝓢⟦ Whl b s     ⟧ i σ = mfix (λ f i σ → if (𝓑⟦ b ⟧ σ) then (𝓢⟦ s ⟧ i σ) ⟫= f else return σ) i σ
  𝓢⟦ Seq s₁ s₂   ⟧ i σ = 𝓢⟦ s₁ ⟧ i σ ⟫= 𝓢⟦ s₂ ⟧ i

  hoare-soundness : ∀ {P Q s} →
    ⟪ P ⟫ s ⟪ Q ⟫ →
    ∀ σ → P σ → ∀ i → ∀ σ′ → 𝓢⟦ s ⟧ i σ ≡ just σ′ → Q σ′

  mfix-soundness : ∀ {b}{s}{P : Pred State} σ i σ′
    → (pre : P σ)
    → (mfix≡ : mfix (λ f i σ → if 𝓑⟦ b ⟧ σ then (𝓢⟦ s ⟧ i σ ⟫= f) else just σ) i σ ≡ just σ′)
    → (loop-inv : ∀ σ → P σ × 𝓑⟦ b ⟧ σ ≡ true → ∀ i σ′ → 𝓢⟦ s ⟧ i σ ≡ just σ′ → P σ′)
    → P σ′ × 𝓑⟦ b ⟧ σ′ ≡ false

  mfix-soundness {b}{s}{P} σ i σ′ Pσ mfix≡ loop-inv
    with j , refl ← mfix-just σ i σ′ mfix≡
    with 𝓑⟦ b ⟧ σ in eq-b
  mfix-soundness {b} {s} {P} σ .(suc j) σ′ Pσ refl loop-inv | false = Pσ , eq-b
  ... | true 
    with σ″ , 𝓢⟦s⟧ ← maybe-just (𝓢⟦ s ⟧ j σ) mfix≡
    rewrite 𝓢⟦s⟧
    using Pσ″ ← loop-inv σ (Pσ , eq-b) j σ″ 𝓢⟦s⟧
    = mfix-soundness {b}{s}{P} σ″ j σ′ Pσ″ mfix≡ loop-inv

  hoare-soundness H-Skp σ P i σ′ refl = P
  hoare-soundness H-Ass σ P i σ′ refl = P
  hoare-soundness (H-Ite {b = b} 𝓗 𝓗₁) σ P i σ′ v≡
    with 𝓑⟦ b ⟧ σ in eq-b
  ... | true = hoare-soundness 𝓗 σ (P , eq-b) i σ′ v≡
  ... | false = hoare-soundness 𝓗₁ σ (P , eq-b) i σ′ v≡
  hoare-soundness (H-Whl {b = b}{s = s} 𝓗) σ P i σ′ v≡
    with hoare-soundness 𝓗
  ... | ih = mfix-soundness {b = b}{s = s} σ i σ′ P v≡ ih
  hoare-soundness (H-Seq {s₁ = s₁}{s₂ = s₂} 𝓗 𝓗₁) σ P i σ′ v≡
    with σ″ , eq″ ← maybe-just (𝓢⟦ s₁ ⟧ i σ) v≡
    rewrite eq″
    with hoare-soundness 𝓗 σ P i σ″ eq″
  ... | Qσ″
    = hoare-soundness 𝓗₁ σ″ Qσ″ i σ′ v≡
  hoare-soundness (H-Wea P₁⇒P₂ 𝓗 Q₁⇒Q₂) σ P i σ′ v≡ =
    Q₁⇒Q₂ σ′ (hoare-soundness 𝓗 σ (P₁⇒P₂ σ P) i σ′ v≡)


  -- auxiliary lemmas for soundness

  -- monotonicity of the denotational semantics
  -- once we have a result, it remains stable if we give more gas
  𝓢-step : ∀ {i} σ s σ' →
    𝓢⟦ s ⟧ i σ ≡ just σ' →
    𝓢⟦ s ⟧ (suc i) σ ≡ just σ'

  mfix-step : ∀ b s i σ σ′ →
    mfix (λ f i₁ σ₁ → if 𝓑⟦ b ⟧ σ₁ then (𝓢⟦ s ⟧ i₁ σ₁ ⟫= f) else just σ₁) i σ ≡ just σ′ →
    mfix (λ f i₁ σ₁ → if 𝓑⟦ b ⟧ σ₁ then (𝓢⟦ s ⟧ i₁ σ₁ ⟫= f) else just σ₁) (suc i) σ ≡ just σ′
  mfix-step b s (suc i) σ σ′ mfix≡
    with 𝓑⟦ b ⟧ σ
  ... | false = mfix≡
  ... | true
    with σ″ , eq″ ← maybe-just (𝓢⟦ s ⟧ i σ) mfix≡
    rewrite 𝓢-step σ s σ″ eq″
    rewrite eq″
    = mfix-step b s i σ″ σ′ mfix≡

  𝓢-step σ Skp σ' eq = eq
  𝓢-step σ (Ass x e) σ' eq = eq
  𝓢-step σ (Ite b s s₁) σ' eq
    with 𝓑⟦ b ⟧ σ
  ... | true = 𝓢-step σ s σ' eq
  ... | false = 𝓢-step σ s₁ σ' eq
  𝓢-step {i} σ (Whl b s) σ' eq = mfix-step b s i σ σ' eq
  𝓢-step {i} σ (Seq s s₁) σ' eq
    with σ″ , eq-1 ← maybe-just (𝓢⟦ s ⟧ i σ) eq
    rewrite 𝓢-step σ s σ″ eq-1
    rewrite eq-1
    = 𝓢-step σ″ s₁ σ' eq

  -- soundness of small-step semantics (WIP)

  soundness : ∀ {σ₁ s₁ σ₂ s₂} →
    (σ₁ , s₁) —→ (σ₂ , s₂) →
    ∀ i → ∀ σ → 𝓢⟦ s₁ ⟧ i σ₁ ≡ just σ → 𝓢⟦ s₂ ⟧ i σ₂ ≡ just σ
  soundness Ass→ i σ 𝓢⟦s₁⟧ = 𝓢⟦s₁⟧
  soundness (Ite→₁ 𝓑⟦b⟧≡true) i σ 𝓢⟦s₁⟧ rewrite 𝓑⟦b⟧≡true = 𝓢⟦s₁⟧
  soundness (Ite→₂ 𝓑⟦b⟧≡false) i σ 𝓢⟦s₁⟧ rewrite 𝓑⟦b⟧≡false = 𝓢⟦s₁⟧
  soundness {σ₁ = σ₁} (Whl→ {b = b}{s = s}) i σ 𝓢⟦s₁⟧
    with j , refl ← mfix-just σ₁ i σ 𝓢⟦s₁⟧
    with 𝓑⟦ b ⟧ σ₁
  ... | false = 𝓢⟦s₁⟧
  ... | true
    with σ″ , eq″ ← maybe-just (𝓢⟦ s ⟧ j σ₁) 𝓢⟦s₁⟧
    rewrite 𝓢-step σ₁ s σ″ eq″
    rewrite eq″
    = {!!}
  soundness {σ₁ = σ₁} (Seq→₁ {s₁ = s₁} r) i σ 𝓢⟦s₁⟧
    with σ″ , eq ← maybe-just (𝓢⟦ s₁ ⟧ i σ₁) 𝓢⟦s₁⟧
    rewrite eq
    rewrite soundness r i σ″ eq
    = 𝓢⟦s₁⟧  
  soundness Seq→₂ i σ 𝓢⟦s₁⟧ = 𝓢⟦s₁⟧

  completeness : ∀ i s σ σ′ →
    𝓢⟦ s ⟧ i σ ≡ just σ′ →
    (σ , s) ⇓ σ′
  completeness i Skp σ σ′ refl = done
  completeness i (Ass x e) σ σ′ refl = step Ass→ done
  completeness i (Ite b s s₁) σ σ′ eq
    with 𝓑⟦ b ⟧ σ in eq-b
  ... | true = step (Ite→₁ eq-b) (completeness i _ σ σ′ eq)
  ... | false = step (Ite→₂ eq-b) (completeness i _ σ σ′ eq)
  completeness i (Whl b s) σ σ′ eq = {!!}
  completeness i (Seq s s₁) σ σ′ eq
    with σ″ , eq″ ← maybe-just (𝓢⟦ s ⟧ i σ) eq
    rewrite eq″
    = ⇓-trans (completeness i s σ σ″ eq″) (completeness i s₁ σ″ σ′ eq)
```

Non-compositional version from the lecture :-(

```
𝓢⟦_⟧ : Stmt → ℕ → State → Maybe State
𝓢⟦ s           ⟧ zero    σ = nothing
𝓢⟦ Skp         ⟧ (suc i) σ = return σ
𝓢⟦ Ass x e     ⟧ (suc i) σ = return (update x (𝓔⟦ e ⟧ σ) σ)
𝓢⟦ Ite b s₁ s₂ ⟧ (suc i) σ  = if 𝓑⟦ b ⟧ σ then 𝓢⟦ s₁ ⟧ i σ else 𝓢⟦ s₂ ⟧ i σ
𝓢⟦ Whl b s     ⟧ (suc i) σ = 𝓢⟦ Ite b (Seq s (Whl b s)) Skp ⟧ i σ
𝓢⟦ Seq s₁ s₂   ⟧ (suc i) σ = 𝓢⟦ s₁ ⟧ i σ ⟫= 𝓢⟦ s₂ ⟧ i
```

```
lem' : ∀ i σ σ′ → 𝓢⟦ Skp ⟧ i σ ≡ just σ′ → σ ≡ σ′
lem' (suc i) σ σ′ refl = refl

hoare-soundness : ∀ {P Q s} →
  ⟪ P ⟫ s ⟪ Q ⟫ →
  ∀ σ → P σ → ∀ i → ∀ σ′ → 𝓢⟦ s ⟧ i σ ≡ just σ′ → Q σ′
hoare-soundness H-Skp          σ Pσ (suc i) .σ refl = Pσ
hoare-soundness H-Ass          σ Pσ (suc i) σ′ refl = Pσ
hoare-soundness (H-Ite {b = b} H₁ H₂)  σ Pσ (suc i) σ′ eq with 𝓑⟦ b ⟧ σ in eq-b
...                                                          | true  = hoare-soundness H₁ σ (Pσ , eq-b) i σ′ eq
...                                                          | false = hoare-soundness H₂ σ (Pσ , eq-b) i σ′ eq
hoare-soundness (H-Whl {b = b} {s = s} H)      σ Pσ (suc (suc i)) σ′ eq
 with 𝓑⟦ b ⟧ σ in eq-b
... | false rewrite sym (lem' i σ σ′ eq) = Pσ , eq-b
... | true
 with i
... | suc i
 with 𝓢⟦ s ⟧ i σ in eq-s
... | just σ′′
 with hoare-soundness H σ (Pσ , eq-b) i σ′′ eq-s
... | Pσ′′
 = hoare-soundness (H-Whl H) σ′′ Pσ′′ i σ′ eq
hoare-soundness (H-Seq {s₁ = s₁} {s₂ = s₂} H₁ H₂)  σ Pσ (suc i) σ′ eq₂
 with 𝓢⟦ s₁ ⟧ i σ in eq₁
... | just σ′′ = let Pσ′′ = hoare-soundness H₁ σ Pσ i σ′′ eq₁
                 in hoare-soundness H₂ σ′′ Pσ′′ i σ′ eq₂
hoare-soundness (H-Wea pre H post) σ Pσ (suc i) σ′ eq = post σ′ (hoare-soundness H σ (pre σ Pσ) (suc i) σ′ eq)
```

Properties of the denotational semantics

```
𝓢-has-steps : ∀ i s {σ} {σ′} → 𝓢⟦ s ⟧ i σ ≡ just σ′ → ∃[ j ] i ≡ suc j
𝓢-has-steps (suc i) s ss= = i , refl

𝓢-suc : ∀ {i} σ s σ' →
  𝓢⟦ s ⟧ i σ ≡ just σ' →
  𝓢⟦ s ⟧ (suc i) σ ≡ just σ'
𝓢-suc {i = suc i} σ Skp σ' eq = eq
𝓢-suc {i = suc i} σ (Ass x e) σ' eq = eq
𝓢-suc {i = suc i} σ (Ite b s s₁) σ' eq
  with 𝓑⟦ b ⟧ σ
... | true = 𝓢-suc σ s σ' eq
... | false = 𝓢-suc σ s₁ σ' eq
𝓢-suc {i = suc i} σ (Whl b s) σ' eq
  with j , refl ← 𝓢-has-steps i (Ite b (Seq s (Whl b s)) Skp) eq
  with 𝓑⟦ b ⟧ σ in eq-b
... | false
  with  j′ , refl ← 𝓢-has-steps j Skp eq
  = eq

... | true
  with j′ , refl ← 𝓢-has-steps j (Seq s (Whl b s)) eq
  with σ″ , eq″ ← maybe-just (𝓢⟦ s ⟧ j′ σ) eq
  rewrite 𝓢-suc {j′} σ s σ″ eq″
  = {!!}
𝓢-suc {i = suc i} σ (Seq s s₁) σ' eq
  with maybe-just (𝓢⟦ s ⟧ i σ) eq
... | σ″ , eq′
  rewrite 𝓢-suc{i} σ s σ″ eq′
  rewrite eq′ = 𝓢-suc {i} σ″ s₁ σ' eq

𝓢-≤  : ∀ {i j} σ s σ' →
  i ≤′ j →
  𝓢⟦ s ⟧ i σ ≡ just σ' →
  𝓢⟦ s ⟧ j σ ≡ just σ'
𝓢-≤ {i = i} {j = j} σ s σ' (_≤′_.≤′-reflexive refl) eq = eq
𝓢-≤ {i = i} {j = j} σ s σ' (_≤′_.≤′-step i≤j) eq = 𝓢-suc σ s σ' (𝓢-≤ σ s _ i≤j eq)

𝓢-mono : ∀ s i σ →
  𝓢⟦ s ⟧ i σ ≡ nothing ⊎ 𝓢⟦ s ⟧ i σ ≡ 𝓢⟦ s ⟧ (suc i) σ
𝓢-mono s i σ with 𝓢⟦ s ⟧ i σ in eq
... | nothing = inj₁ refl
... | just σ' = inj₂ (sym (𝓢-suc σ s σ' eq))
```

Soundness of the operational semantics


```
soundness : ∀ {σ₁ s₁ σ₂ s₂} →
  (σ₁ , s₁) —→ (σ₂ , s₂) →
  ∀ i → ∀ σ → 𝓢⟦ s₁ ⟧ i σ₁ ≡ just σ → 𝓢⟦ s₂ ⟧ i σ₂ ≡ just σ
soundness r zero σ ()
soundness Ass→ (suc i) σ eq = eq
soundness (Ite→₁ {s₁ = s₁} b=true) (suc i) σ eq rewrite b=true = 𝓢-suc {i} _ s₁ σ eq 
soundness (Ite→₂ {s₂ = s₂} b=false) (suc i) σ eq rewrite b=false = 𝓢-suc {i} _ s₂ σ eq
soundness Whl→ (suc i) = {!!}
soundness {σ₁ = σ₁} (Seq→₁ {s₁ = s₁} r) (suc i) σ eq
  with σ′ , eq′ ← maybe-just (𝓢⟦ s₁ ⟧ i σ₁) eq
  rewrite soundness r i σ′ eq′
  rewrite eq′
  = eq
soundness {σ₁ = σ₁} (Seq→₂ {s₂ = s₂}) (suc i) σ eq
  with σ′ , eq′ ← maybe-just (𝓢⟦ Skp ⟧ i σ₁) eq
  rewrite eq′
  with j , refl ← 𝓢-has-steps i Skp eq′
  with eq′
... | refl = 𝓢-suc {i} σ₁ s₂ σ eq

completeness : ∀ {i} {s}{σ}{σ′} →
  𝓢⟦ s ⟧ i σ ≡ just σ′ →
  (σ , s) ⇓ σ′
completeness {i = i} {s = s} eq = {!!}
