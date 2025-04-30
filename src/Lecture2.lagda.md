```
module Lecture2 where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
```

## Notes for chapter "Induction"


Towards proving commutativity of addition, we need two lemmas.

Instead of using `rewrite` we write equality proofs using equational reasoning (a convenient notation).

```
+-identityʳ : ∀ m → m + zero ≡ m
+-identityʳ = {!!}
```

```
+-suc : ∀ m n → m + suc n ≡ suc m + n
+-suc m n = {!!}
```

```
+-comm : ∀ m n → m + n ≡ n + m
+-comm = {!!}
```

Selected exercises

```
+-swap : ∀ m n p → m + (n + p) ≡ n + (m + p)
+-swap = {!!}
```


```
*-distrib-+ : ∀ m n p → (m + n) * p ≡ m * p + n * p
*-distrib-+ = {!!}
```



## Notes for chapter "Relations"

Let's define `≤` on natural numbers!


