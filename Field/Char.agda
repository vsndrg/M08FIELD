open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality

open import Field.Core
open import Field.Sum
open import Nat.Core

module Field.Char {ℓ : Level} (F : Field ℓ) where

open Field.Core.Field F

char-is-prime : (n : ℕ) → (x₀ : Carrier) → ∑ x₀ n ≡ 0#
