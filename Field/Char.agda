open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality as A
open A.≡-Reasoning

open import Nat.Core
open import Field.Core
open import Field.Sum
open import Field.Numerals

module Field.Char {ℓ : Level} (F : Field ℓ) where

  open Field.Core.Field F
  
  is-char-el : (n : ℕ) → (x₀ : Carrier) → Set ℓ
  is-char-el n x₀ = x₀ · n ≡ 0
  
  -- char-exists : (x : Carrier) → (n : ℕ) → ∑ F x n ≡ 0#
  -- char-exists x n = ∑ F x n ≡ 0#
  
  
  -- char-is-prime : (n m : ℕ) → (x₀ : Carrier) → ∑ F x₀ n ≡ 0#

