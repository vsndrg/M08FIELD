open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality as A
open A.≡-Reasoning

open import Nat.Core
open import Field.Core
open import Field.Numerals

module Field.Char {ℓ : Level} (F : Field ℓ) where

  open Field.Core.Field F
  
  is-char-el : (x₀ : Carrier) → (n : ℕ) → Set ℓ
  is-char-el x₀ n = x₀ · n ≡ 0#
  
  -- char-exists : (x : Carrier) → (n : ℕ) → ∑ F x n ≡ 0#
  -- char-exists x n = ∑ F x n ≡ 0#
  
  
  -- char-is-prime : (n m : ℕ) → (x₀ : Carrier) → ∑ F x₀ n ≡ 0#

