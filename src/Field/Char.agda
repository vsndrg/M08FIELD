open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality
open import Relation.Binary.PropositionalEquality as A
open A.≡-Reasoning

open import Field.Core

module Field.Char {ℓ : Level} (F : Field.Core.Field ℓ) where

  open import Nat.Core
  open import Field.Numerals

  open Field.Core.Field F public
  
  is-char-el : Carrier → ℕ → Set ℓ
  is-char-el x₀ n = x₀ · n ≡ 0#
