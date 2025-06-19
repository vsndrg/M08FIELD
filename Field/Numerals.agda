open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality

open import Nat.Core
open import Field.Core

module Field.Numerals {ℓ : Level} (F : Field ℓ) where

  open Field.Core.Field F

  -- Mapping natural number to a field element function.
  -- ARGUMENTS:
  --   - natural number to map:
  --       n : ℕ
  -- RETURNS:
  --   (Carrier) a field element connected with n.
  --
  n# : (n : ℕ) → Carrier
  n# 0 = 0#
  n# (suc n) = n# n +# 1#

  -- Multlply field element by natural number operator.
  -- ARGUMENS:
  --   - natural number to multiply
  --       n : ℕ
  -- RETURNS:
  --   (Carrier) result of multiplication - field element.
  --
  infixl 7 _·_
  _·_ : (x : Carrier) → (n : ℕ) → Carrier
  _·_ x n = x *# n# n
