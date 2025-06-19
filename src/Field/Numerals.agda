open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality

open import Nat.Core

open import Field.Core

module Field.Numerals {ℓ : Level} (F : Field.Core.Field ℓ) where

  open Field.Core.Field F public

  -- Mapping natural number to a field element function.
  -- ARGUMENTS:
  --   - natural number to map:
  --       n : ℕ
  -- RETURNS:
  --   (Carrier) a field element connected with n.
  --
  f : ℕ → Carrier
  f 0 = 0#
  f (suc n) = 1# +# (f n)

  -- Multlply field element by natural number operator.
  -- ARGUMENS:
  --   - natural number to multiply
  --       n : ℕ
  -- RETURNS:
  --   (Carrier) result of multiplication - field element.
  --
  infixl 7 _·_
  _·_ : Carrier → ℕ → Carrier
  _·_ x n = x *# (f n) 

