open import Field.Core

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality

module Field.Sum {ℓ : Level} (F : Field ℓ) where

open import Nat.Core
open Field.Core.Field F

∑ : (el : Carrier) → (n : ℕ) → Carrier
∑ el 0 = 0#
∑ el (suc n) = ∑ el n ＋ el

