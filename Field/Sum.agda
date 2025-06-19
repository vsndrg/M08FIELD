open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality

open import Field.Core
open import Nat.Core

module Field.Sum {ℓ : Level} (F : Field ℓ) where

open Field.Core.Field F

∑ : (x : Carrier) → (n : ℕ) → Carrier
∑ x 0 = 0#
∑ x (suc n) = ∑ x n +# x

