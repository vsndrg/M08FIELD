module Field.Core where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality
open import Nat.Core

-- Empty type definition.
-- ARGUMENTS: None
-- RETURNS:
--   (Set) universe.
--
data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

-- Field record type.
-- ARGUMENTS:
--   - universe where a Field lives:
--       ℓ : Level
-- RETURNS:
--   (Set (lsuc ℓ)) next level universe.
--
record Field (ℓ : Level) : Set (lsuc ℓ) where
  field
    Carrier  : Set ℓ

    _+#_     : Carrier → Carrier → Carrier
    _*#_      : Carrier → Carrier → Carrier
    -_       : Carrier → Carrier
    _⁻¹      : Carrier → Carrier

    0#       : Carrier
    1#       : Carrier

    +#-comm  : ∀ a b → a +# b ≡ b +# a
    +#-assoc : ∀ a b c → (a +# b) +# c ≡ a +# (b +# c)
    +#-zero  : ∀ a → a +# 0# ≡ a
    +#-inv   : ∀ a → a +# (- a) ≡ 0#

    *#-comm   : ∀ a b → a *# b ≡ b *# a
    *#-assoc  : ∀ a b c → (a *# b) *# c ≡ a *# (b *# c)
    *#-id     : ∀ a → a *# 1# ≡ a
    *#-inv    : ∀ {a} → (a ≡ 0# → ⊥) → a *# (a ⁻¹) ≡ 1#

    distr    : ∀ a b c → (a +# b) *# c ≡ (a *# c) +# (b *# c)

open Field

