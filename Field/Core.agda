module Field.Core where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality

data ⊥ : Set where

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

record Field (ℓ : Level) : Set (lsuc ℓ) where
  field
    Carrier : Set ℓ

    _＋_     : Carrier → Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    _⁻¹     : Carrier → Carrier

    0#      : Carrier
    1#      : Carrier

    ＋-comm  : ∀ a b → a ＋ b ≡ b ＋ a
    ＋-assoc : ∀ a b c → (a ＋ b) ＋ c ≡ a ＋ (b ＋ c)
    ＋-zero  : ∀ a → a ＋ 0# ≡ a
    ＋-inv   : ∀ a → a ＋ (- a) ≡ 0#

    ·-comm  : ∀ a b → a · b ≡ b · a
    ·-assoc : ∀ a b c → (a · b) · c ≡ a · (b · c)
    ·-id    : ∀ a → a · 1# ≡ a
    ·-inv   : ∀ {a} → (a ≡ 0# → ⊥) → a · (a ⁻¹) ≡ 1#

    distr   : ∀ a b c → (a ＋ b) · c ≡ (a · c) ＋ (b · c)


open Field

-- char : ∀ {ℓ : Level} → Field ℓ → N
-- char F = {!!}

-- FieldChar : ∀ {ℓ : Level} → Field ℓ → {n : N} → ∀ {x₀ : Carrier} → ∑ (λ x → x₀) 0 n ≡ 0
