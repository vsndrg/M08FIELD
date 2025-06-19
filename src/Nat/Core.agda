module Nat.Core where
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
_+_ 0 x = x
_+_ (suc y) x = suc (y + x)

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
_*_ 0 x = 0
_*_ (suc y) x = x + y * x

infixl 8 _^_
_^_ : ℕ → ℕ → ℕ
_^_ a 0 = 1
_^_ a (suc n) = a * a ^ n

open import Relation.Binary.PropositionalEquality as A
open A.≡-Reasoning

plus-zero : (x : ℕ) → x + 0 ≡ x
plus-zero 0 = refl
plus-zero (suc x) = 
  begin
    suc x + 0 ≡⟨⟩ suc (x + 0)
    ≡⟨ cong suc (plus-zero x) ⟩ suc x
  ∎

add-assoc : (a b c : ℕ) → a + (b + c) ≡ a + b + c
add-assoc 0 b c = refl
add-assoc (suc a) b c = cong suc (add-assoc a b c)

plus-suc : (a b : ℕ) → a + suc b ≡ suc (a + b)
plus-suc 0 b = refl
plus-suc (suc a) b = cong suc (plus-suc a b)

add-comm : (a b : ℕ) → a + b ≡ b + a
add-comm 0 b = sym (plus-zero b)
add-comm (suc a) b =
  begin
    suc a + b
   ≡⟨ cong suc (add-comm a b) ⟩ suc (b + a)
   ≡⟨ sym (plus-suc b a) ⟩ b + suc a
  ∎

mul-zero : (a : ℕ) → a * 0 ≡ 0
mul-zero 0 = refl
mul-zero (suc a) = mul-zero a

mul-one : (a : ℕ) → a * 1 ≡ a
mul-one 0 = refl
mul-one (suc a) =
  begin
    (suc a) * 1
    ≡⟨⟩ 1 + a * 1
    ≡⟨ cong (λ x → 1 + x) (mul-one a) ⟩ 1 + a
    ≡⟨⟩ (suc a)
  ∎

distr-left : (a b c : ℕ) → a * b + a * c ≡ a * (b + c)
distr-left 0 b c = refl
distr-left (suc a) b c =
  begin
    suc a * b + suc a * c
    ≡⟨⟩ b + a * b + (c + a * c)
    ≡⟨ add-assoc (b + a * b) c (a * c) ⟩ b + a * b + c + a * c
    ≡⟨ cong (λ x → x + a * c) (sym (add-assoc b (a * b) c)) ⟩ b + (a * b + c) + a * c
    ≡⟨ cong (λ x → b + x + a * c) (add-comm (a * b) c) ⟩ b + (c + a * b) + a * c
    ≡⟨ cong (λ x → x + a * c) (add-assoc b c (a * b)) ⟩ b + c + a * b + a * c
    ≡⟨ sym (add-assoc (b + c) (a * b) (a * c)) ⟩ b + c + (a * b + a * c)
    ≡⟨ cong (λ x → b + c + x) (distr-left a b c) ⟩ b + c + a * (b + c)
    ≡⟨⟩ (suc a) * (b + c)
  ∎  


{-
mul-comm : (a b : ℕ) → a * b ≡ b * a
mul-comm 0 b = sym (mul-zero b)
mul-comm (suc a) b =
  begin
    suc a * b ≡⟨⟩ b + a * b ≡⟨ ? ⟩ b * suc a
  ∎

mul-assoc : (a b c : ℕ) → a * b * c ≡ a * (b * c)
mul-assoc 0 b c = refl
mul-assoc (suc a) b c =
  begin
    suc a * b * c ≡⟨⟩ (b + a * b) * c ≡⟨ ? ⟩ suc a * (b * c)
  ∎
-}

