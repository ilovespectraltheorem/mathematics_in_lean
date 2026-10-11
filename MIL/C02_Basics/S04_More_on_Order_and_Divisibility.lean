import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  show min a b ≤ min b a
  apply le_min
  apply min_le_right
  apply min_le_left
  show min b a ≤ min a b
  apply le_min
  apply min_le_right
  apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  have h : ∀ x y : ℝ, max x y ≥ max y x := by
    intro x y
    apply max_le
    apply le_max_right
    apply le_max_left
  apply le_antisymm
  apply h
  apply h

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  apply le_min
  have h : min (min a b) c ≤ min a b := by
    apply min_le_left
  have h₁ : min a b ≤ a := by
    apply min_le_left
  apply le_trans h h₁
  apply le_min
  have h : min (min a b) c ≤ min a b := by
    apply min_le_left
  have h₂ : min a b ≤ b := by
    apply min_le_right
  apply le_trans h h₂
  apply min_le_right
  apply le_min
  apply le_min
  apply min_le_left
  have h : min a (min b c) ≤ min b c := by
    apply min_le_right
  have h₃ : min b c ≤ b := by
    apply min_le_left
  apply le_trans h h₃
  have h : min a (min b c) ≤ min b c := by
    apply min_le_right
  have h₄ : min b c ≤ c := by
    apply min_le_right
  apply le_trans h h₄



theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  apply add_le_add_left
  apply min_le_left
  apply add_le_add_left
  apply min_le_right

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  apply aux
  have h: min (a+c) (b+c) -c + c ≤ min a b + c := by
    apply add_le_add_left
    simpa only [sub_eq_add_neg, add_neg_cancel_right] using aux (a+c) (b+c) (-c)
  linarith [h]

#check (abs_add_le : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

#check (add_sub_cancel_right)
#check (sub_add_cancel)

example : |a| - |b| ≤ |a - b| := by
  nth_rewrite 1[← sub_add_cancel a b]
  linarith [abs_add_le (a-b) b]
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  apply dvd_add
  apply dvd_mul_of_dvd_right
  apply dvd_mul_right
  apply dvd_mul_left
  have h₁: w ∣ w^2 := by
    apply dvd_mul_left
  apply dvd_trans h h₁
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply dvd_antisymm
  apply Nat.dvd_gcd
  exact Nat.gcd_dvd_right m n
  exact Nat.gcd_dvd_left m n
  apply Nat.dvd_gcd
  exact Nat.gcd_dvd_right n m
  exact Nat.gcd_dvd_left n m
end
