import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace C03S04

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  intro h
  apply h₁
  rw [h]

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  ⟨h₀, fun h ↦ h₁ (by rw [h])⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  have h : x ≠ y := by
    contrapose! h₁
    rw [h₁]
  ⟨h₀, h⟩

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩ h'
  exact h₁ (le_antisymm h₀ h')

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x :=
  fun ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  case intro h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  next h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  match h with
    | ⟨h₀, h₁⟩ =>
        contrapose! h₁
        exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro h'
  apply h.right
  exact le_antisymm h.left h'

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  constructor
  rcases h with ⟨h1, h2⟩
  exact h1
  rcases h with ⟨h1, h2⟩
  intro h
  rcases h1 with ⟨k, hk⟩
  rcases h with ⟨l, hl⟩
  contrapose! h2
  by_cases hn: n = (0: ℕ)
  . rw[hn] at hl
    rw[zero_mul] at hl
    rw[hl, hn]
  . rw[hl] at hk
    nth_rewrite 1[← mul_one n] at hk
    rw[mul_assoc] at hk
    apply mul_left_cancel₀ hn at hk
    symm at hk
    have hl1 := Nat.eq_one_of_mul_eq_one_right hk
    rw[hl1, mul_one] at hl
    exact hl

#check mul_left_cancel₀

example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
  ⟨5 / 2, by norm_num, by norm_num⟩

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
  fun ⟨_z, xltz, zlty⟩ ↦ lt_trans xltz zlty

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  constructor <;> norm_num

example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  norm_num

example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩
  use h₀
  exact fun h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl
    rfl
  contrapose!
  exact le_antisymm h

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h₀ h₁ ↦ h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  intro h
  rcases h with ⟨h1, h2⟩
  constructor
  exact h1
  contrapose! h2
  rw[h2]
  intro h
  rcases h with ⟨h1, h2⟩
  constructor
  exact h1
  contrapose! h2
  apply le_antisymm h1 h2

theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by
    have h1: 0 ≤ y ^ 2 := by apply sq_nonneg y
    by_contra h2
    have h3: 0 ≤ x ^ 2 := by apply sq_nonneg x
    change x ^ 2 ≠ 0 at h2
    have hpos : 0 < x ^ 2 := lt_of_le_of_ne h3 (Ne.symm h2)
    have hsum := add_lt_add_of_lt_of_le hpos h1
    rw[zero_add] at hsum
    rw[h] at hsum
    exact (lt_irrefl 0) hsum
  eq_zero_of_pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  intro h
  have h1: x = 0 := by apply aux h
  constructor
  exact h1
  rw[h1] at h
  simp at h
  exact h
  intro h
  rcases h with ⟨h0, h1⟩
  rw[h0, h1]
  simp

section

example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith

example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor <;> norm_num

end

theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push_neg
  rfl

example : ¬Monotone fun x : ℝ ↦ -x := by
  intro h
  rw [Monotone] at h
  have h1: (0:ℝ) ≤ (1:ℝ) := by norm_cast
  have h2: (-0:ℝ) ≤ (-1:ℝ) := h h1
  simp at h2
  linarith

section
variable {α : Type*} [PartialOrder α]
variable (a b : α)

example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_ge]
  constructor
  intro h
  rcases h with ⟨h1, h2⟩
  constructor
  exact h1
  contrapose! h2
  rw[h2]
  intro h
  rcases h with ⟨h1, h2⟩
  constructor
  exact h1
  contrapose! h2
  apply le_antisymm h1 h2

end

section
variable {α : Type*} [Preorder α]
variable (a b c : α)

example : ¬a < a := by
  rw [lt_iff_le_not_ge]
  push_neg
  intro h
  exact h

example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_ge]
  intro h h1
  rcases h with ⟨h2, h3⟩
  rcases h1 with ⟨h4, h5⟩
  constructor
  apply le_trans h2 h4
  have h6: ¬b ≤ a ∨ ¬c ≥ b := by
    left
    exact h3
  contrapose! h6
  constructor
  apply le_trans h4 h6
  exact h4

end
