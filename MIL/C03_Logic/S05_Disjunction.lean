import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h1 | h2
  rw [abs_of_nonneg h1]
  rw [abs_of_neg h2]
  linarith

theorem neg_le_abs (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h1 | h2
  rw [abs_of_nonneg h1]
  linarith
  rw [abs_of_neg h2]

-- the author's mental state is not well and he went crazy on this proof
theorem abs_add_le (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 x with h1 | h2
  rcases le_or_gt 0 y with h3 | h4
  have h5: 0 ≤ x + y := by linarith
  rw [abs_of_nonneg h1, abs_of_nonneg h3, abs_of_nonneg h5]
  rw[abs_of_nonneg h1, abs_of_neg h4]
  rcases le_or_gt x (-y) with h6 | h7
  have h8: x + y ≤ 0
  linarith
  rcases eq_or_ne (x + y) 0 with h | h
  rw[h]
  simp
  linarith
  have h9: (x + y) < 0 := by apply lt_of_le_of_ne h8 h
  rw[abs_of_neg h9]
  linarith
  have h10: (x + y) > 0 := by linarith
  have h11: (x + y) ≥ 0 := by apply le_of_lt h10
  rw [abs_of_nonneg h11]
  linarith
  rcases le_or_gt 0 y with h3 | h4
  rcases le_or_gt x (-y) with h6 | h7
  have h8: (x+y) ≤ 0 := by linarith
  rw[abs_of_nonpos h8]
  rw[abs_of_nonneg h3]
  rw[abs_of_neg h2]
  linarith
  have h9: (x + y) > 0 := by linarith
  have h10: (x+y) ≥ 0 := by apply le_of_lt h9
  rw[abs_of_nonneg h10]
  rw[abs_of_nonneg h3]
  rw[abs_of_neg h2]
  linarith
  rw[abs_of_neg h2, abs_of_neg h4]
  have h10: (x + y) < 0 := by linarith
  rw[abs_of_neg h10]
  linarith

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  rcases le_or_gt 0 y with h1 | h2
  intro h
  left
  rw [abs_of_nonneg h1] at h
  exact h
  intro h
  right
  rw [abs_of_neg h2] at h
  exact h
  intro h
  rcases h with h1 | h2
  have h3: y ≤ |y| := by apply le_abs_self y
  apply lt_of_lt_of_le h1 h3
  have h4: -y ≤ |-y| := by apply le_abs_self (-y)
  rw[abs_neg] at h4
  apply lt_of_lt_of_le h2 h4

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  rcases le_or_gt 0 x with h1 | h2
  constructor
  intro h
  rw[abs_of_nonneg h1] at h
  constructor
  linarith
  exact h
  intro h
  rcases h with ⟨h3, h4⟩
  rw[abs_of_nonneg h1]
  exact h4
  constructor
  intro h
  constructor
  rw[abs_of_neg h2] at h
  linarith
  rw[abs_of_neg h2] at h
  linarith
  intro h
  rcases h with ⟨h3, h4⟩
  rw[abs_of_neg h2]
  linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl | rfl⟩ <;> linarith [sq_nonneg x, sq_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h1: (x+1) * (x-1) = 0 := by linarith
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h1
  rcases h1 with h2 | h3
  right
  linarith
  left
  linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h1: (x+y) * (x-y) = 0 := by linarith
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h1
  rcases h1 with h2 | h3
  right
  linarith
  left
  linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h1: (x+1)*(x-1) = 0 := by
    ring_nf
    rw[h]
    simp
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h1
  rcases h1 with h2|h3
  right
  exact eq_neg_of_add_eq_zero_left h2
  left
  exact sub_eq_zero.mp h3

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h1: (x+y)*(x-y) = 0 := by
    ring_nf
    rw[h]
    simp
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h1
  rcases h1 with h2|h3
  right
  exact eq_neg_of_add_eq_zero_left h2
  left
  exact sub_eq_zero.mp h3

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  assumption
  contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  intro h
  by_cases h1 : P
  apply h at h1
  right
  exact h1
  left
  exact h1
  intro h
  by_cases h1 : P
  rcases h with h2 | h3
  contradiction
  intro h4
  exact h3
  intro h5
  contradiction
