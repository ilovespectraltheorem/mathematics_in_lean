import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_iff_left₀ _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  have h0: ∀ (n : ℕ), n ≥ (max Ns Nt) → |(s n  - a) + (t n - b)| ≤ |(s n) - a| + |(t n) - b| := by
    intro n hn
    apply abs_add_le (s n - a) (t n - b)
  intro n hn
  have hns : Ns ≤ n := le_trans (le_max_left Ns Nt) hn
  have hnt : Nt ≤ n := le_trans (le_max_right Ns Nt) hn
  have hsum := add_lt_add (hs n hns) (ht n hnt)
  have hcombined := lt_of_le_of_lt (h0 n hn) hsum
  simp at hcombined
  have h1: |s n - a + (t n - b)| = |s n + t n - (a + b)| := by
    congr 1
    linarith
  rw[← h1]
  exact hcombined

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε epos
  dsimp
  have ε2pos : 0 < ε / |c| := by apply div_pos epos acpos
  rcases cs (ε / |c|) ε2pos with ⟨Ns, h0⟩
  use Ns
  intro n ns
  have h1 := mul_lt_mul_of_pos_left (h0 n ns) acpos
  rw[← abs_mul c (s n -a)] at h1
  rw[mul_sub, mul_div_cancel₀ ε (ne_of_gt acpos)] at h1
  exact h1

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn
  have h0: ∀ (n : ℕ), n ≥ N → |(s n  - a) + a| ≤ |(s n) - a| + |a| := by
    intro n hn
    apply abs_add_le (s n - a) a
  simp at h0
  have h1 := add_lt_add_right (h n hn) |a|
  rw [add_comm |a| |s n - a|] at h1
  exact lt_of_le_of_lt (h0 n hn) h1

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n hn
  simp
  obtain ⟨hn0, hn1⟩ := max_le_iff.mp hn
  simp at h₁
  have hprod := mul_lt_mul_of_nonneg (h₀ n hn0) (h₁ n hn1)
    (abs_nonneg (s n)) (abs_nonneg (t n))
  simp at hprod
  rw [mul_div_cancel₀ ε (ne_of_gt Bpos)] at hprod
  exact hprod

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    apply sub_ne_zero.mpr at abne
    apply abs_pos.mpr
    exact abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    have h1: N ≥ Na := by apply le_max_left Na Nb
    apply hNa
    exact h1
  have absb : |s N - b| < ε := by
    have h1: N ≥ Nb := by apply le_max_right Na Nb
    apply hNb
    exact h1
  have : |a - b| < |a - b| := by
    have h2: |s N -a| = |a - s N| := by
      rw[← abs_neg (s N - a)]
      congr 1
      simp
    rw[h2] at absa
    have h3: |(a - s N) + (s N - b)| ≤ |a - s N| + |s N - b|:= by
      apply abs_add_le (a- s N) (s N - b)
    simp at h3
    have h4 := add_lt_add absa absb
    have h5 := lt_of_le_of_lt h3 h4
    dsimp[ε] at h5
    simp at h5
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
