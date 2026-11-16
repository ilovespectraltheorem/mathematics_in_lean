import MIL.Common
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic

#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num

#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
    have h1: 2 ∣ m ^ 2 := by
      rw[sqr_eq]
      exact dvd_mul_right 2 (n ^ 2)
    apply even_of_even_sqr
    exact h1
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have h1: 2 * k ^ 2 = n ^ 2 :=
    have h2: 2 ≠ 0 := by
      norm_num
    (mul_right_inj' h2).mp this
  have : 2 ∣ n := by
    have h2: 2 ∣ n ^ 2 := by
      rw[← h1]
      exact dvd_mul_right 2 (k ^ 2)
    apply even_of_even_sqr h2
  have : 2 ∣ m.gcd n := by
    apply Nat.dvd_gcd
    assumption
    exact this
  have : 2 ∣ 1 := by
    have h4: m.gcd n = 1 := by
      apply coprime_mn
    rw[← h4]
    exact this
  norm_num at this

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  have h0 (m : ℕ): p ∣ m ^ 2 → p ∣ m := by
    intro pdiv
    rw[pow_two] at pdiv
    apply prime_p.dvd_mul.mp at pdiv
    rcases pdiv with p1 | p2
    exact p1; exact p2
  intro sqr_eq
  have : p ∣ m := by
    have h1: p ∣ m ^ 2 := by
      rw[sqr_eq]
      exact dvd_mul_right p (n ^ 2)
    apply h0 at h1
    exact h1
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : p * (p * k ^ 2) = p * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have h1: p * k ^ 2 = n ^ 2 :=
    have h2: p ≠ 0 := by
      by_contra p1
      have h3: 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
        (rwa [Nat.prime_def_lt] at prime_p)
      rcases h3 with ⟨h4, h5⟩
      rw[p1] at h4
      norm_num at h4
    (mul_right_inj' h2).mp this
  have : p ∣ n := by
    have h2: p ∣ n ^ 2 := by
      rw[← h1]
      exact dvd_mul_right p (k ^ 2)
    apply h0 at h2
    exact h2
  have : p ∣ m.gcd n := by
    apply Nat.dvd_gcd
    assumption
    exact this
  have h5 : p ∣ 1 := by
    have h4: m.gcd n = 1 := by
      apply coprime_mn
    rw[← h4]
    exact this
  have h4: p ≤ 1 := by
    have h6: 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
        (rwa [Nat.prime_def_lt] at prime_p)
    rcases h6 with ⟨h7, h8⟩
    have h9: 0 < 2:= by norm_num
    have h10: 0 < p := by
      exact lt_of_lt_of_le h9 h7
    apply Nat.le_of_dvd
    norm_num
    exact h5
  norm_num at this
  have h3: 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
        (rwa [Nat.prime_def_lt] at prime_p)
  rcases h3 with ⟨h6, h7⟩
  have h7: 2 ≤ 1 := by apply le_trans h6 h4
  norm_num at h7

#check Nat.primeFactorsList
#check Nat.prime_of_mem_primeFactorsList
#check Nat.prod_primeFactorsList
#check Nat.primeFactorsList_unique

theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    apply factorization_pow'
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    calc
    (p * n ^ 2).factorization p = p.factorization p + (n ^ 2).factorization p :=
    factorization_mul' prime_p.ne_zero nsqr_nez p
    p.factorization p + (n ^ 2).factorization p = 1 + (n ^ 2).factorization p := by
      rw[Nat.Prime.factorization' prime_p]
    1 + (n ^ 2).factorization p = 2 * n.factorization p + 1 := by
      rw[factorization_pow' n 2 p, add_comm]
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := by
    by_contra h1
    apply eq_zero_of_pow_eq_zero at h1
    contradiction
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
    apply factorization_pow'
  have eq2 : ((r + 1) * n ^ k).factorization p =
      k * n.factorization p + (r + 1).factorization p := by
      have h2: r + 1 ≠ 0 := by
        apply r.succ_ne_zero
      rw[factorization_mul' h2 npow_nz, factorization_pow', add_comm]
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
  have k1 : k ∣ k * m.factorization p := by
    apply Nat.dvd_mul_right
  have k2 : k ∣ k * n.factorization p := by
    apply Nat.dvd_mul_right
  apply Nat.dvd_sub k1 k2

#check multiplicity
