import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x hx
  rcases hx with hst | hsn
  rcases hst with ⟨hs, ht⟩
  rw[inter_def]
  simp only [mem_setOf, mem_union]
  constructor
  exact hs
  left
  exact ht
  rcases hsn with ⟨hs,hn⟩
  rw[inter_def, mem_setOf]
  constructor
  exact hs
  rw[union_def, mem_setOf]
  right
  exact hn

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intro x xsntu
  have xs : x ∈ s := xsntu.1
  have xntu : x ∉ (t ∪ u) := xsntu.2
  constructor
  constructor
  exact xs
  intro hx
  have h1: x ∈ (t ∪ u) := by exact Set.mem_union_left u hx
  apply xntu at h1
  exact h1
  intro hx
  have h2: x ∈ (t ∪ u) := by exact Set.mem_union_right t hx
  apply xntu at h2
  exact h2

example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun _x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
    Subset.antisymm (by
    intro x hx
    rcases hx with ⟨h1, h2⟩
    constructor
    exact h2
    exact h1
  ) (by
  intro x hx
  rcases hx with ⟨h1, h2⟩
  constructor
  exact h2
  exact h1
  )

example : s ∩ (s ∪ t) = s := by
  ext x
  constructor
  intro hx
  rcases hx with ⟨h1, h2⟩
  exact h1
  intro hx
  constructor
  exact hx
  rw[union_def, mem_setOf]
  constructor
  exact hx

example : s ∪ s ∩ t = s := by
  ext x
  constructor
  intro hx
  rcases hx with h1 | h2
  exact h1
  rcases h2 with ⟨h3, h4⟩
  exact h3
  intro hx
  constructor
  exact hx

example : s \ t ∪ t = s ∪ t := by
  ext x
  constructor
  intro hx
  rcases hx with h1 | h2
  rcases h1 with ⟨h3, h4⟩
  constructor
  exact h3
  rw[union_def, mem_setOf]
  right
  exact h2
  intro hx
  rcases hx with h1 | h2
  by_cases hx : x ∈ t
  rw[union_def, mem_setOf]
  right
  exact hx
  constructor
  constructor
  exact h1
  exact hx
  rw[union_def, mem_setOf]
  right
  exact h2

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  intro hx
  rcases hx with h1 | h2
  rcases h1 with ⟨h3, h4⟩
  constructor
  rw[union_def, mem_setOf]
  left
  exact h3
  intro h5
  rcases h5 with ⟨h6, h7⟩
  apply h4 at h7
  exact h7
  rcases h2 with ⟨h8, h9⟩
  constructor
  rw[union_def, mem_setOf]
  right
  exact h8
  intro h10
  rcases h10 with ⟨h11, h12⟩
  apply h9 at h11
  exact h11
  intro hx
  rcases hx with ⟨h1, h2⟩
  rcases h1 with h3 | h4
  rw[union_def, mem_setOf]
  left
  constructor
  exact h3
  intro h5
  have h6: x ∈ s ∩ t := by
    constructor
    exact h3
    exact h5
  apply h2 at h6
  exact h6
  right
  constructor
  exact h4
  intro h5
  have h6: x ∈ s ∩ t := by
    constructor
    exact h5
    exact h4
  apply h2 at h6
  exact h6

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False := by
  simp at h

example (x : ℕ) : x ∈ (univ : Set ℕ) := by
  trivial

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n
  simp
  intro h1 h2
  have h3:= Nat.Prime.eq_two_or_odd h1
  rcases h3 with h4 | h5
  rw[h4] at h2
  simp at h2
  rw[Nat.odd_iff]
  exact h5

#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end

section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x hs
  have h: (x ∈ t) := ssubt hs
  constructor
  apply h₀ x h
  apply h₁ x h

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x, hx⟩
  use x
  rcases hx with ⟨h1, h2⟩
  rcases h2 with ⟨h3, h4⟩
  constructor
  have h : (x ∈ t) := ssubt h1
  exact h
  exact h4

end

end

section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i

example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  constructor
  intro hx
  simp at hx
  simp
  intro i
  rcases hx with hs | hi
  right
  exact hs
  left
  exact hi i
  intro hi
  rw[union_def, mem_setOf]
  by_cases hs : x ∈ s
  constructor
  exact hs
  rw[mem_iInter] at hi
  right
  rw[mem_iInter]
  intro i
  rcases (hi i) with h1 | h2
  exact h1
  contradiction

def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  apply eq_univ_of_forall
  simp
  have h := Nat.exists_infinite_primes
  intro n
  rcases h n with ⟨p, p1, p2⟩
  have h1: p ∈ primes := by
    exact p2
  use p
end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end
