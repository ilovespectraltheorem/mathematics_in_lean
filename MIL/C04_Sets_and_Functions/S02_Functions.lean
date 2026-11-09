import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  intro imsinv x xs
  simp
  have h : f x ∈ f '' s := by
    simp
    use x
  exact imsinv h
  intro sinpreimv x xfs
  rcases xfs with ⟨y, hy⟩
  rcases hy with ⟨h1, h2⟩
  have h3: y ∈ f⁻¹' v := by exact sinpreimv h1
  simp at h3
  rw[h2] at h3
  exact h3

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x xs
  simp at xs
  rcases xs with ⟨y, ys, hy⟩
  apply h at hy
  rw[hy] at ys
  exact ys

example : f '' (f ⁻¹' u) ⊆ u := by
  intro x xs
  simp at xs
  rcases xs with ⟨y, yu, yx⟩
  rw[yx] at yu
  exact yu

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y ys
  simp
  rcases h y with ⟨x, hx⟩
  use x
  constructor
  rw [← hx] at ys
  exact ys
  exact hx

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro x xims
  simp
  rcases xims with ⟨y, hy, hy1⟩
  have h1: y ∈ t := by
    apply h hy
  use y

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x xu
  simp
  simp at xu
  exact h xu

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  intro hx
  simp at hx
  rcases hx with h1 | h2
  simp
  left
  exact h1
  right
  exact h2
  intro hx
  simp at hx
  simp
  exact hx

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro x hx
  rcases hx with ⟨y, ys, yt⟩
  simp
  constructor
  use y
  constructor
  rcases ys with ⟨h1, h2⟩
  exact h1
  exact yt
  use y
  rcases ys with ⟨h1, h2⟩
  constructor
  exact h2
  exact yt

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro x hx
  rcases hx with ⟨hs, ht⟩
  rcases hs with ⟨y, h0, h1⟩
  rcases ht with ⟨y1, h2, h3⟩
  have h4: f y = f y1 := by rw[h3, h1]
  have h5: y = y1 := by exact h h4
  rw[← h5] at h2
  have h6: y ∈ s ∩ t := by
    simp
    constructor
    exact h0
    exact h2
  simp
  use y

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro x hx
  rcases hx with ⟨hs, ht⟩
  rcases hs with ⟨y, hy, fyx⟩
  by_cases h1: y ∉ t
  have h2: y∈ s\t := by
    simp
    constructor
    exact hy
    exact h1
  simp
  use y
  simp at h1
  have h3: x ∈ f '' t := by
    simp
    use y
  contradiction

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x hx
  simp at hx
  simp
  exact hx

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext x
  constructor
  intro hx
  rcases hx with ⟨xs, xv⟩
  rcases xs with ⟨y, ys⟩
  rcases ys with ⟨y1, y2⟩
  simp
  use y
  constructor
  constructor
  exact y1
  rw[← y2] at xv
  exact xv
  exact y2
  intro hx
  rcases hx with ⟨y, hy⟩
  rcases hy with ⟨y1, y2⟩
  rcases y1 with ⟨h3, h4⟩
  simp
  constructor
  use y
  simp at h4
  rw[y2] at h4
  exact h4

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro y hy
  rcases hy with ⟨x, hx⟩
  rcases hx with ⟨xs, fxy⟩
  rcases xs with ⟨xs, xu⟩
  simp at xu
  simp
  constructor
  use x
  rw[fxy] at xu
  exact xu

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x hx
  rcases hx with ⟨hs, hfu⟩
  simp
  constructor
  use x
  simp at hfu
  exact hfu

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  intro x hx
  rcases hx with hs | hfu
  simp
  left
  use x
  right
  simp at hfu
  exact hfu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  constructor
  rintro ⟨x, h0, h1⟩
  rcases h0 with ⟨I, hI, xI⟩
  simp
  rcases hI with ⟨i, hi⟩
  simp at hi
  use i
  use x
  constructor
  rw[← hi] at xI
  exact xI
  exact h1
  rintro ⟨x, h0, h1⟩
  rcases h0 with ⟨i, hi⟩
  simp at hi
  rw[← hi] at h1
  rcases h1 with ⟨w, hw1, hw2⟩
  simp
  use w
  constructor
  use i
  exact hw2

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  rintro y hy
  rcases hy with ⟨x, hxi, hxy⟩
  simp
  rintro i
  use x
  constructor
  apply hxi
  simp
  exact hxy

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  rintro y h0
  simp only [mem_iInter] at h0
  rcases h0 i with ⟨x, hx1, hx2⟩
  simp
  use x
  constructor
  rw[← hx2] at h0
  rintro j
  have h1: f x ∈ f '' A j := by apply h0 j
  rcases h1 with ⟨z, hz, hzx⟩
  have h2: z = x := by apply injf hzx
  rw[h2] at hz
  exact hz
  exact hx2

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  constructor
  rintro hx
  simp
  rcases hx with ⟨y, hy, fxy⟩
  rcases hy with ⟨z, hz⟩
  use z
  simp at hz
  rw[← hz] at fxy
  exact fxy
  rintro hx
  simp
  rcases hx with ⟨y, hy, hxy⟩
  rcases hy with ⟨z, hz⟩
  simp at hz
  use z
  rw[← hz] at hxy
  simp at hxy
  exact hxy

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  constructor
  rintro hx
  simp
  simp at hx
  exact hx
  rintro hx
  simp
  simp at hx
  exact hx

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos e
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xpos y ypos xy
  simp at xpos ypos
  calc
    x = (√ x)^2 := by apply (Real.sq_sqrt xpos).symm
    (√ x)^2 = (√ y)^2 := by rw[xy]
    (√ y)^2 = y := by apply Real.sq_sqrt ypos

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xpos y ypos xy
  simp at xy
  calc
    x = √ (x ^ 2) := by apply (Real.sqrt_sq xpos).symm
    √ (x ^ 2) = √ (y ^ 2) := by rw[xy]
    √ (y ^ 2) = y := by apply Real.sqrt_sq ypos

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y; constructor
  rintro hy
  simp
  rcases hy with ⟨x, hx1, hx2⟩
  simp at hx1
  rw[← hx2]
  exact Real.sqrt_nonneg x
  rintro hy
  simp at hy
  use y ^ 2
  constructor
  simp
  exact sq_nonneg y
  exact Real.sqrt_sq hy

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y; constructor
  rintro hy
  simp
  rcases hy with ⟨x, hx⟩
  simp at hx
  rw[← hx]
  exact sq_nonneg x
  rintro hy
  simp at hy
  simp
  use √ y
  exact Real.sq_sqrt hy

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw[inverse]
  rw[dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  intro inj
  rw[LeftInverse]
  intro x
  rw[inverse]
  have h: ∃ z, f z = f x := by
    use x
  rw[dif_pos h]
  have hchosen := Classical.choose_spec h
  exact inj hchosen
  intro leftinv
  rw[LeftInverse] at leftinv
  rintro x y fxy
  have h := congrArg (inverse f) fxy
  rw[leftinv, leftinv] at h
  exact h

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  intro surj
  rw[RightInverse]
  rw[LeftInverse]
  rintro x
  rw[inverse]
  have h: ∃ z, f z = x := by
    apply surj x
  rw[dif_pos h]
  exact Classical.choose_spec h
  intro rightinv
  rw[RightInverse] at rightinv
  rw[LeftInverse] at rightinv
  dsimp [Function.Surjective]
  intro b
  use inverse f b
  rw[rightinv b]

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := by
    exact h₁
  have h₃ : j ∉ S := by
    rw[← h] at h₂
    contradiction
  contradiction

-- COMMENTS: TODO: improve this
end
