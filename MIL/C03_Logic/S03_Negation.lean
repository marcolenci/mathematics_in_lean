import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f :=
  sorry

example : ¬FnHasUb fun x ↦ x :=
  sorry

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

--mine
example (h : Monotone f) (h' : f a < f b) : a < b := by
  have : ¬ b ≤ a := by
    intro h''
    have h''' : ¬ f a < f b := not_lt_of_ge (h h'')
    exact h''' h'
  exact lt_of_not_ge this

--copied this from the definition fo `absurd`
section mine
variable (p q : Prop)

-- anything follows from 2 contradictory statements (notice the order: first p and then ¬p)
example (hp : p) (hnp : ¬p) : q := absurd hp hnp

-- here I do the same with the tactic exfalso
example (hp : p) (hnp : ¬p) : q := by
  exfalso
  exact hnp hp

end mine

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  sorry

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by sorry
  have h' : f 1 ≤ f 0 := le_refl _
  sorry

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  sorry

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

--mine
example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  rintro x h₁
  have hcontra : ∃ x, P x := ⟨ x, h₁ ⟩
  apply absurd hcontra
  exact h
-- last 2 lines shortened in `exact h hcontra`

--mine
example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro hc
  obtain ⟨ x, hpx ⟩ := hc
  exact (h x) hpx

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  sorry

--mine
example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro hnot
  obtain ⟨x, hnotpx⟩ := h
  exact hnotpx (hnot x)

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x -- this part is useless here (see also description of `show`)
  by_contra h''
  exact h' ⟨x, h''⟩

-- these are all mine
example (h : ¬¬Q) : Q := not_not.mp h

example (h : ¬¬Q) : Q := by
  by_contra hh
  exact h hh

example (h : Q) : ¬¬Q := by
  by_contra hh
  exact hh h

example (h : Q) : ¬¬Q := fun hh ↦ hh h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  sorry

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  dsimp [FnHasUb] -- as always this is useless to lean
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

--mine
example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  dsimp [Monotone] at h
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  simp -- I've added this to explain the term `∃ ε > 0, ε < x`, which became `∃ ε, 0 < ε ∧ ε < x`
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

--my rewriting of the above to use suffice instead of have
example (h : 0 < 0) : a > 37 := by
  suffices h' : ¬0 < 0
  contradiction
  exact lt_irrefl 0

end
