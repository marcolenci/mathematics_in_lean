import Mathlib.Tactic
import Mathlib.Data.Real.Basic

theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end

theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h₀ h₁ ha hb

end

theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := abs_mul x y
    _ ≤ |x| * ε := by
        apply mul_le_mul
        . rfl
        . exact ylt.le -- that is a shortcut for LT.lt.le ylt
        . exact abs_nonneg y
        . exact abs_nonneg x
    _ < 1 * ε := by
        apply (mul_lt_mul_right epos).2
        exact lt_of_lt_of_le xlt ele1
        /- also
        apply (mul_lt_mul_right _).2
        . exact lt_of_lt_of_le xlt ele1
        . exact epos
        -/
    _ = ε := by rw[one_mul]
  done

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

theorem fnUb_add {f g : Real → Real} {a b : Real} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) := by
  intro y
  dsimp
  apply add_le_add
-- Now we have two goals; it's good practice to delineate them.
  · apply hfa
    -- also exact hfa _
    -- also exact hfa y
  . apply hgb

section
/- Next up is the existential quantifier: "there exists", denoted `∃`.
You can type it with \exists or just \ex. -/

variable (α : Type) (P : α → Prop)
#check ∃ x, P x

/- Again, we need to know how to prove an existence statement - how to
supply a witness `x` and a proof `P x` - and how to use one to add a
witness and hypothesis to the local context. -/
end

/- In tactic mode we can use the `use` tactic. -/
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5 / 2
  norm_num

/- In term mode, we use "anonymous constructor" notation. This lets us
create terms of a certain class of types concisely; Lean works out
from the declaration type what we mean by `⟨_, ..., _⟩` in each case. -/
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  Exists.intro (5 / 2) (by norm_num)
  -- also ⟨5 / 2, by norm_num⟩

/- We can hide an existential under a definition. -/
def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

variable {f g : ℝ → ℝ}

/- To extract an `x` and a hypothesis `P x` from the statement
`∃ x, P x`, we can use the `rcases` tactic. Like `intro`, it can see
under definitions. -/
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubgb⟩
  exact Exists.intro (a+b) (fnUb_add ubfa ubgb) -- this is my semi-nontactic variation
  /- use a + b
  apply fnUb_add ubfa ubgb -/

/- This is what she (Amelia Lvingston) wrote:
The tactic `rintro` is a combination of `intro` and `rcases`. -/
example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x :=
  fun ⟨a, ubfa⟩ ⟨b, ubgb⟩ ↦ ⟨a + b, fnUb_add ubfa ubgb⟩

section
variable (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro y
  dsimp
  apply add_le_add
-- Now we have two goals; it's good practice to delineate them.
  · apply hfa
    -- also exact hfa _
    -- also exact hfa y
  . apply hgb
  done

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro y
  dsimp
  exact mul_nonneg (nnf y) (nng y)
  /- also
  apply mul_nonneg
  . apply nnf
  . apply nng
  done

  also, if I didn't want to use tactics
  fun y => mul_nonneg (nnf y) (nng y)
  -/


example (hfa : FnUb f a) (hfb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
      intro y
      dsimp
      exact mul_le_mul (hfa y) (hfb y) (nng y) nna
      done

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x :=
  match lbf with
  | ⟨a, albf⟩ => match lbg with
    | ⟨b, albg⟩ => ⟨a+b, fun x => add_le_add (albf x) (albg x)⟩
-- done by marcello and me with no tactics

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  sorry

end

section

variable {α : Type _} [CommRing α]

def SumOfSquares (x : α) :=
  ∃ a b, x = a ^ 2 + b ^ 2

theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, xeq⟩
  rcases sosy with ⟨c, d, yeq⟩
  rw [xeq, yeq]
  use a * c - b * d, a * d + b * c
  ring

theorem sumOfSquares_mul' {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, rfl⟩
  rcases sosy with ⟨c, d, rfl⟩
  use a * c - b * d, a * d + b * c
  ring

end

section
variable {a b c : ℕ}

example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, beq⟩
  rcases divbc with ⟨e, ceq⟩
  rw [ceq, beq]
  use d * e; ring

-- redone by Marcello and me
example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, rfl⟩
  rcases divbc with ⟨e, rfl⟩
  use d * e
  exact Nat.mul_assoc a d e

-- new one
example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  rcases divab with ⟨d, rfl⟩
  rcases divac with ⟨e, rfl⟩
  exact ⟨d+e, by ring⟩
end

section

open Function

example {c : ℝ} : Surjective fun x ↦ x + c := by
  intro x
  use x - c
  dsimp; ring

example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  intro x
  use x / c
  field_simp [h]
  apply mul_comm
  done
  -- also (in place of field_simp) exact mul_div_cancel' x h

example (x y : ℝ) (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by
  field_simp [h]
  ring

example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
  rcases h 2 with ⟨x, hx⟩
  use x
  rw [hx]
  norm_num

end

section
open Function
variable {α : Type _} {β : Type _} {γ : Type _}
variable {g : β → γ} {f : α → β}

example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  intro z
  rcases surjg z with ⟨y, hy⟩
  rcases surjf y with ⟨x, hx⟩
  use x
  simp [hx, hy]
  /- also
  simp
  rw [hx, hy]
  -/
  done

end

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

example (h : Monotone f) (h' : f a < f b) : a < b := by
  sorry

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
