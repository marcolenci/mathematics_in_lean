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
        . exact ylt.le -- that is a shortcup for LT.lt.le ylt
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