variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)


variable (a b c d : Nat)

/-
def divides (a b : Nat) : Prop := ∃ k, k*a = b

notation a "|" b => divides a b

#check divides 2 4
#check 2|4
-/

def prime (n : Nat) : Prop := sorry