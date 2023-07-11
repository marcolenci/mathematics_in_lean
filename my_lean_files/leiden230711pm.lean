import Mathlib.Tactic

open Set

section Sets

variable (α : Type)
variable (S : Set α)

example : Set α := fun x => True
example : Set α := fun x ↦ x ≠ x

#check Set α
#reduce Set α

example : Set α := {x : α | True} -- notational sugar
example : Set α := {x : α | x ≠ x} -- all elements of α that do not verify reflexivity

variable (S T U : Set α)

example : S ∩ (T ∩ U) ⊆ S ∩ T ∪ S ∩ U := by
  intro x
  simp
  tauto
  done

variable (β : Type)
variable (f : α → Set β)
#check ⋃ i, f i
#check ⋂ i, f i

#reduce ⋃ i, f i -- study!!
#reduce ⋂ i, f i -- study!!

end Sets

section Functions
open Function

variable (α β : Type)
variable (f : α → β)

variable (S : Set α)
variable (T : Set β)

#check range f

#check f '' S
