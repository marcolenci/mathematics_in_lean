variable (p q r s : Prop)

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  -- show r from h₁ (h₂ h₃)
  h₁ (h₂ h₃)

#check t2

theorem t3 {p q r : Prop} (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun hp : p => h₁ (h₂ hp)

#check t3

def main : IO Unit :=
  IO.println "Hello, world!"

#eval main

#eval Lean.versionString

theorem t4 : p ∧ q → q ∧ p := 
  fun h : p ∧ q => And.intro (And.right h) (And.left h)
 

theorem t5 (hh : p ∧ q) : q ∧ p := 
  And.intro (And.right hh) (And.left hh) 

#check t4
#check t5

theorem t6 : p → p ∨ q := fun hp => Or.intro_left q hp

theorem t7 (hp : p) : p ∨ q := Or.intro_left q hp

#check t6
#check t7
