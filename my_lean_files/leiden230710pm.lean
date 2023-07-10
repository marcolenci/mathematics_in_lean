import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

example {G : Type} [Group G] (g h : G) : ⁅g, h⁆ = ⁅h, g⁆⁻¹ := by  
  rw [commutatorElement_def]
  rw [commutatorElement_def]
  rw [mul_inv_rev]
  rw [mul_inv_rev]
  rw [mul_inv_rev]
  rw [inv_inv]
  rw [inv_inv]
  rw [mul_assoc]
  rw [mul_assoc]
  done -- this is useless

example {G : Type} [Group G] (g h : G) : ⁅g, h⁆ = ⁅h, g⁆⁻¹ := by  
  repeat rw [commutatorElement_def]
  repeat rw [mul_inv_rev]
  repeat rw [inv_inv]
  repeat rw [mul_assoc]

example {G : Type} [Group G] (g h : G) : ⁅g, h⁆ = ⁅h, g⁆⁻¹ := by 
  rw [commutatorElement_inv]

open Real 

example : Continuous (fun x ↦ (sin (x^2))^3 + cos (5*x)) := by
  continuity
-- this is too much of a shortcut
