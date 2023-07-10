variable (g : Nat → Nat → Nat)
variable (hg : g 0 0 = 0)

theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true  -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4


variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    fun w =>
      fun hw : p w ∧ q w => Exists.intro w (And.intro hw.right hw.left)
      /- The book writes: ... => show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)
      could have abbreviated the last part as ⟨w, hw.right, hw.left⟩, which is
      super short abbreviation for ⟨w, ⟨hw.right, hw.left⟩⟩. -/

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w => ⟨w, ⟨hw.right, hw.left⟩⟩)

example (h : ∃ x, p x ∧ q x) : ∃ x, p x :=
  Exists.elim h   -- after here I shoukd put some element of ∀ y, p y ∧ q y → ∃ x, p x
                  -- i.e., y → (p y ∧ q y → ∃ x, p x), 
                  -- i.e., y → p y ∧ q y → ∃ x, p x
    fun y =>
      fun h₁ : p y ∧ q y => Exists.intro y h₁.left

example (h : ∃ x, p x ∧ q x) : ∃ x, p x :=
  match h with
  | Exists.intro (y : α) (h₁ : p y ∧ q y) => Exists.intro y h₁.left
--  simplified:  | Exists.intro y h₁ => Exists.intro y h₁.left
--  anonymous constructor notation:  | ⟨(y : α), (h₁ : p y ∧ q y)⟩ => ⟨y, h₁.left⟩


open Classical

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x := byContradiction 
  fun h1 : ¬ ∃ x, p x => 
    have h2 : ∀ x, ¬ p x := 
      fun x => 
        fun h3 : p x => 
          have h4 : ∃ x, p x := Exists.intro x h3 -- equiv. ⟨x,h3⟩
          h1 h4
    h h2