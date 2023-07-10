variable (a b c d : Nat)

def f a := a + 1
def g := fun a => a + 1
#check f
#check g
#eval f 2
#eval g 2


def divides (a b : Nat) : Prop := ∃ k, k*a = b

notation a "|" b => divides a b

#check divides 2 4
#check 2|4

example : 2|4 := Exists.intro 2 (Eq.refl 4)
example : 2|4 := ⟨ 2 , Eq.refl 4 ⟩
theorem pluto : 2|4 := ⟨ 2 , rfl ⟩

def prime (n : Nat) : Prop := 
  ∀ a : Nat, (a|n) → (a=1 ∨ a=n)

#check prime 
#check prime 3

#print prime
#print pluto

-- first attempts at tactic modes

theorem bythebook (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp
/- the terrible thing above is that aparently all commands need to
be aligned -/

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp

theorem bythebook_nt (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := 
  And.intro hp (And.intro hq hp)

#print bythebook
#print bythebook_nt

theorem bythebook2 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  apply And.intro hq
  exact hp

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁

-- the above w/o tactics would be

example : ∀ a b c : Nat, a = b → a = c → c = b :=
  fun a b c =>
    fun hab : a = b =>
      fun hac : a = c => Eq.trans (Eq.symm hac) hab

example (α : Type) (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩

-- these following examples are really hard to understand well

example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨y, Or.inl h⟩ => exact ⟨y, Or.inr h⟩ ;
  | ⟨y, Or.inr h⟩ => exact ⟨y, Or.inl h⟩ 

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption

example (x : Nat) : x = x := by
  revert x
  intro 
  rfl  -- rfl is syntactic sugar for "exact rfl"
  -- I would have understood this better if it ended with "apply Eq.refl" 

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => constructor; apply Or.inl; exact px

-- the above is from the book, and of course I get epsilon of it
-- let me try to do it myself in other ways

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  match h with 
  | ⟨y, py⟩ => constructor; apply Or.inl; assumption -- or "...; exact py"
-- I still mostly don't understand "constructor", but maybe a liiiiittle bit

-- The following was done entirely by me and it's different from the book
example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨x, px, qx⟩ 
  constructor
  apply And.intro 
  repeat assumption

example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction

  