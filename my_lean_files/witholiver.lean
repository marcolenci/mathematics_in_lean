-- This is the Ntural Numbers game that Oliver was talking about

inductive myNat
  | zero : myNat
  | succ : myNat → myNat

open myNat

def add : myNat → myNat → myNat
  | m, zero     => m 
  | m, (succ n) => succ (add m n) 

def mul : myNat → myNat → myNat
  | _, zero     => zero
  | m, (succ n) => add (mul m n)  m 

def one := succ zero
def two := succ one
def three := succ two 
def four := succ three

-- theorem yay : add two two = four := sorry  

variable (n : myNat)

theorem thm_one (n : myNat) : n = n := rfl

theorem thm_two 
  (n : myNat) (h : add n two = three) : add one (add n two) = add one three := by
  rw [h]

theorem thm_three 
  (n : myNat) : add n two = three →  add one (add n two) = add one three :=  by
  intro h
  rw [h]

example : one = one := Eq.refl one 

inductive my_False : Prop

#check False 
#check my_False


theorem umm :  succ three = add one three := rfl 

theorem thm_four : 
  ∀ n, add n two = three →  add one (add n two) = four := by
  intro n h
  rw [h]
  have h₂ :  succ three = add one three := rfl
  -- apply h₂
  rw [←h₂]
  rfl
  
theorem why : succ three = four := rfl 
theorem why_not : add two two = four := rfl 

theorem thm_five : 
  ∀ n, three = add n two →  add one (add n two) = add one three := by
  intro _ h
  rw [←h]

-- theorem zero_add (n : myNat) : add n zero = n := sorry

/- Oliver did this by himeself when I was away -/

-- try it 
def Implies (p q : Prop) : Prop := p → q
structure Proof (p : Prop) : Type where
  proof : p
#check Proof   -- Proof : Prop → Type

axiom and_comm (p q : Prop) : Proof (Implies (And p q) (And q p))

-- try it 
universe u

#check @Eq.refl.{u}   -- ∀ {α : Sort u} (a : α), a = a
#check @Eq.symm.{u}   -- ∀ {α : Sort u} {a b : α}, a = b → b = a
#check @Eq.trans.{u}  -- ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-- try it 

-- axiom unsound : False
-- Everything follows from false

theorem ex (proof_of_false : False) : 1 = 0 :=
  False.elim proof_of_false

