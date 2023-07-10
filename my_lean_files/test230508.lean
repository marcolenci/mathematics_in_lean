variable (α β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _

#check Eq.refl    -- ∀ (a : ?m.1), a = a
#check Eq.symm    -- ∀ {α : Sort u} {a b : α}, a = b → b = a
#check Eq.trans   -- ∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

/- Not sure I understand, as of now what the underscore does in this
series of examples below -/

#check Eq.refl 
#check Eq.refl _
#check Eq.refl Nat

variable (h : α = β)

#check Eq.symm h

/- but the book says that this feature of the framework is so important 
that the library defines a notation rfl for Eq.refl _ -/

-- changing topic

example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

example (h : a=b) : b=a :=
    Eq.symm h

#check congrArg
#check congrFun


variable (a b : α)

#check Eq.refl a

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

variable (x y : Nat)
variable (h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y)

#check Nat.add_mul x y y
#check (Nat.add_mul x y y) ▸ h1

variable (hh : (x + y) * (x + y) = (x + y) * x + (x * y + y * y))
#check hh
#check Nat.add_mul x y x
#check (Nat.add_mul x y x) ▸ hh

-- The following is an example by the book of calculational proof 

variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

theorem T : a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4

#check h3
#check congrArg Nat.succ h3 /- this is of type Nat.succ c = Nat.succ d, not c+1 = d+1
                              but it works anyway apparently -/

-- Let me try to rewrite it in regular terms

theorem myT : a = e :=
  have h₁ : a = c+1 := Eq.trans h1 h2
  have h₂ : a = d+1 := h3 ▸ h₁
  /- NOTE: Eq.subst h3 h₁ in the above does not work: this is semiunderstandable
  but it's still not clear to me why ▸ works; must be a "smart" command -/ 
  have h₃ : a = 1+d := Eq.trans h₂ (Nat.add_comm d 1)
  -- I culd abbreviate the above to: have h₃ : a = 1+d := h₂.trans (Nat.add_comm d 1)
  Eq.trans h₃ (Eq.symm h4)


theorem T2 : a = e :=
  by rw [h1, h2, h3, Nat.add_comm, h4]

theorem T3 : a = e :=
  by simp [Nat.add_comm, h3, h2, h1, h4]

/- T3 above is a modification of an example by the book to better highlight the
difference between rw and simp -/

variable (n : Nat)

def iseven (n : Nat) : Prop := ∃ k : Nat, 2*k = n
/- the above appears to be equivalent to 
def iseven2 := fun n : Nat => ∃ k : Nat, 2*k = n
-/
#check iseven

#check iseven 4

example : ∃ k : Nat, 2*k = 4 :=
  have g : 2*2 = 4 := by rfl
  Exists.intro 2 g

example : iseven 4 :=
  have g : 2*2 = 4 := by rfl
  Exists.intro 2 g

example : ∀n : Nat, iseven (2*n) := 
  fun n : Nat => Exists.intro n (Eq.refl (2*n))
    
#check Eq.refl (2*n)

theorem seemed_silly : ∀n : Nat, iseven (4*n) := 
  fun n : Nat => 
    have he : 2*(2*n) = 4*n := 
      calc
        2*(2*n) = 2*2*n := by rw [Nat.mul_assoc]
        _ = 4*n := by simp
    show iseven (4*n) from Exists.intro (2*n) he
    -- as always 'show ... from' is redundant
    -- more compact notation for 'Exists.intro (2*n) he' ⟨2*n,he⟩ (bra-kets)
  
theorem seemed_silly_no_tactics : ∀n : Nat, iseven (4*n) := 
  fun n : Nat => 
    have he : 2*(2*n) = 4*n := 
      calc
        2*(2*n) = 2*2*n := Eq.symm (Nat.mul_assoc 2 2 n)
        _ = 4*n := Eq.refl (4*n)
      Exists.intro (2*n) he