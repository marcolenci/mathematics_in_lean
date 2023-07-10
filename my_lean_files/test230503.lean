/- variable (p q : Prop)

example (hpq: p → q) : ¬q → ¬p :=
  fun hnq => fun hp => False

#check False
#check p → False 

quick "mind refresh here": the above example is not 
working (as it shouldn't) because with "hp => False" I 
produce a function which maps p to the proposition False
(which is the proposition that is always false), but
I should produce a function which maps p to a proof
(i.e., an element) of False" -/

-- variable (α : Type)
def α : Type := Nat
variable {p q : α → Prop}

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
    fun y : α => (h y).left
    -- or 'show p y from (h y).left'

#check α
#eval α
#check p

def b1 : Bool := true 

#check b1
#eval b1


