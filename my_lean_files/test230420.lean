variable (i j k : Nat)

def mysum := i+j
def myprod := i*j

#eval mysum 3 4
#eval myprod 3 4

-- these above were just recap stuff

variable (p q : Prop)

open Classical

#check em p

example (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1)
    (fun h1 : ¬p => False.elim (h h1))
    -- modified from book: in the book it was 'absurd h1 h'

example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p =>
     show False from h h1)

-- I try this example of my own

example (hpq: p → q) : ¬q → ¬p :=
  byCases 
    (fun hp : p => fun hnq : ¬q => (fun hpp : p => hnq (hpq hpp)))
    (fun hnp : ¬p => fun hnq : ¬q => hnp) 

example (hpq: p → q) : ¬q → ¬p :=
  fun hnq : ¬q => (fun hp : p => hnq (hpq hp))
  -- could simplfy notation by eliminating outer parentheses

/- Let's contract notation (Lean expects nhq to be of type hpq 
and hp to be of type p) -/
theorem mycontradictionprinciple (hpq: p → q) : ¬q → ¬p :=
  fun hnq => fun hp => hnq (hpq hp)

/- This is an exercise from end of Sect. 3 of the book. I first start with
two examples and then I solve the exercise -/

example (hporq : p ∨ q) : q ∨ p := 
  Or.elim hporq
  (fun hp => Or.inr hp) 
  (fun hq => Or.inl hq) 

example : p ∨ q → q ∨ p :=
  fun (hporq : p ∨ q) => 
    (Or.elim hporq
    (fun hp => Or.inr hp) 
    (fun hq => Or.inl hq))

example : p ∨ q ↔ q ∨ p := 
  Iff.intro 
    (fun (hporq : p ∨ q) => 
      (Or.elim hporq
      (fun hp => Or.inr hp) 
      (fun hq => Or.inl hq)))
    (fun (hqorp : q ∨ p) => 
      (Or.elim hqorp
      (fun hq => Or.inr hq) 
      (fun hp => Or.inl hp)))
  