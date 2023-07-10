variable (p q : Prop)

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)

#check ¬p

theorem t7prime (h : p ∧ q) : q ∧ p :=
  have hp : p := And.left h
  have hq : q := And.right h
  And.intro hq hp
  /- would have been the same with 
  `show q ∧ p from And.intro hq hp' -/

theorem t8 (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from h.right
/- last line can be abbreviated to `h.right' alone -/

axiom unsound : False
-- Everything follows from false
theorem ex : 1 = 0 :=
  False.elim unsound

open Classical

variable (p : Prop)
#check em p

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => False.elim (h hnp)) 
    -- modified from book: in the book it was 'absurd hnp h'

open Classical
variable (p : Prop)

example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p => h h1)
    -- show False from h h1)

#check em p