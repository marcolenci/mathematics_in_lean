example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl

-- is equivalent to

example (n : Nat) : n + 1 = Nat.succ n := by
  rfl

-- example from the book that I really don't understand
example : ∃ x, x + 2 = 8 := by
  let a : Nat := 3 * 2
  exists a

-- what I was able to do by myself
example : ∃ x, x + 2 = 8 := by
    let a : Nat := 3 * 2
    have : a + 2 = 8 := rfl
    constructor
    exact this

-- I was also able to do this, but I understand it less than before
example : ∃ x, x + 2 = 8 := by
  -- let a : Nat := 3 * 2
  constructor
  rfl
