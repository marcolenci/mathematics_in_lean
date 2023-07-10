#eval 4/3
#check 5/3 = 1
#eval 5/3 = 1

variable {i n : Nat}

-- def iseven := fun n : Nat => ((n/2)*2 = n)

#check iseven
#check (4*n/2)*2 = n

/- 
theorem silly : ∀ n : Nat, (4*n/2)*2 = 4*n :=
  fun n : Nat => (4*n/2)*2 = 4*n
-/

#check fun i : Nat => ((4*i/2)*2 = 4*i)
#check ∀ n : Nat, (4*n/2)*2 = 4*n

#check ((n/2)*2 = n)
#eval ((n/2)*2 = n)

theorem sillier : ∀ n : Nat, n = n := 
  -- fun (n : Nat) => rfl   (this doesn't work!)
  by 
  intro n 
  rfl

theorem test1 : n = n := Eq.refl n

theorem test2 : ∀ n : Nat, n = n := 
  fun (i : Nat) => Eq.refl i

