import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

open BigOperators

namespace C05S03

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat apply Nat.succ_le_succ
    apply zero_le

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m <;> contradiction

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  revert h0 h1
  revert h m
  decide

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn

--mine
#check Nat.factorial_pos
#check Nat.dvd_sub'

theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have : 2 ≤ Nat.factorial n + 1 := by
    simp
    have := Nat.factorial_pos n
    linarith
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  refine ⟨p, ?_, pp⟩
  --show p > n
  by_contra ple
  push_neg at ple
  have : p ∣ Nat.factorial n := Nat.dvd_factorial (Nat.Prime.pos pp) ple
  have : p ∣ 1 := by
    have rough := Nat.dvd_sub pdvd this
    have smp : n.factorial + 1 - n.factorial = 1 := by field_simp
        -- field_simp seems to be the only tactic that works here
    rwa [← smp]
    /-
    The solutions suggested:
    convert Nat.dvd_sub pdvd this
    simp
    -/
  --show False
  simp at this
  have pge2 : 2 ≤ p := Nat.Prime.two_le pp
  linarith
  /-
  The solutions suggested:
  linarith [Nat.Prime.two_le pp]
  -/

open Finset

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  rw [subset_iff]
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  tauto

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t ⊆ r ∩ (s ∪ t) := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t = r ∩ (s ∪ t) := by
  ext x
  simp
  tauto

end

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

--the next two are mine
example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  simp
  tauto

example : (r \ s) \ t = r \ (s ∪ t) := by
  ext
  simp
  tauto

end

example (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ ∏ i ∈ s, i :=
  Finset.dvd_prod_of_mem _ h

--next two are mine
theorem _root_.Nat.Prime.eq_of_dvd_of_prime {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) : p = q := by
  have := Nat.Prime.eq_one_or_self_of_dvd prime_q p h
  rcases this with h1 | h1
  · have := Nat.Prime.two_le prime_p
    exfalso -- this can also be removed (linarith is smart enough)
    linarith
  · assumption

theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
    (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n ∈ s, n) → p ∈ s := by
  intro h₀ h₁
  induction' s using Finset.induction_on with a s ans ih
  · simp at h₁
    linarith [prime_p.two_le]
  simp [Finset.prod_insert ans, prime_p.dvd_mul] at h₀ h₁
  rw [mem_insert]
  obtain ⟨prime_a, less_easy⟩ := h₀
  by_cases cs1 : p = a
  · left ; assumption
  · rcases h₁ with cs2 | cs2
    · have := _root_.Nat.Prime.eq_of_dvd_of_prime prime_p prime_a cs2
      contradiction
    · right
      exact ih less_easy cs2

example (s : Finset ℕ) (x : ℕ) : x ∈ s.filter Nat.Prime ↔ x ∈ s ∧ x.Prime :=
  mem_filter

#check Finset.prod_pos

--mine
theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  intro s
  by_contra h
  push_neg at h
  set s' := s.filter Nat.Prime with s'_def
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h -- I would have written `exact h n` (which works!).
            -- `apply h` is more "implicit" but ok
  have : 2 ≤ (∏ i ∈ s', i) + 1 := by
    simp
    have : 0 < ∏ i ∈ s', i := by
      apply Finset.prod_pos
      intro n nins
      have nge2 : 2 ≤ n := Nat.Prime.two_le (mem_s'.mp nins)
      linarith
    linarith
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  have : p ∣ ∏ i ∈ s', i := by
    apply Finset.dvd_prod_of_mem
    exact mem_s'.mpr pp
  have : p ∣ 1 := by
    convert Nat.dvd_sub pdvd this
    simp
  --show False
  simp at *
  have := Nat.Prime.two_le pp
  linarith

theorem bounded_of_ex_finset (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, hs⟩
  use s.sup id + 1
  intro k Qk
  apply Nat.lt_succ_of_le
  show id k ≤ s.sup id
  apply le_sup (hs k Qk)

theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use (range (n + 1)).filter Q
  intro k
  simp [Nat.lt_succ_iff]
  exact hn k

example : 27 % 4 = 3 := by norm_num

--mine
#eval 27 % 4

example : 27 % 4 ≠ 7 := by norm_num

example (n : ℕ) : (4 * n + 3) % 4 = 3 := by
  rw [add_comm, Nat.add_mul_mod_self_left]

theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  revert h
  rw [Nat.mul_mod]
  have : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  /- my comment: the above is a cure shortcut for what I'd have written:
  have : m % 4 < 4 := by
    apply Nat.mod_lt
    norm_num
  -/
  interval_cases m % 4 <;> simp [-Nat.mul_mod_mod]
  have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases n % 4 <;> simp

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
  apply two_le <;>
    · intro neq
      rw [neq] at h
      norm_num at h

--all the next proofs are mine (meaning, I filled the sorrys)
theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  constructor
  · exact Nat.div_dvd_of_dvd h₀
  · apply Nat.div_lt_self
    · exact Nat.zero_lt_of_lt h₂
    · linarith

#print Nat.div_dvd_of_dvd
#print Nat.div_lt_self

--I did this without the `aux` theorem proved above
theorem exists_prime_factor_mod_4_eq_3 {n : Nat} (h : n % 4 = 3) :
    ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  by_cases np : n.Prime
  · use n
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩
  have mge2 : 2 ≤ m := by
    apply two_le _ mne1
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have neq : m * (n / m) = n := Nat.mul_div_cancel' mdvdn
  have : m % 4 = 3 ∨ n / m % 4 = 3 := by
    apply mod_4_eq_3_or_mod_4_eq_3
    rw [neq, h]
  rcases this with h1 | h1
  · by_cases mp : m.Prime
    · use m
    · have h2 : ∃ p, Nat.Prime p ∧ p ∣ m ∧ p % 4 = 3 := ih m mltn h1 mp
      rcases h2 with ⟨p, pprime, pdivm, peq4mod3⟩
      use p
      have pdivn : p ∣ n := Nat.dvd_trans pdivm mdvdn
      exact ⟨pprime, pdivn, peq4mod3⟩
  · have nmdivn : (n / m) ∣ n := Nat.div_dvd_of_dvd mdvdn
    by_cases nmp : (n / m).Prime
    · use n / m
    · have : n / m < n := by
        refine Nat.div_lt_self ?_ mge2
        linarith
      have h2 : ∃ p, Nat.Prime p ∧ p ∣ (n / m) ∧ p % 4 = 3 := ih (n / m) this h1 nmp
      rcases h2 with ⟨p, pprime, pdivnm, peq4mod3⟩
      use p
      have pdivn : p ∣ n := Nat.dvd_trans pdivnm nmdivn
      exact ⟨pprime, pdivn, peq4mod3⟩

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  rwa [mem_erase] at h

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  simp at h
  assumption

#print Nat.dvd_add_iff_left
#print Nat.dvd_sub'
#print Nat.dvd_sub

--mine
theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, Nat.Prime p ∧ p % 4 = 3 := by
  by_contra h
  push_neg at h
  rcases h with ⟨n, hn⟩
  have : ∃ s : Finset Nat, ∀ p : ℕ, p.Prime ∧ p % 4 = 3 ↔ p ∈ s := by
    apply ex_finset_of_bounded
    use n
    contrapose! hn
    rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩
    exact ⟨p, pltn, pp, p4⟩
  rcases this with ⟨s, hs⟩
  have h₁ : ((4 * ∏ i ∈ erase s 3, i) + 3) % 4 = 3 := by
    rw [add_comm, Nat.add_mul_mod_self_left]
  rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩
  have ps : p ∈ s := (hs p).mp ⟨pp, p4eq⟩
  have pne3 : p ≠ 3 := by
    by_contra peq3
    rw [peq3] at pdvd
    have : 3 ∣ 3 := by norm_num
    have pdvd' := Nat.dvd_sub pdvd this
    norm_num at pdvd'
    rw [Nat.Prime.dvd_mul] at pdvd' -- lean has used by itself that 3 is a prime, i.e., `Nat.Prime 3`
    norm_num at pdvd'
    /- the above part is a beautiful trick that I admit I copied for the solutions.
    I'd have written something like:
    rcases pdvd' with absdiv | pdvd''
    · contradiction
    · .....same code as below with pdvd'' instead of pdvd'
    -/
    have this : 3 ∈ s.erase 3 := by
      refine mem_of_dvd_prod_primes Nat.prime_three ?_ pdvd'
      intro q pinsm3
      simp at pinsm3
      exact ((hs q).mpr pinsm3.right).left
    simp at this
    norm_num
  have : p ∣ 4 * ∏ i ∈ erase s 3, i := by
    have : p ∣ ∏ i ∈ erase s 3, i := by
      have : p ∈ erase s 3 := by
        simp
        push_neg
        exact ⟨pne3, ps⟩
      exact dvd_prod_of_mem (fun i ↦ i) this
    exact Nat.dvd_mul_left_of_dvd this 4
  have : p ∣ 3 := by
    have pdvd' := Nat.dvd_sub pdvd this
    norm_num at pdvd'
    assumption
  have : p = 3 := by
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three p this with peq1 | peq3
    · rw [peq1] at pp
      contradiction
    · assumption
    -- In the solutions, the authors prove this last have as:
    -- `apply pp.eq_of_dvd_of_prime Nat.prime_three this`
  contradiction
