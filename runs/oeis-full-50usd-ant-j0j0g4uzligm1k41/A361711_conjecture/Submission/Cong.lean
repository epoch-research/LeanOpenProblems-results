import Submission.Closed2
open Finset BigOperators Nat

theorem prodrep (m : ℕ) :
    (aaq (2*m+1) : ℚ) = ∏ i ∈ Finset.range m, (1 - (2*(m:ℚ)+1)^2/((i:ℚ)+1)^2) := by
  have hm : (m.factorial:ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h2m1 : ((2*m+1).factorial:ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  -- denominator
  have hden : ∏ i ∈ Finset.range m, ((i:ℚ)+1)^2 = (m.factorial:ℚ)^2 := by
    have h1 : ∏ i ∈ Finset.range m, ((i:ℚ)+1) = (m.factorial:ℚ) := by
      rw [← Finset.prod_range_add_one_eq_factorial m, Nat.cast_prod]
      exact Finset.prod_congr rfl (fun i _ => by push_cast; ring)
    rw [Finset.prod_pow, h1]
  -- ascending factorial product
  have hasc : ∏ i ∈ Finset.range m, ((i:ℚ)+2*(m:ℚ)+2) = ((2*m+2).ascFactorial m : ℚ) := by
    rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
    exact Finset.prod_congr rfl (fun i _ => by push_cast; ring)
  -- descending factorial product
  have hdesc2 : ∏ i ∈ Finset.range m, (2*(m:ℚ)-(i:ℚ)) = ((2*m).descFactorial m:ℚ) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi; rw [Finset.mem_range] at hi
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hdesc : ∏ i ∈ Finset.range m, ((i:ℚ)-2*(m:ℚ)) = (-1)^m * ((2*m).descFactorial m:ℚ) := by
    rw [← hdesc2]
    rw [show ((-1:ℚ))^m = ∏ _i ∈ Finset.range m, (-1:ℚ) from by rw [Finset.prod_const, Finset.card_range], ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => by ring)
  -- numerator
  have hnum : ∏ i ∈ Finset.range m, (((i:ℚ)+1)^2-(2*(m:ℚ)+1)^2)
      = (-1)^m * ((2*m).descFactorial m:ℚ) * ((2*m+2).ascFactorial m:ℚ) := by
    have step1 : ∏ i ∈ Finset.range m, (((i:ℚ)+1)^2-(2*(m:ℚ)+1)^2)
        = (∏ i ∈ Finset.range m, ((i:ℚ)-2*(m:ℚ))) * (∏ i ∈ Finset.range m, ((i:ℚ)+2*(m:ℚ)+2)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => by ring)
    rw [step1, hdesc, hasc]
  -- factorial relations
  have hfd : ((2*m).descFactorial m:ℚ) = ((2*m).factorial:ℚ)/(m.factorial:ℚ) := by
    rw [eq_div_iff hm]
    have := Nat.factorial_mul_descFactorial (show m ≤ 2*m by omega)
    rw [show 2*m-m = m from by omega] at this
    have hc := congrArg (Nat.cast : ℕ → ℚ) this; push_cast at hc ⊢; linarith [hc]
  have hfa : ((2*m+2).ascFactorial m:ℚ) = ((3*m+1).factorial:ℚ)/((2*m+1).factorial:ℚ) := by
    rw [eq_div_iff h2m1]
    have := Nat.factorial_mul_ascFactorial (2*m+1) m
    rw [show 2*m+1+1 = 2*m+2 from by omega, show 2*m+1+m = 3*m+1 from by omega] at this
    have hc := congrArg (Nat.cast : ℕ → ℚ) this; push_cast at hc ⊢; linarith [hc]
  -- RHS as ratio
  have hterm : ∀ i ∈ Finset.range m, (1 - (2*(m:ℚ)+1)^2/((i:ℚ)+1)^2)
      = (((i:ℚ)+1)^2-(2*(m:ℚ)+1)^2)/((i:ℚ)+1)^2 := by
    intro i _
    have : ((i:ℚ)+1)^2 ≠ 0 := by positivity
    field_simp
  rw [Finset.prod_congr rfl hterm, Finset.prod_div_distrib, hnum, hden, hfd, hfa, closedform]
  simp only [gq, Gnat, Nat.cast_mul]
  rw [Nat.cast_choose ℚ (show m ≤ 2*m by omega), Nat.cast_choose ℚ (show m ≤ 3*m+1 by omega)]
  rw [show 2*m-m = m from by omega, show 3*m+1-m = 2*m+1 from by omega]
  push_cast
  field_simp
