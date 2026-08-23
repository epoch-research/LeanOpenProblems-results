import FormalConjectures.Util.ProblemImports

open Nat Finset

lemma factorial_eight : (8 : ℕ).factorial = 40320 := by decide

lemma choose_eight_mul (z : ℕ) :
    40320 * (z + 7).choose 8 = (z + 7).descFactorial 8 := by
  rw [← factorial_eight, descFactorial_eq_factorial_mul_choose]

lemma choose_eight_ge (z : ℕ) : z ^ 8 ≤ 40320 * (z + 7).choose 8 := by
  rw [choose_eight_mul, descFactorial_eq_prod_range]
  have h : ∀ i ∈ range 8, z ≤ z + 7 - i := by
    intro i hi
    have : i < 8 := mem_range.mp hi
    omega
  calc
    z ^ 8 = ∏ _i ∈ range 8, z := by simp [prod_const, card_range]
    _ ≤ ∏ i ∈ range 8, (z + 7 - i) := prod_le_prod' h

lemma twentyfour_mul_choose_four (x : ℕ) :
    24 * (x + 3).choose 4 = x * (x + 1) * (x + 2) * (x + 3) := by
  have h := descFactorial_eq_factorial_mul_choose (x + 3) 4
  have hf : (4 : ℕ).factorial = 24 := by decide
  have hd : (x + 3).descFactorial 4 = x * (x + 1) * (x + 2) * (x + 3) := by
    simp [descFactorial_succ]
    ring
  rw [hf] at h
  rw [← h, hd]

lemma twentyfour_choose_four_add_one (x : ℕ) :
    24 * (x + 3).choose 4 + 1 = (x * x + 3 * x + 1) * (x * x + 3 * x + 1) := by
  have h24 := twentyfour_mul_choose_four x
  have : x * (x + 1) * (x + 2) * (x + 3) + 1 =
      (x * x + 3 * x + 1) * (x * x + 3 * x + 1) := by ring
  omega

lemma choose_eight_succ_sub (z : ℕ) :
    (z + 8).choose 8 - (z + 7).choose 8 = (z + 7).choose 7 := by
  have h : (z + 8).choose 8 = (z + 7).choose 7 + (z + 7).choose 8 := by
    simpa using choose_succ_succ' (z + 7) 7
  rw [h, Nat.add_comm, Nat.add_sub_cancel_left]

/-- For `n > 0`, `C(n+8, 8) > n`. -/
lemma choose_n8_gt (n : ℕ) : n < (n + 8).choose 8 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hgrow : ((n + 8).choose 8).succ ≤ (n + 9).choose 8 := by
      have h : (n + 9).choose 8 = (n + 8).choose 7 + (n + 8).choose 8 := by
        simpa using choose_succ_succ' (n + 8) 7
      have : 1 ≤ (n + 8).choose 7 := choose_pos (by omega)
      rw [h]
      omega
    have : n + 1 + 8 = n + 9 := by omega
    rw [this]
    exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt ih) (Nat.lt_of_succ_le hgrow)

lemma exists_max_choose_eight (n : ℕ) :
    ∃ z, (z + 7).choose 8 ≤ n ∧ n < (z + 8).choose 8 := by
  have hbig : n < (n + 8).choose 8 := choose_n8_gt n
  by_cases h8 : n < (8 : ℕ).choose 8
  · refine ⟨0, ?_, ?_⟩
    · simp
    · simpa using h8
  · have hP0 : (0 + 7).choose 8 ≤ n := by simp
    let P : ℕ → Prop := fun z => (z + 7).choose 8 ≤ n
    have hP0' : P 0 := hP0
    let z := Nat.findGreatest P n
    have hzP : P z := Nat.findGreatest_spec (n := n) (m := 0) (Nat.zero_le _) hP0'
    refine ⟨z, hzP, ?_⟩
    by_contra hnot
    have hle' : (z + 8).choose 8 ≤ n := Nat.le_of_not_gt hnot
    have hPs : P (z + 1) := by simpa [P] using hle'
    have hz_le : ∀ z, P z → z ≤ n := by
      intro z hz
      by_contra hgt
      have : n < z := Nat.lt_of_not_ge hgt
      have hmono : (n + 8).choose 8 ≤ (z + 7).choose 8 :=
        choose_le_choose 8 (by omega)
      exact (not_le_of_gt hbig) (hmono.trans hz)
    have hz1le : z + 1 ≤ n := hz_le _ hPs
    have hng : ¬ P (z + 1) :=
      Nat.findGreatest_is_greatest (P := P) (n := n) (by omega) hz1le
    exact hng hPs

#check exists_max_choose_eight
#check choose_eight_succ_sub
