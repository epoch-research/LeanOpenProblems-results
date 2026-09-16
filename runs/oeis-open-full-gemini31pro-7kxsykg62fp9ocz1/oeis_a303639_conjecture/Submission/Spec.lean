import FormalConjectures.Util.ProblemImports

open Nat BigOperators

/--
A303639: Number of ways to write $n$ as $a^2 + b^2 + \binom{2c+1}{c} + \binom{2d+1}{d}$,
where $a,b,c,d$ are nonnegative integers with $a \le b$ and $c \le d$.
-/
def a (n : ℕ) : ℕ :=
  -- Helper for the binomial coefficient term: B(k) = binomial(2*k+1, k)
  let B (k : ℕ) : ℕ := (2 * k + 1).choose k

  -- The maximum value for $a, b$ is $\lfloor \sqrt{n} \rfloor$.
  -- We can use `Finset.range (n + 1)` as an upper bound for convenience,
  -- but the definition provided uses `n.sqrt + 1`, which is tighter.
  let R_sq := Finset.range (n.sqrt + 1)
  -- The maximum value for $c, d$ is safely bounded by $n$.
  let R_binom := Finset.range (n + 1)

  R_sq.sum fun a =>
    R_sq.sum fun b =>
      R_binom.sum fun c =>
        R_binom.sum fun d =>
          if a ≤ b ∧ c ≤ d ∧ a ^ 2 + b ^ 2 + B c + B d = n then 1 else 0

/--
Conjecture A303639: $a(n) > 0$ for all $n > 1$.
-/
theorem oeis_a303639_conjecture (n : ℕ) (hn : n > 1) : a n > 0 := by
  sorry

set_option maxHeartbeats 4000000

lemma B_mono {c : ℕ} (h : c ≥ 17) : (2*c+1).choose c > 800322180 := by
  induction' c, h using Nat.le_induction with k hk ih
  · decide
  · have eq1 : (2 * (k + 1) + 1) = (2 * k + 2) + 1 := by omega
    have step1 : (2 * (k + 1) + 1).choose (k + 1) = (2 * k + 2).choose k + (2 * k + 2).choose (k + 1) := by
      rw [eq1, Nat.choose_succ_succ]
    have eq3 : k = (k - 1) + 1 := by omega
    have step4 : (2 * k + 1 + 1).choose (k - 1 + 1) = (2 * k + 1).choose (k - 1) + (2 * k + 1).choose (k - 1 + 1) := by
      exact Nat.choose_succ_succ (2 * k + 1) (k - 1)
    have eq4 : (2 * k + 1 + 1) = 2 * k + 2 := by omega
    have eq5 : k - 1 + 1 = k := by omega
    rw [eq4, eq5] at step4
    omega

lemma sum_two_squares_step {R q a b : ℕ} (hq : q.Prime) (hq3 : q % 4 = 3) (h : a^2 + b^2 = R) (hdiv : q ∣ R) : q ∣ a ∧ q ∣ b ∧ (a/q)^2 + (b/q)^2 = R / (q^2) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have h1 : (a : ZMod q)^2 + (b : ZMod q)^2 = (R : ZMod q) := by
    calc (a : ZMod q)^2 + (b : ZMod q)^2 = ((a^2 + b^2 : ℕ) : ZMod q) := by push_cast; rfl
    _ = (R : ZMod q) := by rw [h]
  have h2 : (R : ZMod q) = 0 := (CharP.cast_eq_zero_iff (ZMod q) q R).mpr hdiv
  rw [h2] at h1
  have h3 : (a : ZMod q)^2 = - (b : ZMod q)^2 := eq_neg_of_add_eq_zero_left h1
  have h4 : (b : ZMod q) = 0 := by
    by_contra hb
    exact (ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hb h3) hq3
  have h5 : q ∣ b := (CharP.cast_eq_zero_iff (ZMod q) q b).mp h4
  have h6 : (a : ZMod q) = 0 := by
    rw [h4] at h3
    have hz : (- (0 : ZMod q)^2) = (0 : ZMod q) := by rw [sq, mul_zero, neg_zero]
    rw [hz] at h3
    exact sq_eq_zero_iff.mp h3
  have h7 : q ∣ a := (CharP.cast_eq_zero_iff (ZMod q) q a).mp h6
  refine ⟨h7, h5, ?_⟩
  rcases h7 with ⟨m, rfl⟩
  rcases h5 with ⟨k, rfl⟩
  have h8 : (q * m)^2 + (q * k)^2 = q^2 * (m^2 + k^2) := by ring
  rw [h8] at h
  have hq_pos : q > 0 := hq.pos
  have hq2_pos : q^2 > 0 := by positivity
  rw [Nat.mul_div_cancel_left m hq_pos, Nat.mul_div_cancel_left k hq_pos]
  rw [← h]
  exact (Nat.mul_div_cancel_left _ hq2_pos).symm

lemma no_sum_two_squares {R q : ℕ} (hq : q.Prime) (hq3 : q % 4 = 3) (hdiv : q ∣ R) (hndiv : ¬ q^2 ∣ R) (a b : ℕ) : a^2 + b^2 ≠ R := by
  intro h
  have step := sum_two_squares_step hq hq3 h hdiv
  rcases step with ⟨hqa, hqb, hr⟩
  rcases hqa with ⟨m, rfl⟩
  rcases hqb with ⟨k, rfl⟩
  have h8 : (q * m)^2 + (q * k)^2 = q^2 * (m^2 + k^2) := by ring
  rw [h8] at h
  have hndiv2 : q^2 ∣ R := by use (m^2 + k^2); exact h.symm
  exact hndiv hndiv2

lemma no_solution (a b c d : ℕ) : a^2 + b^2 + (2*c+1).choose c + (2*d+1).choose d ≠ 800322180 := by
  intro h
  have hc : c ≤ 16 := by
    by_contra hgt
    have h17 : c ≥ 17 := by omega
    have hB : (2*c+1).choose c > 800322180 := B_mono h17
    omega
  have hd : d ≤ 16 := by
    by_contra hgt
    have h17 : d ≥ 17 := by omega
    have hB : (2*d+1).choose d > 800322180 := B_mono h17
    omega
  revert a b h
  interval_cases c <;> interval_cases d
  · intro a b h
    have hq : Nat.Prime 647 := by norm_num
    have hq3 : 647 % 4 = 3 := by norm_num
    have eqC : (2*0+1).choose 0 = 1 := by decide
    have eqD : (2*0+1).choose 0 = 1 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322178 := by omega
    have hdiv_end : 647 ∣ 800322178 := by norm_num
    have hndiv_end : ¬ 647^2 ∣ 800322178 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 163 := by norm_num
    have hq3 : 163 % 4 = 3 := by norm_num
    have eqC : (2*0+1).choose 0 = 1 := by decide
    have eqD : (2*1+1).choose 1 = 3 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322176 := by omega
    have hdiv_end : 163 ∣ 800322176 := by norm_num
    have hndiv_end : ¬ 163^2 ∣ 800322176 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 67 := by norm_num
    have hq3 : 67 % 4 = 3 := by norm_num
    have eqC : (2*0+1).choose 0 = 1 := by decide
    have eqD : (2*2+1).choose 2 = 10 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322169 := by omega
    have hdiv_end : 67 ∣ 800322169 := by norm_num
    have hndiv_end : ¬ 67^2 ∣ 800322169 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*0+1).choose 0 = 1 := by decide
    have eqD : (2*3+1).choose 3 = 35 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322144 := by omega
    have hdiv_end : 3 ∣ 800322144 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800322144 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 23 := by norm_num
    have hq3 : 23 % 4 = 3 := by norm_num
    have eqC : (2*0+1).choose 0 = 1 := by decide
    have eqD : (2*4+1).choose 4 = 126 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322053 := by omega
    have hdiv_end : 23 ∣ 800322053 := by norm_num
    have hndiv_end : ¬ 23^2 ∣ 800322053 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 467 := by norm_num
    have hq3 : 467 % 4 = 3 := by norm_num
    have eqC : (2*0+1).choose 0 = 1 := by decide
    have eqD : (2*5+1).choose 5 = 462 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800321717 := by omega
    have hdiv_end : 467 ∣ 800321717 := by norm_num
    have hndiv_end : ¬ 467^2 ∣ 800321717 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 223 := by norm_num
    have hq3 : 223 % 4 = 3 := by norm_num
    have eqC : (2*0+1).choose 0 = 1 := by decide
    have eqD : (2*6+1).choose 6 = 1716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800320463 := by omega
    have hdiv_end : 223 ∣ 800320463 := by norm_num
    have hndiv_end : ¬ 223^2 ∣ 800320463 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 991 := by norm_num
    have hq3 : 991 % 4 = 3 := by norm_num
    have eqC : (2*0+1).choose 0 = 1 := by decide
    have eqD : (2*7+1).choose 7 = 6435 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800315744 := by omega
    have hdiv_end : 991 ∣ 800315744 := by norm_num
    have hndiv_end : ¬ 991^2 ∣ 800315744 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*0+1).choose 0 = 1 := by decide
    have eqD : (2*8+1).choose 8 = 24310 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800297869 := by omega
    have hdiv_end : 7 ∣ 800297869 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 800297869 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*0+1).choose 0 = 1 := by decide
    have eqD : (2*9+1).choose 9 = 92378 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800229801 := by omega
    have hdiv_end : 3 ∣ 800229801 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800229801 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 23 := by norm_num
    have hq3 : 23 % 4 = 3 := by norm_num
    have eqC : (2*0+1).choose 0 = 1 := by decide
    have eqD : (2*10+1).choose 10 = 352716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 799969463 := by omega
    have hdiv_end : 23 ∣ 799969463 := by norm_num
    have hndiv_end : ¬ 23^2 ∣ 799969463 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*0+1).choose 0 = 1 := by decide
    have eqD : (2*11+1).choose 11 = 1352078 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798970101 := by omega
    have hdiv_end : 3 ∣ 798970101 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 798970101 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 887 := by norm_num
    have hq3 : 887 % 4 = 3 := by norm_num
    have eqC : (2*0+1).choose 0 = 1 := by decide
    have eqD : (2*12+1).choose 12 = 5200300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 795121879 := by omega
    have hdiv_end : 887 ∣ 795121879 := by norm_num
    have hndiv_end : ¬ 887^2 ∣ 795121879 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 26905651 := by norm_num
    have hq3 : 26905651 % 4 = 3 := by norm_num
    have eqC : (2*0+1).choose 0 = 1 := by decide
    have eqD : (2*13+1).choose 13 = 20058300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 780263879 := by omega
    have hdiv_end : 26905651 ∣ 780263879 := by norm_num
    have hndiv_end : ¬ 26905651^2 ∣ 780263879 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*0+1).choose 0 = 1 := by decide
    have eqD : (2*14+1).choose 14 = 77558760 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722763419 := by omega
    have hdiv_end : 7 ∣ 722763419 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 722763419 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 1999 := by norm_num
    have hq3 : 1999 % 4 = 3 := by norm_num
    have eqC : (2*0+1).choose 0 = 1 := by decide
    have eqD : (2*15+1).choose 15 = 300540195 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499781984 := by omega
    have hdiv_end : 1999 ∣ 499781984 := by norm_num
    have hndiv_end : ¬ 1999^2 ∣ 499781984 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have eqC : (2*0+1).choose 0 = 1 := by decide
    have eqD : (2*16+1).choose 16 = 1166803110 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have hq : Nat.Prime 163 := by norm_num
    have hq3 : 163 % 4 = 3 := by norm_num
    have eqC : (2*1+1).choose 1 = 3 := by decide
    have eqD : (2*0+1).choose 0 = 1 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322176 := by omega
    have hdiv_end : 163 ∣ 800322176 := by norm_num
    have hndiv_end : ¬ 163^2 ∣ 800322176 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*1+1).choose 1 = 3 := by decide
    have eqD : (2*1+1).choose 1 = 3 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322174 := by omega
    have hdiv_0 : 3 ∣ 800322174 := by norm_num
    have hstep_0 := sum_two_squares_step hq hq3 hr_0 hdiv_0
    rcases hstep_0 with ⟨-, -, hr_1⟩
    have hdiv_end : 3 ∣ 88924686 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 88924686 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_1
  · intro a b h
    have hq : Nat.Prime 643 := by norm_num
    have hq3 : 643 % 4 = 3 := by norm_num
    have eqC : (2*1+1).choose 1 = 3 := by decide
    have eqD : (2*2+1).choose 2 = 10 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322167 := by omega
    have hdiv_end : 643 ∣ 800322167 := by norm_num
    have hndiv_end : ¬ 643^2 ∣ 800322167 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*1+1).choose 1 = 3 := by decide
    have eqD : (2*3+1).choose 3 = 35 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322142 := by omega
    have hdiv_end : 19 ∣ 800322142 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 800322142 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*1+1).choose 1 = 3 := by decide
    have eqD : (2*4+1).choose 4 = 126 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322051 := by omega
    have hdiv_end : 3 ∣ 800322051 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800322051 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*1+1).choose 1 = 3 := by decide
    have eqD : (2*5+1).choose 5 = 462 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800321715 := by omega
    have hdiv_0 : 3 ∣ 800321715 := by norm_num
    have hstep_0 := sum_two_squares_step hq hq3 hr_0 hdiv_0
    rcases hstep_0 with ⟨-, -, hr_1⟩
    have hdiv_1 : 3 ∣ 88924635 := by norm_num
    have hstep_1 := sum_two_squares_step hq hq3 hr_1 hdiv_1
    rcases hstep_1 with ⟨-, -, hr_2⟩
    have hdiv_2 : 3 ∣ 9880515 := by norm_num
    have hstep_2 := sum_two_squares_step hq hq3 hr_2 hdiv_2
    rcases hstep_2 with ⟨-, -, hr_3⟩
    have hdiv_end : 3 ∣ 1097835 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 1097835 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_3
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*1+1).choose 1 = 3 := by decide
    have eqD : (2*6+1).choose 6 = 1716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800320461 := by omega
    have hdiv_end : 3 ∣ 800320461 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800320461 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*1+1).choose 1 = 3 := by decide
    have eqD : (2*7+1).choose 7 = 6435 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800315742 := by omega
    have hdiv_end : 3 ∣ 800315742 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800315742 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 78607 := by norm_num
    have hq3 : 78607 % 4 = 3 := by norm_num
    have eqC : (2*1+1).choose 1 = 3 := by decide
    have eqD : (2*8+1).choose 8 = 24310 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800297867 := by omega
    have hdiv_end : 78607 ∣ 800297867 := by norm_num
    have hndiv_end : ¬ 78607^2 ∣ 800297867 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 27594131 := by norm_num
    have hq3 : 27594131 % 4 = 3 := by norm_num
    have eqC : (2*1+1).choose 1 = 3 := by decide
    have eqD : (2*9+1).choose 9 = 92378 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800229799 := by omega
    have hdiv_end : 27594131 ∣ 800229799 := by norm_num
    have hndiv_end : ¬ 27594131^2 ∣ 800229799 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*1+1).choose 1 = 3 := by decide
    have eqD : (2*10+1).choose 10 = 352716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 799969461 := by omega
    have hdiv_end : 3 ∣ 799969461 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 799969461 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 31 := by norm_num
    have hq3 : 31 % 4 = 3 := by norm_num
    have eqC : (2*1+1).choose 1 = 3 := by decide
    have eqD : (2*11+1).choose 11 = 1352078 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798970099 := by omega
    have hdiv_end : 31 ∣ 798970099 := by norm_num
    have hndiv_end : ¬ 31^2 ∣ 798970099 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 11 := by norm_num
    have hq3 : 11 % 4 = 3 := by norm_num
    have eqC : (2*1+1).choose 1 = 3 := by decide
    have eqD : (2*12+1).choose 12 = 5200300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 795121877 := by omega
    have hdiv_end : 11 ∣ 795121877 := by norm_num
    have hndiv_end : ¬ 11^2 ∣ 795121877 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*1+1).choose 1 = 3 := by decide
    have eqD : (2*13+1).choose 13 = 20058300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 780263877 := by omega
    have hdiv_end : 3 ∣ 780263877 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 780263877 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*1+1).choose 1 = 3 := by decide
    have eqD : (2*14+1).choose 14 = 77558760 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722763417 := by omega
    have hdiv_end : 3 ∣ 722763417 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 722763417 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*1+1).choose 1 = 3 := by decide
    have eqD : (2*15+1).choose 15 = 300540195 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499781982 := by omega
    have hdiv_end : 3 ∣ 499781982 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 499781982 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have eqC : (2*1+1).choose 1 = 3 := by decide
    have eqD : (2*16+1).choose 16 = 1166803110 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have hq : Nat.Prime 67 := by norm_num
    have hq3 : 67 % 4 = 3 := by norm_num
    have eqC : (2*2+1).choose 2 = 10 := by decide
    have eqD : (2*0+1).choose 0 = 1 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322169 := by omega
    have hdiv_end : 67 ∣ 800322169 := by norm_num
    have hndiv_end : ¬ 67^2 ∣ 800322169 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 643 := by norm_num
    have hq3 : 643 % 4 = 3 := by norm_num
    have eqC : (2*2+1).choose 2 = 10 := by decide
    have eqD : (2*1+1).choose 1 = 3 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322167 := by omega
    have hdiv_end : 643 ∣ 800322167 := by norm_num
    have hndiv_end : ¬ 643^2 ∣ 800322167 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 11 := by norm_num
    have hq3 : 11 % 4 = 3 := by norm_num
    have eqC : (2*2+1).choose 2 = 10 := by decide
    have eqD : (2*2+1).choose 2 = 10 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322160 := by omega
    have hdiv_end : 11 ∣ 800322160 := by norm_num
    have hndiv_end : ¬ 11^2 ∣ 800322160 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*2+1).choose 2 = 10 := by decide
    have eqD : (2*3+1).choose 3 = 35 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322135 := by omega
    have hdiv_end : 3 ∣ 800322135 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800322135 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 200080511 := by norm_num
    have hq3 : 200080511 % 4 = 3 := by norm_num
    have eqC : (2*2+1).choose 2 = 10 := by decide
    have eqD : (2*4+1).choose 4 = 126 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322044 := by omega
    have hdiv_end : 200080511 ∣ 800322044 := by norm_num
    have hndiv_end : ¬ 200080511^2 ∣ 800322044 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 23 := by norm_num
    have hq3 : 23 % 4 = 3 := by norm_num
    have eqC : (2*2+1).choose 2 = 10 := by decide
    have eqD : (2*5+1).choose 5 = 462 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800321708 := by omega
    have hdiv_end : 23 ∣ 800321708 := by norm_num
    have hndiv_end : ¬ 23^2 ∣ 800321708 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 284003 := by norm_num
    have hq3 : 284003 % 4 = 3 := by norm_num
    have eqC : (2*2+1).choose 2 = 10 := by decide
    have eqD : (2*6+1).choose 6 = 1716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800320454 := by omega
    have hdiv_end : 284003 ∣ 800320454 := by norm_num
    have hndiv_end : ¬ 284003^2 ∣ 800320454 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 4326031 := by norm_num
    have hq3 : 4326031 % 4 = 3 := by norm_num
    have eqC : (2*2+1).choose 2 = 10 := by decide
    have eqD : (2*7+1).choose 7 = 6435 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800315735 := by omega
    have hdiv_end : 4326031 ∣ 800315735 := by norm_num
    have hndiv_end : ¬ 4326031^2 ∣ 800315735 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*2+1).choose 2 = 10 := by decide
    have eqD : (2*8+1).choose 8 = 24310 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800297860 := by omega
    have hdiv_end : 19 ∣ 800297860 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 800297860 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*2+1).choose 2 = 10 := by decide
    have eqD : (2*9+1).choose 9 = 92378 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800229792 := by omega
    have hdiv_end : 3 ∣ 800229792 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800229792 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 399984727 := by norm_num
    have hq3 : 399984727 % 4 = 3 := by norm_num
    have eqC : (2*2+1).choose 2 = 10 := by decide
    have eqD : (2*10+1).choose 10 = 352716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 799969454 := by omega
    have hdiv_end : 399984727 ∣ 799969454 := by norm_num
    have hndiv_end : ¬ 399984727^2 ∣ 799969454 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*2+1).choose 2 = 10 := by decide
    have eqD : (2*11+1).choose 11 = 1352078 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798970092 := by omega
    have hdiv_end : 3 ∣ 798970092 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 798970092 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 79512187 := by norm_num
    have hq3 : 79512187 % 4 = 3 := by norm_num
    have eqC : (2*2+1).choose 2 = 10 := by decide
    have eqD : (2*12+1).choose 12 = 5200300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 795121870 := by omega
    have hdiv_end : 79512187 ∣ 795121870 := by norm_num
    have hndiv_end : ¬ 79512187^2 ∣ 795121870 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 127 := by norm_num
    have hq3 : 127 % 4 = 3 := by norm_num
    have eqC : (2*2+1).choose 2 = 10 := by decide
    have eqD : (2*13+1).choose 13 = 20058300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 780263870 := by omega
    have hdiv_end : 127 ∣ 780263870 := by norm_num
    have hndiv_end : ¬ 127^2 ∣ 780263870 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 2819 := by norm_num
    have hq3 : 2819 % 4 = 3 := by norm_num
    have eqC : (2*2+1).choose 2 = 10 := by decide
    have eqD : (2*14+1).choose 14 = 77558760 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722763410 := by omega
    have hdiv_end : 2819 ∣ 722763410 := by norm_num
    have hndiv_end : ¬ 2819^2 ∣ 722763410 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*2+1).choose 2 = 10 := by decide
    have eqD : (2*15+1).choose 15 = 300540195 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499781975 := by omega
    have hdiv_end : 7 ∣ 499781975 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 499781975 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have eqC : (2*2+1).choose 2 = 10 := by decide
    have eqD : (2*16+1).choose 16 = 1166803110 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*3+1).choose 3 = 35 := by decide
    have eqD : (2*0+1).choose 0 = 1 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322144 := by omega
    have hdiv_end : 3 ∣ 800322144 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800322144 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*3+1).choose 3 = 35 := by decide
    have eqD : (2*1+1).choose 1 = 3 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322142 := by omega
    have hdiv_end : 19 ∣ 800322142 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 800322142 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*3+1).choose 3 = 35 := by decide
    have eqD : (2*2+1).choose 2 = 10 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322135 := by omega
    have hdiv_end : 3 ∣ 800322135 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800322135 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*3+1).choose 3 = 35 := by decide
    have eqD : (2*3+1).choose 3 = 35 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322110 := by omega
    have hdiv_end : 7 ∣ 800322110 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 800322110 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*3+1).choose 3 = 35 := by decide
    have eqD : (2*4+1).choose 4 = 126 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322019 := by omega
    have hdiv_end : 7 ∣ 800322019 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 800322019 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*3+1).choose 3 = 35 := by decide
    have eqD : (2*5+1).choose 5 = 462 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800321683 := by omega
    have hdiv_end : 7 ∣ 800321683 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 800321683 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 43 := by norm_num
    have hq3 : 43 % 4 = 3 := by norm_num
    have eqC : (2*3+1).choose 3 = 35 := by decide
    have eqD : (2*6+1).choose 6 = 1716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800320429 := by omega
    have hdiv_end : 43 ∣ 800320429 := by norm_num
    have hndiv_end : ¬ 43^2 ∣ 800320429 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 5843 := by norm_num
    have hq3 : 5843 % 4 = 3 := by norm_num
    have eqC : (2*3+1).choose 3 = 35 := by decide
    have eqD : (2*7+1).choose 7 = 6435 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800315710 := by omega
    have hdiv_end : 5843 ∣ 800315710 := by norm_num
    have hndiv_end : ¬ 5843^2 ∣ 800315710 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*3+1).choose 3 = 35 := by decide
    have eqD : (2*8+1).choose 8 = 24310 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800297835 := by omega
    have hdiv_end : 3 ∣ 800297835 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800297835 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7923067 := by norm_num
    have hq3 : 7923067 % 4 = 3 := by norm_num
    have eqC : (2*3+1).choose 3 = 35 := by decide
    have eqD : (2*9+1).choose 9 = 92378 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800229767 := by omega
    have hdiv_end : 7923067 ∣ 800229767 := by norm_num
    have hndiv_end : ¬ 7923067^2 ∣ 800229767 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*3+1).choose 3 = 35 := by decide
    have eqD : (2*10+1).choose 10 = 352716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 799969429 := by omega
    have hdiv_end : 7 ∣ 799969429 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 799969429 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*3+1).choose 3 = 35 := by decide
    have eqD : (2*11+1).choose 11 = 1352078 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798970067 := by omega
    have hdiv_end : 7 ∣ 798970067 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 798970067 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*3+1).choose 3 = 35 := by decide
    have eqD : (2*12+1).choose 12 = 5200300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 795121845 := by omega
    have hdiv_end : 3 ∣ 795121845 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 795121845 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 23 := by norm_num
    have hq3 : 23 % 4 = 3 := by norm_num
    have eqC : (2*3+1).choose 3 = 35 := by decide
    have eqD : (2*13+1).choose 13 = 20058300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 780263845 := by omega
    have hdiv_end : 23 ∣ 780263845 := by norm_num
    have hndiv_end : ¬ 23^2 ∣ 780263845 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 23 := by norm_num
    have hq3 : 23 % 4 = 3 := by norm_num
    have eqC : (2*3+1).choose 3 = 35 := by decide
    have eqD : (2*14+1).choose 14 = 77558760 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722763385 := by omega
    have hdiv_end : 23 ∣ 722763385 := by norm_num
    have hndiv_end : ¬ 23^2 ∣ 722763385 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 23 := by norm_num
    have hq3 : 23 % 4 = 3 := by norm_num
    have eqC : (2*3+1).choose 3 = 35 := by decide
    have eqD : (2*15+1).choose 15 = 300540195 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499781950 := by omega
    have hdiv_end : 23 ∣ 499781950 := by norm_num
    have hndiv_end : ¬ 23^2 ∣ 499781950 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have eqC : (2*3+1).choose 3 = 35 := by decide
    have eqD : (2*16+1).choose 16 = 1166803110 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have hq : Nat.Prime 23 := by norm_num
    have hq3 : 23 % 4 = 3 := by norm_num
    have eqC : (2*4+1).choose 4 = 126 := by decide
    have eqD : (2*0+1).choose 0 = 1 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322053 := by omega
    have hdiv_end : 23 ∣ 800322053 := by norm_num
    have hndiv_end : ¬ 23^2 ∣ 800322053 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*4+1).choose 4 = 126 := by decide
    have eqD : (2*1+1).choose 1 = 3 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322051 := by omega
    have hdiv_end : 3 ∣ 800322051 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800322051 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 200080511 := by norm_num
    have hq3 : 200080511 % 4 = 3 := by norm_num
    have eqC : (2*4+1).choose 4 = 126 := by decide
    have eqD : (2*2+1).choose 2 = 10 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322044 := by omega
    have hdiv_end : 200080511 ∣ 800322044 := by norm_num
    have hndiv_end : ¬ 200080511^2 ∣ 800322044 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*4+1).choose 4 = 126 := by decide
    have eqD : (2*3+1).choose 3 = 35 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800322019 := by omega
    have hdiv_end : 7 ∣ 800322019 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 800322019 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*4+1).choose 4 = 126 := by decide
    have eqD : (2*4+1).choose 4 = 126 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800321928 := by omega
    have hdiv_end : 3 ∣ 800321928 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800321928 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*4+1).choose 4 = 126 := by decide
    have eqD : (2*5+1).choose 5 = 462 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800321592 := by omega
    have hdiv_end : 3 ∣ 800321592 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800321592 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 719 := by norm_num
    have hq3 : 719 % 4 = 3 := by norm_num
    have eqC : (2*4+1).choose 4 = 126 := by decide
    have eqD : (2*6+1).choose 6 = 1716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800320338 := by omega
    have hdiv_end : 719 ∣ 800320338 := by norm_num
    have hndiv_end : ¬ 719^2 ∣ 800320338 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*4+1).choose 4 = 126 := by decide
    have eqD : (2*7+1).choose 7 = 6435 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800315619 := by omega
    have hdiv_end : 3 ∣ 800315619 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800315619 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 563 := by norm_num
    have hq3 : 563 % 4 = 3 := by norm_num
    have eqC : (2*4+1).choose 4 = 126 := by decide
    have eqD : (2*8+1).choose 8 = 24310 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800297744 := by omega
    have hdiv_end : 563 ∣ 800297744 := by norm_num
    have hndiv_end : ¬ 563^2 ∣ 800297744 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 200057419 := by norm_num
    have hq3 : 200057419 % 4 = 3 := by norm_num
    have eqC : (2*4+1).choose 4 = 126 := by decide
    have eqD : (2*9+1).choose 9 = 92378 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800229676 := by omega
    have hdiv_end : 200057419 ∣ 800229676 := by norm_num
    have hndiv_end : ¬ 200057419^2 ∣ 800229676 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*4+1).choose 4 = 126 := by decide
    have eqD : (2*10+1).choose 10 = 352716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 799969338 := by omega
    have hdiv_0 : 3 ∣ 799969338 := by norm_num
    have hstep_0 := sum_two_squares_step hq hq3 hr_0 hdiv_0
    rcases hstep_0 with ⟨-, -, hr_1⟩
    have hdiv_end : 3 ∣ 88885482 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 88885482 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_1
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*4+1).choose 4 = 126 := by decide
    have eqD : (2*11+1).choose 11 = 1352078 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798969976 := by omega
    have hdiv_end : 7 ∣ 798969976 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 798969976 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*4+1).choose 4 = 126 := by decide
    have eqD : (2*12+1).choose 12 = 5200300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 795121754 := by omega
    have hdiv_end : 7 ∣ 795121754 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 795121754 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*4+1).choose 4 = 126 := by decide
    have eqD : (2*13+1).choose 13 = 20058300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 780263754 := by omega
    have hdiv_end : 3 ∣ 780263754 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 780263754 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*4+1).choose 4 = 126 := by decide
    have eqD : (2*14+1).choose 14 = 77558760 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722763294 := by omega
    have hdiv_end : 3 ∣ 722763294 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 722763294 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*4+1).choose 4 = 126 := by decide
    have eqD : (2*15+1).choose 15 = 300540195 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499781859 := by omega
    have hdiv_end : 3 ∣ 499781859 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 499781859 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have eqC : (2*4+1).choose 4 = 126 := by decide
    have eqD : (2*16+1).choose 16 = 1166803110 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have hq : Nat.Prime 467 := by norm_num
    have hq3 : 467 % 4 = 3 := by norm_num
    have eqC : (2*5+1).choose 5 = 462 := by decide
    have eqD : (2*0+1).choose 0 = 1 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800321717 := by omega
    have hdiv_end : 467 ∣ 800321717 := by norm_num
    have hndiv_end : ¬ 467^2 ∣ 800321717 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*5+1).choose 5 = 462 := by decide
    have eqD : (2*1+1).choose 1 = 3 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800321715 := by omega
    have hdiv_0 : 3 ∣ 800321715 := by norm_num
    have hstep_0 := sum_two_squares_step hq hq3 hr_0 hdiv_0
    rcases hstep_0 with ⟨-, -, hr_1⟩
    have hdiv_1 : 3 ∣ 88924635 := by norm_num
    have hstep_1 := sum_two_squares_step hq hq3 hr_1 hdiv_1
    rcases hstep_1 with ⟨-, -, hr_2⟩
    have hdiv_2 : 3 ∣ 9880515 := by norm_num
    have hstep_2 := sum_two_squares_step hq hq3 hr_2 hdiv_2
    rcases hstep_2 with ⟨-, -, hr_3⟩
    have hdiv_end : 3 ∣ 1097835 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 1097835 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_3
  · intro a b h
    have hq : Nat.Prime 23 := by norm_num
    have hq3 : 23 % 4 = 3 := by norm_num
    have eqC : (2*5+1).choose 5 = 462 := by decide
    have eqD : (2*2+1).choose 2 = 10 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800321708 := by omega
    have hdiv_end : 23 ∣ 800321708 := by norm_num
    have hndiv_end : ¬ 23^2 ∣ 800321708 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*5+1).choose 5 = 462 := by decide
    have eqD : (2*3+1).choose 3 = 35 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800321683 := by omega
    have hdiv_end : 7 ∣ 800321683 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 800321683 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*5+1).choose 5 = 462 := by decide
    have eqD : (2*4+1).choose 4 = 126 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800321592 := by omega
    have hdiv_end : 3 ∣ 800321592 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800321592 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*5+1).choose 5 = 462 := by decide
    have eqD : (2*5+1).choose 5 = 462 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800321256 := by omega
    have hdiv_0 : 3 ∣ 800321256 := by norm_num
    have hstep_0 := sum_two_squares_step hq hq3 hr_0 hdiv_0
    rcases hstep_0 with ⟨-, -, hr_1⟩
    have hdiv_end : 3 ∣ 88924584 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 88924584 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_1
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*5+1).choose 5 = 462 := by decide
    have eqD : (2*6+1).choose 6 = 1716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800320002 := by omega
    have hdiv_end : 3 ∣ 800320002 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800320002 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*5+1).choose 5 = 462 := by decide
    have eqD : (2*7+1).choose 7 = 6435 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800315283 := by omega
    have hdiv_end : 3 ∣ 800315283 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800315283 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 12504647 := by norm_num
    have hq3 : 12504647 % 4 = 3 := by norm_num
    have eqC : (2*5+1).choose 5 = 462 := by decide
    have eqD : (2*8+1).choose 8 = 24310 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800297408 := by omega
    have hdiv_end : 12504647 ∣ 800297408 := by norm_num
    have hndiv_end : ¬ 12504647^2 ∣ 800297408 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 23 := by norm_num
    have hq3 : 23 % 4 = 3 := by norm_num
    have eqC : (2*5+1).choose 5 = 462 := by decide
    have eqD : (2*9+1).choose 9 = 92378 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800229340 := by omega
    have hdiv_end : 23 ∣ 800229340 := by norm_num
    have hndiv_end : ¬ 23^2 ∣ 800229340 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*5+1).choose 5 = 462 := by decide
    have eqD : (2*10+1).choose 10 = 352716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 799969002 := by omega
    have hdiv_end : 3 ∣ 799969002 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 799969002 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*5+1).choose 5 = 462 := by decide
    have eqD : (2*11+1).choose 11 = 1352078 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798969640 := by omega
    have hdiv_end : 7 ∣ 798969640 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 798969640 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*5+1).choose 5 = 462 := by decide
    have eqD : (2*12+1).choose 12 = 5200300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 795121418 := by omega
    have hdiv_end : 7 ∣ 795121418 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 795121418 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*5+1).choose 5 = 462 := by decide
    have eqD : (2*13+1).choose 13 = 20058300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 780263418 := by omega
    have hdiv_end : 3 ∣ 780263418 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 780263418 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*5+1).choose 5 = 462 := by decide
    have eqD : (2*14+1).choose 14 = 77558760 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722762958 := by omega
    have hdiv_end : 3 ∣ 722762958 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 722762958 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*5+1).choose 5 = 462 := by decide
    have eqD : (2*15+1).choose 15 = 300540195 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499781523 := by omega
    have hdiv_end : 3 ∣ 499781523 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 499781523 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have eqC : (2*5+1).choose 5 = 462 := by decide
    have eqD : (2*16+1).choose 16 = 1166803110 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have hq : Nat.Prime 223 := by norm_num
    have hq3 : 223 % 4 = 3 := by norm_num
    have eqC : (2*6+1).choose 6 = 1716 := by decide
    have eqD : (2*0+1).choose 0 = 1 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800320463 := by omega
    have hdiv_end : 223 ∣ 800320463 := by norm_num
    have hndiv_end : ¬ 223^2 ∣ 800320463 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*6+1).choose 6 = 1716 := by decide
    have eqD : (2*1+1).choose 1 = 3 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800320461 := by omega
    have hdiv_end : 3 ∣ 800320461 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800320461 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 284003 := by norm_num
    have hq3 : 284003 % 4 = 3 := by norm_num
    have eqC : (2*6+1).choose 6 = 1716 := by decide
    have eqD : (2*2+1).choose 2 = 10 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800320454 := by omega
    have hdiv_end : 284003 ∣ 800320454 := by norm_num
    have hndiv_end : ¬ 284003^2 ∣ 800320454 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 43 := by norm_num
    have hq3 : 43 % 4 = 3 := by norm_num
    have eqC : (2*6+1).choose 6 = 1716 := by decide
    have eqD : (2*3+1).choose 3 = 35 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800320429 := by omega
    have hdiv_end : 43 ∣ 800320429 := by norm_num
    have hndiv_end : ¬ 43^2 ∣ 800320429 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 719 := by norm_num
    have hq3 : 719 % 4 = 3 := by norm_num
    have eqC : (2*6+1).choose 6 = 1716 := by decide
    have eqD : (2*4+1).choose 4 = 126 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800320338 := by omega
    have hdiv_end : 719 ∣ 800320338 := by norm_num
    have hndiv_end : ¬ 719^2 ∣ 800320338 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*6+1).choose 6 = 1716 := by decide
    have eqD : (2*5+1).choose 5 = 462 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800320002 := by omega
    have hdiv_end : 3 ∣ 800320002 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800320002 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*6+1).choose 6 = 1716 := by decide
    have eqD : (2*6+1).choose 6 = 1716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800318748 := by omega
    have hdiv_end : 3 ∣ 800318748 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800318748 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*6+1).choose 6 = 1716 := by decide
    have eqD : (2*7+1).choose 7 = 6435 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800314029 := by omega
    have hdiv_end : 19 ∣ 800314029 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 800314029 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*6+1).choose 6 = 1716 := by decide
    have eqD : (2*8+1).choose 8 = 24310 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800296154 := by omega
    have hdiv_end : 7 ∣ 800296154 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 800296154 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*6+1).choose 6 = 1716 := by decide
    have eqD : (2*9+1).choose 9 = 92378 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800228086 := by omega
    have hdiv_end : 7 ∣ 800228086 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 800228086 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*6+1).choose 6 = 1716 := by decide
    have eqD : (2*10+1).choose 10 = 352716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 799967748 := by omega
    have hdiv_end : 3 ∣ 799967748 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 799967748 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 139 := by norm_num
    have hq3 : 139 % 4 = 3 := by norm_num
    have eqC : (2*6+1).choose 6 = 1716 := by decide
    have eqD : (2*11+1).choose 11 = 1352078 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798968386 := by omega
    have hdiv_end : 139 ∣ 798968386 := by norm_num
    have hndiv_end : ¬ 139^2 ∣ 798968386 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 227 := by norm_num
    have hq3 : 227 % 4 = 3 := by norm_num
    have eqC : (2*6+1).choose 6 = 1716 := by decide
    have eqD : (2*12+1).choose 12 = 5200300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 795120164 := by omega
    have hdiv_end : 227 ∣ 795120164 := by norm_num
    have hndiv_end : ¬ 227^2 ∣ 795120164 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 11 := by norm_num
    have hq3 : 11 % 4 = 3 := by norm_num
    have eqC : (2*6+1).choose 6 = 1716 := by decide
    have eqD : (2*13+1).choose 13 = 20058300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 780262164 := by omega
    have hdiv_end : 11 ∣ 780262164 := by norm_num
    have hndiv_end : ¬ 11^2 ∣ 780262164 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*6+1).choose 6 = 1716 := by decide
    have eqD : (2*14+1).choose 14 = 77558760 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722761704 := by omega
    have hdiv_0 : 3 ∣ 722761704 := by norm_num
    have hstep_0 := sum_two_squares_step hq hq3 hr_0 hdiv_0
    rcases hstep_0 with ⟨-, -, hr_1⟩
    have hdiv_1 : 3 ∣ 80306856 := by norm_num
    have hstep_1 := sum_two_squares_step hq hq3 hr_1 hdiv_1
    rcases hstep_1 with ⟨-, -, hr_2⟩
    have hdiv_end : 3 ∣ 8922984 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 8922984 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_2
  · intro a b h
    have hq : Nat.Prime 67 := by norm_num
    have hq3 : 67 % 4 = 3 := by norm_num
    have eqC : (2*6+1).choose 6 = 1716 := by decide
    have eqD : (2*15+1).choose 15 = 300540195 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499780269 := by omega
    have hdiv_end : 67 ∣ 499780269 := by norm_num
    have hndiv_end : ¬ 67^2 ∣ 499780269 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have eqC : (2*6+1).choose 6 = 1716 := by decide
    have eqD : (2*16+1).choose 16 = 1166803110 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have hq : Nat.Prime 991 := by norm_num
    have hq3 : 991 % 4 = 3 := by norm_num
    have eqC : (2*7+1).choose 7 = 6435 := by decide
    have eqD : (2*0+1).choose 0 = 1 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800315744 := by omega
    have hdiv_end : 991 ∣ 800315744 := by norm_num
    have hndiv_end : ¬ 991^2 ∣ 800315744 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*7+1).choose 7 = 6435 := by decide
    have eqD : (2*1+1).choose 1 = 3 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800315742 := by omega
    have hdiv_end : 3 ∣ 800315742 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800315742 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 4326031 := by norm_num
    have hq3 : 4326031 % 4 = 3 := by norm_num
    have eqC : (2*7+1).choose 7 = 6435 := by decide
    have eqD : (2*2+1).choose 2 = 10 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800315735 := by omega
    have hdiv_end : 4326031 ∣ 800315735 := by norm_num
    have hndiv_end : ¬ 4326031^2 ∣ 800315735 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 5843 := by norm_num
    have hq3 : 5843 % 4 = 3 := by norm_num
    have eqC : (2*7+1).choose 7 = 6435 := by decide
    have eqD : (2*3+1).choose 3 = 35 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800315710 := by omega
    have hdiv_end : 5843 ∣ 800315710 := by norm_num
    have hndiv_end : ¬ 5843^2 ∣ 800315710 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*7+1).choose 7 = 6435 := by decide
    have eqD : (2*4+1).choose 4 = 126 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800315619 := by omega
    have hdiv_end : 3 ∣ 800315619 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800315619 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*7+1).choose 7 = 6435 := by decide
    have eqD : (2*5+1).choose 5 = 462 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800315283 := by omega
    have hdiv_end : 3 ∣ 800315283 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800315283 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*7+1).choose 7 = 6435 := by decide
    have eqD : (2*6+1).choose 6 = 1716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800314029 := by omega
    have hdiv_end : 19 ∣ 800314029 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 800314029 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*7+1).choose 7 = 6435 := by decide
    have eqD : (2*7+1).choose 7 = 6435 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800309310 := by omega
    have hdiv_end : 3 ∣ 800309310 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800309310 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 199 := by norm_num
    have hq3 : 199 % 4 = 3 := by norm_num
    have eqC : (2*7+1).choose 7 = 6435 := by decide
    have eqD : (2*8+1).choose 8 = 24310 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800291435 := by omega
    have hdiv_end : 199 ∣ 800291435 := by norm_num
    have hndiv_end : ¬ 199^2 ∣ 800291435 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 31 := by norm_num
    have hq3 : 31 % 4 = 3 := by norm_num
    have eqC : (2*7+1).choose 7 = 6435 := by decide
    have eqD : (2*9+1).choose 9 = 92378 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800223367 := by omega
    have hdiv_end : 31 ∣ 800223367 := by norm_num
    have hndiv_end : ¬ 31^2 ∣ 800223367 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 31 := by norm_num
    have hq3 : 31 % 4 = 3 := by norm_num
    have eqC : (2*7+1).choose 7 = 6435 := by decide
    have eqD : (2*10+1).choose 10 = 352716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 799963029 := by omega
    have hdiv_end : 31 ∣ 799963029 := by norm_num
    have hndiv_end : ¬ 31^2 ∣ 799963029 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3331 := by norm_num
    have hq3 : 3331 % 4 = 3 := by norm_num
    have eqC : (2*7+1).choose 7 = 6435 := by decide
    have eqD : (2*11+1).choose 11 = 1352078 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798963667 := by omega
    have hdiv_end : 3331 ∣ 798963667 := by norm_num
    have hndiv_end : ¬ 3331^2 ∣ 798963667 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 139 := by norm_num
    have hq3 : 139 % 4 = 3 := by norm_num
    have eqC : (2*7+1).choose 7 = 6435 := by decide
    have eqD : (2*12+1).choose 12 = 5200300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 795115445 := by omega
    have hdiv_end : 139 ∣ 795115445 := by norm_num
    have hndiv_end : ¬ 139^2 ∣ 795115445 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*7+1).choose 7 = 6435 := by decide
    have eqD : (2*13+1).choose 13 = 20058300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 780257445 := by omega
    have hdiv_end : 3 ∣ 780257445 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 780257445 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*7+1).choose 7 = 6435 := by decide
    have eqD : (2*14+1).choose 14 = 77558760 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722756985 := by omega
    have hdiv_end : 3 ∣ 722756985 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 722756985 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*7+1).choose 7 = 6435 := by decide
    have eqD : (2*15+1).choose 15 = 300540195 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499775550 := by omega
    have hdiv_end : 3 ∣ 499775550 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 499775550 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have eqC : (2*7+1).choose 7 = 6435 := by decide
    have eqD : (2*16+1).choose 16 = 1166803110 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*8+1).choose 8 = 24310 := by decide
    have eqD : (2*0+1).choose 0 = 1 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800297869 := by omega
    have hdiv_end : 7 ∣ 800297869 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 800297869 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 78607 := by norm_num
    have hq3 : 78607 % 4 = 3 := by norm_num
    have eqC : (2*8+1).choose 8 = 24310 := by decide
    have eqD : (2*1+1).choose 1 = 3 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800297867 := by omega
    have hdiv_end : 78607 ∣ 800297867 := by norm_num
    have hndiv_end : ¬ 78607^2 ∣ 800297867 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*8+1).choose 8 = 24310 := by decide
    have eqD : (2*2+1).choose 2 = 10 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800297860 := by omega
    have hdiv_end : 19 ∣ 800297860 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 800297860 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*8+1).choose 8 = 24310 := by decide
    have eqD : (2*3+1).choose 3 = 35 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800297835 := by omega
    have hdiv_end : 3 ∣ 800297835 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800297835 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 563 := by norm_num
    have hq3 : 563 % 4 = 3 := by norm_num
    have eqC : (2*8+1).choose 8 = 24310 := by decide
    have eqD : (2*4+1).choose 4 = 126 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800297744 := by omega
    have hdiv_end : 563 ∣ 800297744 := by norm_num
    have hndiv_end : ¬ 563^2 ∣ 800297744 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 12504647 := by norm_num
    have hq3 : 12504647 % 4 = 3 := by norm_num
    have eqC : (2*8+1).choose 8 = 24310 := by decide
    have eqD : (2*5+1).choose 5 = 462 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800297408 := by omega
    have hdiv_end : 12504647 ∣ 800297408 := by norm_num
    have hndiv_end : ¬ 12504647^2 ∣ 800297408 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*8+1).choose 8 = 24310 := by decide
    have eqD : (2*6+1).choose 6 = 1716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800296154 := by omega
    have hdiv_end : 7 ∣ 800296154 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 800296154 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 199 := by norm_num
    have hq3 : 199 % 4 = 3 := by norm_num
    have eqC : (2*8+1).choose 8 = 24310 := by decide
    have eqD : (2*7+1).choose 7 = 6435 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800291435 := by omega
    have hdiv_end : 199 ∣ 800291435 := by norm_num
    have hndiv_end : ¬ 199^2 ∣ 800291435 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 689891 := by norm_num
    have hq3 : 689891 % 4 = 3 := by norm_num
    have eqC : (2*8+1).choose 8 = 24310 := by decide
    have eqD : (2*8+1).choose 8 = 24310 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800273560 := by omega
    have hdiv_end : 689891 ∣ 800273560 := by norm_num
    have hndiv_end : ¬ 689891^2 ∣ 800273560 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*8+1).choose 8 = 24310 := by decide
    have eqD : (2*9+1).choose 9 = 92378 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800205492 := by omega
    have hdiv_end : 3 ∣ 800205492 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800205492 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 223 := by norm_num
    have hq3 : 223 % 4 = 3 := by norm_num
    have eqC : (2*8+1).choose 8 = 24310 := by decide
    have eqD : (2*10+1).choose 10 = 352716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 799945154 := by omega
    have hdiv_end : 223 ∣ 799945154 := by norm_num
    have hndiv_end : ¬ 223^2 ∣ 799945154 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*8+1).choose 8 = 24310 := by decide
    have eqD : (2*11+1).choose 11 = 1352078 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798945792 := by omega
    have hdiv_end : 3 ∣ 798945792 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 798945792 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 59 := by norm_num
    have hq3 : 59 % 4 = 3 := by norm_num
    have eqC : (2*8+1).choose 8 = 24310 := by decide
    have eqD : (2*12+1).choose 12 = 5200300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 795097570 := by omega
    have hdiv_end : 59 ∣ 795097570 := by norm_num
    have hndiv_end : ¬ 59^2 ∣ 795097570 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 11 := by norm_num
    have hq3 : 11 % 4 = 3 := by norm_num
    have eqC : (2*8+1).choose 8 = 24310 := by decide
    have eqD : (2*13+1).choose 13 = 20058300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 780239570 := by omega
    have hdiv_end : 11 ∣ 780239570 := by norm_num
    have hndiv_end : ¬ 11^2 ∣ 780239570 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7591 := by norm_num
    have hq3 : 7591 % 4 = 3 := by norm_num
    have eqC : (2*8+1).choose 8 = 24310 := by decide
    have eqD : (2*14+1).choose 14 = 77558760 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722739110 := by omega
    have hdiv_end : 7591 ∣ 722739110 := by norm_num
    have hndiv_end : ¬ 7591^2 ∣ 722739110 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19990307 := by norm_num
    have hq3 : 19990307 % 4 = 3 := by norm_num
    have eqC : (2*8+1).choose 8 = 24310 := by decide
    have eqD : (2*15+1).choose 15 = 300540195 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499757675 := by omega
    have hdiv_end : 19990307 ∣ 499757675 := by norm_num
    have hndiv_end : ¬ 19990307^2 ∣ 499757675 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have eqC : (2*8+1).choose 8 = 24310 := by decide
    have eqD : (2*16+1).choose 16 = 1166803110 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*9+1).choose 9 = 92378 := by decide
    have eqD : (2*0+1).choose 0 = 1 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800229801 := by omega
    have hdiv_end : 3 ∣ 800229801 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800229801 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 27594131 := by norm_num
    have hq3 : 27594131 % 4 = 3 := by norm_num
    have eqC : (2*9+1).choose 9 = 92378 := by decide
    have eqD : (2*1+1).choose 1 = 3 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800229799 := by omega
    have hdiv_end : 27594131 ∣ 800229799 := by norm_num
    have hndiv_end : ¬ 27594131^2 ∣ 800229799 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*9+1).choose 9 = 92378 := by decide
    have eqD : (2*2+1).choose 2 = 10 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800229792 := by omega
    have hdiv_end : 3 ∣ 800229792 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800229792 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7923067 := by norm_num
    have hq3 : 7923067 % 4 = 3 := by norm_num
    have eqC : (2*9+1).choose 9 = 92378 := by decide
    have eqD : (2*3+1).choose 3 = 35 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800229767 := by omega
    have hdiv_end : 7923067 ∣ 800229767 := by norm_num
    have hndiv_end : ¬ 7923067^2 ∣ 800229767 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 200057419 := by norm_num
    have hq3 : 200057419 % 4 = 3 := by norm_num
    have eqC : (2*9+1).choose 9 = 92378 := by decide
    have eqD : (2*4+1).choose 4 = 126 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800229676 := by omega
    have hdiv_end : 200057419 ∣ 800229676 := by norm_num
    have hndiv_end : ¬ 200057419^2 ∣ 800229676 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 23 := by norm_num
    have hq3 : 23 % 4 = 3 := by norm_num
    have eqC : (2*9+1).choose 9 = 92378 := by decide
    have eqD : (2*5+1).choose 5 = 462 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800229340 := by omega
    have hdiv_end : 23 ∣ 800229340 := by norm_num
    have hndiv_end : ¬ 23^2 ∣ 800229340 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*9+1).choose 9 = 92378 := by decide
    have eqD : (2*6+1).choose 6 = 1716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800228086 := by omega
    have hdiv_end : 7 ∣ 800228086 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 800228086 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 31 := by norm_num
    have hq3 : 31 % 4 = 3 := by norm_num
    have eqC : (2*9+1).choose 9 = 92378 := by decide
    have eqD : (2*7+1).choose 7 = 6435 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800223367 := by omega
    have hdiv_end : 31 ∣ 800223367 := by norm_num
    have hndiv_end : ¬ 31^2 ∣ 800223367 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*9+1).choose 9 = 92378 := by decide
    have eqD : (2*8+1).choose 8 = 24310 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800205492 := by omega
    have hdiv_end : 3 ∣ 800205492 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 800205492 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*9+1).choose 9 = 92378 := by decide
    have eqD : (2*9+1).choose 9 = 92378 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 800137424 := by omega
    have hdiv_end : 19 ∣ 800137424 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 800137424 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 887 := by norm_num
    have hq3 : 887 % 4 = 3 := by norm_num
    have eqC : (2*9+1).choose 9 = 92378 := by decide
    have eqD : (2*10+1).choose 10 = 352716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 799877086 := by omega
    have hdiv_end : 887 ∣ 799877086 := by norm_num
    have hndiv_end : ¬ 887^2 ∣ 799877086 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*9+1).choose 9 = 92378 := by decide
    have eqD : (2*11+1).choose 11 = 1352078 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798877724 := by omega
    have hdiv_end : 19 ∣ 798877724 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 798877724 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*9+1).choose 9 = 92378 := by decide
    have eqD : (2*12+1).choose 12 = 5200300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 795029502 := by omega
    have hdiv_end : 3 ∣ 795029502 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 795029502 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 11 := by norm_num
    have hq3 : 11 % 4 = 3 := by norm_num
    have eqC : (2*9+1).choose 9 = 92378 := by decide
    have eqD : (2*13+1).choose 13 = 20058300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 780171502 := by omega
    have hdiv_end : 11 ∣ 780171502 := by norm_num
    have hndiv_end : ¬ 11^2 ∣ 780171502 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*9+1).choose 9 = 92378 := by decide
    have eqD : (2*14+1).choose 14 = 77558760 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722671042 := by omega
    have hdiv_end : 19 ∣ 722671042 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 722671042 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*9+1).choose 9 = 92378 := by decide
    have eqD : (2*15+1).choose 15 = 300540195 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499689607 := by omega
    have hdiv_end : 19 ∣ 499689607 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 499689607 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have eqC : (2*9+1).choose 9 = 92378 := by decide
    have eqD : (2*16+1).choose 16 = 1166803110 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have hq : Nat.Prime 23 := by norm_num
    have hq3 : 23 % 4 = 3 := by norm_num
    have eqC : (2*10+1).choose 10 = 352716 := by decide
    have eqD : (2*0+1).choose 0 = 1 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 799969463 := by omega
    have hdiv_end : 23 ∣ 799969463 := by norm_num
    have hndiv_end : ¬ 23^2 ∣ 799969463 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*10+1).choose 10 = 352716 := by decide
    have eqD : (2*1+1).choose 1 = 3 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 799969461 := by omega
    have hdiv_end : 3 ∣ 799969461 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 799969461 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 399984727 := by norm_num
    have hq3 : 399984727 % 4 = 3 := by norm_num
    have eqC : (2*10+1).choose 10 = 352716 := by decide
    have eqD : (2*2+1).choose 2 = 10 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 799969454 := by omega
    have hdiv_end : 399984727 ∣ 799969454 := by norm_num
    have hndiv_end : ¬ 399984727^2 ∣ 799969454 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*10+1).choose 10 = 352716 := by decide
    have eqD : (2*3+1).choose 3 = 35 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 799969429 := by omega
    have hdiv_end : 7 ∣ 799969429 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 799969429 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*10+1).choose 10 = 352716 := by decide
    have eqD : (2*4+1).choose 4 = 126 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 799969338 := by omega
    have hdiv_0 : 3 ∣ 799969338 := by norm_num
    have hstep_0 := sum_two_squares_step hq hq3 hr_0 hdiv_0
    rcases hstep_0 with ⟨-, -, hr_1⟩
    have hdiv_end : 3 ∣ 88885482 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 88885482 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_1
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*10+1).choose 10 = 352716 := by decide
    have eqD : (2*5+1).choose 5 = 462 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 799969002 := by omega
    have hdiv_end : 3 ∣ 799969002 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 799969002 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*10+1).choose 10 = 352716 := by decide
    have eqD : (2*6+1).choose 6 = 1716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 799967748 := by omega
    have hdiv_end : 3 ∣ 799967748 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 799967748 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 31 := by norm_num
    have hq3 : 31 % 4 = 3 := by norm_num
    have eqC : (2*10+1).choose 10 = 352716 := by decide
    have eqD : (2*7+1).choose 7 = 6435 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 799963029 := by omega
    have hdiv_end : 31 ∣ 799963029 := by norm_num
    have hndiv_end : ¬ 31^2 ∣ 799963029 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 223 := by norm_num
    have hq3 : 223 % 4 = 3 := by norm_num
    have eqC : (2*10+1).choose 10 = 352716 := by decide
    have eqD : (2*8+1).choose 8 = 24310 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 799945154 := by omega
    have hdiv_end : 223 ∣ 799945154 := by norm_num
    have hndiv_end : ¬ 223^2 ∣ 799945154 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 887 := by norm_num
    have hq3 : 887 % 4 = 3 := by norm_num
    have eqC : (2*10+1).choose 10 = 352716 := by decide
    have eqD : (2*9+1).choose 9 = 92378 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 799877086 := by omega
    have hdiv_end : 887 ∣ 799877086 := by norm_num
    have hndiv_end : ¬ 887^2 ∣ 799877086 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*10+1).choose 10 = 352716 := by decide
    have eqD : (2*10+1).choose 10 = 352716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 799616748 := by omega
    have hdiv_end : 3 ∣ 799616748 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 799616748 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*10+1).choose 10 = 352716 := by decide
    have eqD : (2*11+1).choose 11 = 1352078 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798617386 := by omega
    have hdiv_end : 19 ∣ 798617386 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 798617386 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*10+1).choose 10 = 352716 := by decide
    have eqD : (2*12+1).choose 12 = 5200300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 794769164 := by omega
    have hdiv_end : 7 ∣ 794769164 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 794769164 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*10+1).choose 10 = 352716 := by decide
    have eqD : (2*13+1).choose 13 = 20058300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 779911164 := by omega
    have hdiv_end : 19 ∣ 779911164 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 779911164 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*10+1).choose 10 = 352716 := by decide
    have eqD : (2*14+1).choose 14 = 77558760 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722410704 := by omega
    have hdiv_0 : 3 ∣ 722410704 := by norm_num
    have hstep_0 := sum_two_squares_step hq hq3 hr_0 hdiv_0
    rcases hstep_0 with ⟨-, -, hr_1⟩
    have hdiv_end : 3 ∣ 80267856 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 80267856 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_1
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*10+1).choose 10 = 352716 := by decide
    have eqD : (2*15+1).choose 15 = 300540195 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499429269 := by omega
    have hdiv_end : 19 ∣ 499429269 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 499429269 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have eqC : (2*10+1).choose 10 = 352716 := by decide
    have eqD : (2*16+1).choose 16 = 1166803110 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*11+1).choose 11 = 1352078 := by decide
    have eqD : (2*0+1).choose 0 = 1 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798970101 := by omega
    have hdiv_end : 3 ∣ 798970101 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 798970101 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 31 := by norm_num
    have hq3 : 31 % 4 = 3 := by norm_num
    have eqC : (2*11+1).choose 11 = 1352078 := by decide
    have eqD : (2*1+1).choose 1 = 3 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798970099 := by omega
    have hdiv_end : 31 ∣ 798970099 := by norm_num
    have hndiv_end : ¬ 31^2 ∣ 798970099 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*11+1).choose 11 = 1352078 := by decide
    have eqD : (2*2+1).choose 2 = 10 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798970092 := by omega
    have hdiv_end : 3 ∣ 798970092 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 798970092 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*11+1).choose 11 = 1352078 := by decide
    have eqD : (2*3+1).choose 3 = 35 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798970067 := by omega
    have hdiv_end : 7 ∣ 798970067 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 798970067 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*11+1).choose 11 = 1352078 := by decide
    have eqD : (2*4+1).choose 4 = 126 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798969976 := by omega
    have hdiv_end : 7 ∣ 798969976 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 798969976 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*11+1).choose 11 = 1352078 := by decide
    have eqD : (2*5+1).choose 5 = 462 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798969640 := by omega
    have hdiv_end : 7 ∣ 798969640 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 798969640 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 139 := by norm_num
    have hq3 : 139 % 4 = 3 := by norm_num
    have eqC : (2*11+1).choose 11 = 1352078 := by decide
    have eqD : (2*6+1).choose 6 = 1716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798968386 := by omega
    have hdiv_end : 139 ∣ 798968386 := by norm_num
    have hndiv_end : ¬ 139^2 ∣ 798968386 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3331 := by norm_num
    have hq3 : 3331 % 4 = 3 := by norm_num
    have eqC : (2*11+1).choose 11 = 1352078 := by decide
    have eqD : (2*7+1).choose 7 = 6435 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798963667 := by omega
    have hdiv_end : 3331 ∣ 798963667 := by norm_num
    have hndiv_end : ¬ 3331^2 ∣ 798963667 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*11+1).choose 11 = 1352078 := by decide
    have eqD : (2*8+1).choose 8 = 24310 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798945792 := by omega
    have hdiv_end : 3 ∣ 798945792 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 798945792 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*11+1).choose 11 = 1352078 := by decide
    have eqD : (2*9+1).choose 9 = 92378 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798877724 := by omega
    have hdiv_end : 19 ∣ 798877724 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 798877724 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*11+1).choose 11 = 1352078 := by decide
    have eqD : (2*10+1).choose 10 = 352716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 798617386 := by omega
    have hdiv_end : 19 ∣ 798617386 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 798617386 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*11+1).choose 11 = 1352078 := by decide
    have eqD : (2*11+1).choose 11 = 1352078 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 797618024 := by omega
    have hdiv_end : 7 ∣ 797618024 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 797618024 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*11+1).choose 11 = 1352078 := by decide
    have eqD : (2*12+1).choose 12 = 5200300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 793769802 := by omega
    have hdiv_end : 3 ∣ 793769802 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 793769802 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*11+1).choose 11 = 1352078 := by decide
    have eqD : (2*13+1).choose 13 = 20058300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 778911802 := by omega
    have hdiv_end : 19 ∣ 778911802 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 778911802 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*11+1).choose 11 = 1352078 := by decide
    have eqD : (2*14+1).choose 14 = 77558760 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 721411342 := by omega
    have hdiv_end : 19 ∣ 721411342 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 721411342 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*11+1).choose 11 = 1352078 := by decide
    have eqD : (2*15+1).choose 15 = 300540195 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 498429907 := by omega
    have hdiv_end : 19 ∣ 498429907 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 498429907 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have eqC : (2*11+1).choose 11 = 1352078 := by decide
    have eqD : (2*16+1).choose 16 = 1166803110 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have hq : Nat.Prime 887 := by norm_num
    have hq3 : 887 % 4 = 3 := by norm_num
    have eqC : (2*12+1).choose 12 = 5200300 := by decide
    have eqD : (2*0+1).choose 0 = 1 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 795121879 := by omega
    have hdiv_end : 887 ∣ 795121879 := by norm_num
    have hndiv_end : ¬ 887^2 ∣ 795121879 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 11 := by norm_num
    have hq3 : 11 % 4 = 3 := by norm_num
    have eqC : (2*12+1).choose 12 = 5200300 := by decide
    have eqD : (2*1+1).choose 1 = 3 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 795121877 := by omega
    have hdiv_end : 11 ∣ 795121877 := by norm_num
    have hndiv_end : ¬ 11^2 ∣ 795121877 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 79512187 := by norm_num
    have hq3 : 79512187 % 4 = 3 := by norm_num
    have eqC : (2*12+1).choose 12 = 5200300 := by decide
    have eqD : (2*2+1).choose 2 = 10 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 795121870 := by omega
    have hdiv_end : 79512187 ∣ 795121870 := by norm_num
    have hndiv_end : ¬ 79512187^2 ∣ 795121870 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*12+1).choose 12 = 5200300 := by decide
    have eqD : (2*3+1).choose 3 = 35 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 795121845 := by omega
    have hdiv_end : 3 ∣ 795121845 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 795121845 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*12+1).choose 12 = 5200300 := by decide
    have eqD : (2*4+1).choose 4 = 126 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 795121754 := by omega
    have hdiv_end : 7 ∣ 795121754 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 795121754 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*12+1).choose 12 = 5200300 := by decide
    have eqD : (2*5+1).choose 5 = 462 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 795121418 := by omega
    have hdiv_end : 7 ∣ 795121418 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 795121418 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 227 := by norm_num
    have hq3 : 227 % 4 = 3 := by norm_num
    have eqC : (2*12+1).choose 12 = 5200300 := by decide
    have eqD : (2*6+1).choose 6 = 1716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 795120164 := by omega
    have hdiv_end : 227 ∣ 795120164 := by norm_num
    have hndiv_end : ¬ 227^2 ∣ 795120164 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 139 := by norm_num
    have hq3 : 139 % 4 = 3 := by norm_num
    have eqC : (2*12+1).choose 12 = 5200300 := by decide
    have eqD : (2*7+1).choose 7 = 6435 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 795115445 := by omega
    have hdiv_end : 139 ∣ 795115445 := by norm_num
    have hndiv_end : ¬ 139^2 ∣ 795115445 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 59 := by norm_num
    have hq3 : 59 % 4 = 3 := by norm_num
    have eqC : (2*12+1).choose 12 = 5200300 := by decide
    have eqD : (2*8+1).choose 8 = 24310 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 795097570 := by omega
    have hdiv_end : 59 ∣ 795097570 := by norm_num
    have hndiv_end : ¬ 59^2 ∣ 795097570 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*12+1).choose 12 = 5200300 := by decide
    have eqD : (2*9+1).choose 9 = 92378 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 795029502 := by omega
    have hdiv_end : 3 ∣ 795029502 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 795029502 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*12+1).choose 12 = 5200300 := by decide
    have eqD : (2*10+1).choose 10 = 352716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 794769164 := by omega
    have hdiv_end : 7 ∣ 794769164 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 794769164 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*12+1).choose 12 = 5200300 := by decide
    have eqD : (2*11+1).choose 11 = 1352078 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 793769802 := by omega
    have hdiv_end : 3 ∣ 793769802 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 793769802 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*12+1).choose 12 = 5200300 := by decide
    have eqD : (2*12+1).choose 12 = 5200300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 789921580 := by omega
    have hdiv_end : 7 ∣ 789921580 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 789921580 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*12+1).choose 12 = 5200300 := by decide
    have eqD : (2*13+1).choose 13 = 20058300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 775063580 := by omega
    have hdiv_end : 19 ∣ 775063580 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 775063580 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*12+1).choose 12 = 5200300 := by decide
    have eqD : (2*14+1).choose 14 = 77558760 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 717563120 := by omega
    have hdiv_end : 19 ∣ 717563120 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 717563120 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*12+1).choose 12 = 5200300 := by decide
    have eqD : (2*15+1).choose 15 = 300540195 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 494581685 := by omega
    have hdiv_end : 19 ∣ 494581685 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 494581685 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have eqC : (2*12+1).choose 12 = 5200300 := by decide
    have eqD : (2*16+1).choose 16 = 1166803110 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have hq : Nat.Prime 26905651 := by norm_num
    have hq3 : 26905651 % 4 = 3 := by norm_num
    have eqC : (2*13+1).choose 13 = 20058300 := by decide
    have eqD : (2*0+1).choose 0 = 1 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 780263879 := by omega
    have hdiv_end : 26905651 ∣ 780263879 := by norm_num
    have hndiv_end : ¬ 26905651^2 ∣ 780263879 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*13+1).choose 13 = 20058300 := by decide
    have eqD : (2*1+1).choose 1 = 3 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 780263877 := by omega
    have hdiv_end : 3 ∣ 780263877 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 780263877 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 127 := by norm_num
    have hq3 : 127 % 4 = 3 := by norm_num
    have eqC : (2*13+1).choose 13 = 20058300 := by decide
    have eqD : (2*2+1).choose 2 = 10 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 780263870 := by omega
    have hdiv_end : 127 ∣ 780263870 := by norm_num
    have hndiv_end : ¬ 127^2 ∣ 780263870 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 23 := by norm_num
    have hq3 : 23 % 4 = 3 := by norm_num
    have eqC : (2*13+1).choose 13 = 20058300 := by decide
    have eqD : (2*3+1).choose 3 = 35 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 780263845 := by omega
    have hdiv_end : 23 ∣ 780263845 := by norm_num
    have hndiv_end : ¬ 23^2 ∣ 780263845 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*13+1).choose 13 = 20058300 := by decide
    have eqD : (2*4+1).choose 4 = 126 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 780263754 := by omega
    have hdiv_end : 3 ∣ 780263754 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 780263754 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*13+1).choose 13 = 20058300 := by decide
    have eqD : (2*5+1).choose 5 = 462 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 780263418 := by omega
    have hdiv_end : 3 ∣ 780263418 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 780263418 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 11 := by norm_num
    have hq3 : 11 % 4 = 3 := by norm_num
    have eqC : (2*13+1).choose 13 = 20058300 := by decide
    have eqD : (2*6+1).choose 6 = 1716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 780262164 := by omega
    have hdiv_end : 11 ∣ 780262164 := by norm_num
    have hndiv_end : ¬ 11^2 ∣ 780262164 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*13+1).choose 13 = 20058300 := by decide
    have eqD : (2*7+1).choose 7 = 6435 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 780257445 := by omega
    have hdiv_end : 3 ∣ 780257445 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 780257445 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 11 := by norm_num
    have hq3 : 11 % 4 = 3 := by norm_num
    have eqC : (2*13+1).choose 13 = 20058300 := by decide
    have eqD : (2*8+1).choose 8 = 24310 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 780239570 := by omega
    have hdiv_end : 11 ∣ 780239570 := by norm_num
    have hndiv_end : ¬ 11^2 ∣ 780239570 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 11 := by norm_num
    have hq3 : 11 % 4 = 3 := by norm_num
    have eqC : (2*13+1).choose 13 = 20058300 := by decide
    have eqD : (2*9+1).choose 9 = 92378 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 780171502 := by omega
    have hdiv_end : 11 ∣ 780171502 := by norm_num
    have hndiv_end : ¬ 11^2 ∣ 780171502 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*13+1).choose 13 = 20058300 := by decide
    have eqD : (2*10+1).choose 10 = 352716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 779911164 := by omega
    have hdiv_end : 19 ∣ 779911164 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 779911164 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*13+1).choose 13 = 20058300 := by decide
    have eqD : (2*11+1).choose 11 = 1352078 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 778911802 := by omega
    have hdiv_end : 19 ∣ 778911802 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 778911802 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*13+1).choose 13 = 20058300 := by decide
    have eqD : (2*12+1).choose 12 = 5200300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 775063580 := by omega
    have hdiv_end : 19 ∣ 775063580 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 775063580 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*13+1).choose 13 = 20058300 := by decide
    have eqD : (2*13+1).choose 13 = 20058300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 760205580 := by omega
    have hdiv_end : 3 ∣ 760205580 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 760205580 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*13+1).choose 13 = 20058300 := by decide
    have eqD : (2*14+1).choose 14 = 77558760 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 702705120 := by omega
    have hdiv_end : 3 ∣ 702705120 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 702705120 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*13+1).choose 13 = 20058300 := by decide
    have eqD : (2*15+1).choose 15 = 300540195 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 479723685 := by omega
    have hdiv_end : 3 ∣ 479723685 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 479723685 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have eqC : (2*13+1).choose 13 = 20058300 := by decide
    have eqD : (2*16+1).choose 16 = 1166803110 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*14+1).choose 14 = 77558760 := by decide
    have eqD : (2*0+1).choose 0 = 1 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722763419 := by omega
    have hdiv_end : 7 ∣ 722763419 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 722763419 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*14+1).choose 14 = 77558760 := by decide
    have eqD : (2*1+1).choose 1 = 3 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722763417 := by omega
    have hdiv_end : 3 ∣ 722763417 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 722763417 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 2819 := by norm_num
    have hq3 : 2819 % 4 = 3 := by norm_num
    have eqC : (2*14+1).choose 14 = 77558760 := by decide
    have eqD : (2*2+1).choose 2 = 10 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722763410 := by omega
    have hdiv_end : 2819 ∣ 722763410 := by norm_num
    have hndiv_end : ¬ 2819^2 ∣ 722763410 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 23 := by norm_num
    have hq3 : 23 % 4 = 3 := by norm_num
    have eqC : (2*14+1).choose 14 = 77558760 := by decide
    have eqD : (2*3+1).choose 3 = 35 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722763385 := by omega
    have hdiv_end : 23 ∣ 722763385 := by norm_num
    have hndiv_end : ¬ 23^2 ∣ 722763385 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*14+1).choose 14 = 77558760 := by decide
    have eqD : (2*4+1).choose 4 = 126 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722763294 := by omega
    have hdiv_end : 3 ∣ 722763294 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 722763294 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*14+1).choose 14 = 77558760 := by decide
    have eqD : (2*5+1).choose 5 = 462 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722762958 := by omega
    have hdiv_end : 3 ∣ 722762958 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 722762958 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*14+1).choose 14 = 77558760 := by decide
    have eqD : (2*6+1).choose 6 = 1716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722761704 := by omega
    have hdiv_0 : 3 ∣ 722761704 := by norm_num
    have hstep_0 := sum_two_squares_step hq hq3 hr_0 hdiv_0
    rcases hstep_0 with ⟨-, -, hr_1⟩
    have hdiv_1 : 3 ∣ 80306856 := by norm_num
    have hstep_1 := sum_two_squares_step hq hq3 hr_1 hdiv_1
    rcases hstep_1 with ⟨-, -, hr_2⟩
    have hdiv_end : 3 ∣ 8922984 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 8922984 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_2
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*14+1).choose 14 = 77558760 := by decide
    have eqD : (2*7+1).choose 7 = 6435 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722756985 := by omega
    have hdiv_end : 3 ∣ 722756985 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 722756985 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7591 := by norm_num
    have hq3 : 7591 % 4 = 3 := by norm_num
    have eqC : (2*14+1).choose 14 = 77558760 := by decide
    have eqD : (2*8+1).choose 8 = 24310 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722739110 := by omega
    have hdiv_end : 7591 ∣ 722739110 := by norm_num
    have hndiv_end : ¬ 7591^2 ∣ 722739110 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*14+1).choose 14 = 77558760 := by decide
    have eqD : (2*9+1).choose 9 = 92378 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722671042 := by omega
    have hdiv_end : 19 ∣ 722671042 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 722671042 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*14+1).choose 14 = 77558760 := by decide
    have eqD : (2*10+1).choose 10 = 352716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 722410704 := by omega
    have hdiv_0 : 3 ∣ 722410704 := by norm_num
    have hstep_0 := sum_two_squares_step hq hq3 hr_0 hdiv_0
    rcases hstep_0 with ⟨-, -, hr_1⟩
    have hdiv_end : 3 ∣ 80267856 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 80267856 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_1
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*14+1).choose 14 = 77558760 := by decide
    have eqD : (2*11+1).choose 11 = 1352078 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 721411342 := by omega
    have hdiv_end : 19 ∣ 721411342 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 721411342 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*14+1).choose 14 = 77558760 := by decide
    have eqD : (2*12+1).choose 12 = 5200300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 717563120 := by omega
    have hdiv_end : 19 ∣ 717563120 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 717563120 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*14+1).choose 14 = 77558760 := by decide
    have eqD : (2*13+1).choose 13 = 20058300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 702705120 := by omega
    have hdiv_end : 3 ∣ 702705120 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 702705120 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*14+1).choose 14 = 77558760 := by decide
    have eqD : (2*14+1).choose 14 = 77558760 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 645204660 := by omega
    have hdiv_end : 3 ∣ 645204660 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 645204660 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*14+1).choose 14 = 77558760 := by decide
    have eqD : (2*15+1).choose 15 = 300540195 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 422223225 := by omega
    have hdiv_end : 3 ∣ 422223225 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 422223225 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have eqC : (2*14+1).choose 14 = 77558760 := by decide
    have eqD : (2*16+1).choose 16 = 1166803110 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have hq : Nat.Prime 1999 := by norm_num
    have hq3 : 1999 % 4 = 3 := by norm_num
    have eqC : (2*15+1).choose 15 = 300540195 := by decide
    have eqD : (2*0+1).choose 0 = 1 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499781984 := by omega
    have hdiv_end : 1999 ∣ 499781984 := by norm_num
    have hndiv_end : ¬ 1999^2 ∣ 499781984 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*15+1).choose 15 = 300540195 := by decide
    have eqD : (2*1+1).choose 1 = 3 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499781982 := by omega
    have hdiv_end : 3 ∣ 499781982 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 499781982 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 7 := by norm_num
    have hq3 : 7 % 4 = 3 := by norm_num
    have eqC : (2*15+1).choose 15 = 300540195 := by decide
    have eqD : (2*2+1).choose 2 = 10 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499781975 := by omega
    have hdiv_end : 7 ∣ 499781975 := by norm_num
    have hndiv_end : ¬ 7^2 ∣ 499781975 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 23 := by norm_num
    have hq3 : 23 % 4 = 3 := by norm_num
    have eqC : (2*15+1).choose 15 = 300540195 := by decide
    have eqD : (2*3+1).choose 3 = 35 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499781950 := by omega
    have hdiv_end : 23 ∣ 499781950 := by norm_num
    have hndiv_end : ¬ 23^2 ∣ 499781950 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*15+1).choose 15 = 300540195 := by decide
    have eqD : (2*4+1).choose 4 = 126 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499781859 := by omega
    have hdiv_end : 3 ∣ 499781859 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 499781859 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*15+1).choose 15 = 300540195 := by decide
    have eqD : (2*5+1).choose 5 = 462 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499781523 := by omega
    have hdiv_end : 3 ∣ 499781523 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 499781523 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 67 := by norm_num
    have hq3 : 67 % 4 = 3 := by norm_num
    have eqC : (2*15+1).choose 15 = 300540195 := by decide
    have eqD : (2*6+1).choose 6 = 1716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499780269 := by omega
    have hdiv_end : 67 ∣ 499780269 := by norm_num
    have hndiv_end : ¬ 67^2 ∣ 499780269 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*15+1).choose 15 = 300540195 := by decide
    have eqD : (2*7+1).choose 7 = 6435 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499775550 := by omega
    have hdiv_end : 3 ∣ 499775550 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 499775550 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19990307 := by norm_num
    have hq3 : 19990307 % 4 = 3 := by norm_num
    have eqC : (2*15+1).choose 15 = 300540195 := by decide
    have eqD : (2*8+1).choose 8 = 24310 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499757675 := by omega
    have hdiv_end : 19990307 ∣ 499757675 := by norm_num
    have hndiv_end : ¬ 19990307^2 ∣ 499757675 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*15+1).choose 15 = 300540195 := by decide
    have eqD : (2*9+1).choose 9 = 92378 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499689607 := by omega
    have hdiv_end : 19 ∣ 499689607 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 499689607 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*15+1).choose 15 = 300540195 := by decide
    have eqD : (2*10+1).choose 10 = 352716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 499429269 := by omega
    have hdiv_end : 19 ∣ 499429269 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 499429269 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*15+1).choose 15 = 300540195 := by decide
    have eqD : (2*11+1).choose 11 = 1352078 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 498429907 := by omega
    have hdiv_end : 19 ∣ 498429907 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 498429907 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 19 := by norm_num
    have hq3 : 19 % 4 = 3 := by norm_num
    have eqC : (2*15+1).choose 15 = 300540195 := by decide
    have eqD : (2*12+1).choose 12 = 5200300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 494581685 := by omega
    have hdiv_end : 19 ∣ 494581685 := by norm_num
    have hndiv_end : ¬ 19^2 ∣ 494581685 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*15+1).choose 15 = 300540195 := by decide
    have eqD : (2*13+1).choose 13 = 20058300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 479723685 := by omega
    have hdiv_end : 3 ∣ 479723685 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 479723685 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*15+1).choose 15 = 300540195 := by decide
    have eqD : (2*14+1).choose 14 = 77558760 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 422223225 := by omega
    have hdiv_end : 3 ∣ 422223225 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 422223225 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have hq : Nat.Prime 3 := by norm_num
    have hq3 : 3 % 4 = 3 := by norm_num
    have eqC : (2*15+1).choose 15 = 300540195 := by decide
    have eqD : (2*15+1).choose 15 = 300540195 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    have hr_0 : a^2 + b^2 = 199241790 := by omega
    have hdiv_end : 3 ∣ 199241790 := by norm_num
    have hndiv_end : ¬ 3^2 ∣ 199241790 := by norm_num
    exact no_sum_two_squares hq hq3 hdiv_end hndiv_end _ _ hr_0
  · intro a b h
    have eqC : (2*15+1).choose 15 = 300540195 := by decide
    have eqD : (2*16+1).choose 16 = 1166803110 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have eqC : (2*16+1).choose 16 = 1166803110 := by decide
    have eqD : (2*0+1).choose 0 = 1 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have eqC : (2*16+1).choose 16 = 1166803110 := by decide
    have eqD : (2*1+1).choose 1 = 3 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have eqC : (2*16+1).choose 16 = 1166803110 := by decide
    have eqD : (2*2+1).choose 2 = 10 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have eqC : (2*16+1).choose 16 = 1166803110 := by decide
    have eqD : (2*3+1).choose 3 = 35 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have eqC : (2*16+1).choose 16 = 1166803110 := by decide
    have eqD : (2*4+1).choose 4 = 126 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have eqC : (2*16+1).choose 16 = 1166803110 := by decide
    have eqD : (2*5+1).choose 5 = 462 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have eqC : (2*16+1).choose 16 = 1166803110 := by decide
    have eqD : (2*6+1).choose 6 = 1716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have eqC : (2*16+1).choose 16 = 1166803110 := by decide
    have eqD : (2*7+1).choose 7 = 6435 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have eqC : (2*16+1).choose 16 = 1166803110 := by decide
    have eqD : (2*8+1).choose 8 = 24310 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have eqC : (2*16+1).choose 16 = 1166803110 := by decide
    have eqD : (2*9+1).choose 9 = 92378 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have eqC : (2*16+1).choose 16 = 1166803110 := by decide
    have eqD : (2*10+1).choose 10 = 352716 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have eqC : (2*16+1).choose 16 = 1166803110 := by decide
    have eqD : (2*11+1).choose 11 = 1352078 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have eqC : (2*16+1).choose 16 = 1166803110 := by decide
    have eqD : (2*12+1).choose 12 = 5200300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have eqC : (2*16+1).choose 16 = 1166803110 := by decide
    have eqD : (2*13+1).choose 13 = 20058300 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have eqC : (2*16+1).choose 16 = 1166803110 := by decide
    have eqD : (2*14+1).choose 14 = 77558760 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have eqC : (2*16+1).choose 16 = 1166803110 := by decide
    have eqD : (2*15+1).choose 15 = 300540195 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega
  · intro a b h
    have eqC : (2*16+1).choose 16 = 1166803110 := by decide
    have eqD : (2*16+1).choose 16 = 1166803110 := by decide
    rw [eqC] at h
    try rw [eqD] at h
    omega


theorem oeis_a303639_conjecture.disproof : ¬ (type_of% @oeis_a303639_conjecture) := by
  intro h
  have h1 : a 800322180 > 0 := h 800322180 (by norm_num)
  unfold a at h1
  have hz : (Finset.range (Nat.sqrt 800322180 + 1)).sum (fun a =>
    (Finset.range (Nat.sqrt 800322180 + 1)).sum (fun b =>
      (Finset.range 800322181).sum (fun c =>
        (Finset.range 800322181).sum (fun d =>
          if a ≤ b ∧ c ≤ d ∧ a^2 + b^2 + (2*c+1).choose c + (2*d+1).choose d = 800322180 then 1 else 0)))) = 0 := by
    apply Finset.sum_eq_zero; intro a ha
    apply Finset.sum_eq_zero; intro b hb
    apply Finset.sum_eq_zero; intro c hc
    apply Finset.sum_eq_zero; intro d hd
    have : a^2 + b^2 + (2*c+1).choose c + (2*d+1).choose d ≠ 800322180 := no_solution a b c d
    simp [this]
  rw [hz] at h1
  exact Nat.not_lt_zero 0 h1

