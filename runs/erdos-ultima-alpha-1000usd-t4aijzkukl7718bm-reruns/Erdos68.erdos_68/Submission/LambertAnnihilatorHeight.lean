import Submission.LambertLongBoundedCombinations

/-! Exact annihilator division decreases coefficient height. Near division
need not give a uniformly separated first row. This does not settle Erdos 68. -/

namespace LambertAnnihilatorHeight

open Polynomial Finset

/-- The integral polynomial for a geometric row with base B and period d. -/
noncomputable def annihilator (B : ℤ) (d : ℕ) : ℤ[X] := C B * X^d - 1

lemma annihilator_mul_coeff (B : ℤ) (d n : ℕ) (q : ℤ[X]) :
    ((annihilator B d)*q).coeff (n+d) = B*q.coeff n-q.coeff (n+d) := by
  simp only [annihilator, sub_mul, one_mul, coeff_sub, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul]

/-- The bound is on the quotient's actual coefficients, not its degree. -/
theorem weighted_quotient_bound (B c Q : ℤ) (d : ℕ) (q : ℤ[X])
    (hB : 1 ≤ B) (hc : 0 ≤ c)
    (hq : ∀ n, c*|((annihilator B d)*q).coeff n| ≤ Q) (n : ℕ) :
    c*(B-1)*|q.coeff n| ≤ Q := by
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (Finset.range (q.natDegree+1))
    (fun j => |q.coeff j|) ⟨0, by simp⟩
  have hglobal (j : ℕ) : |q.coeff j| ≤ |q.coeff m| := by
    by_cases hj : j ≤ q.natDegree
    · exact hmax j (Finset.mem_range.mpr (by omega))
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
  have htri : B*|q.coeff m| ≤ |((annihilator B d)*q).coeff (m+d)|+|q.coeff (m+d)| := by
    calc
      _ = |B*q.coeff m| := by rw [abs_mul, abs_of_nonneg (by omega : 0 ≤ B)]
      _ = |((annihilator B d)*q).coeff (m+d)+q.coeff (m+d)| := by
        rw [annihilator_mul_coeff]
        ring_nf
      _ ≤ _ := abs_add_le _ _
  have hmain : c*(B-1)*|q.coeff m| ≤ Q := by
    have ht := mul_le_mul_of_nonneg_left htri hc
    have hg := mul_le_mul_of_nonneg_left (hglobal (m+d)) hc
    have hb := hq (m+d)
    nlinarith
  exact (mul_le_mul_of_nonneg_left (hglobal n) (mul_nonneg hc (by omega))).trans hmain

noncomputable def rowProduct (ds : List ℕ) : ℤ[X] :=
  (ds.map (fun d => annihilator d.factorial d)).prod

/-- Exact successive division accumulates the factors d!-1 in the height
reduction. It makes no assertion that a nearly vanishing row can be divided. -/
theorem rowProduct_quotient_bound (ds : List ℕ) (c Q : ℤ) (q : ℤ[X])
    (hc : 0 ≤ c) (hds : ∀ d ∈ ds, 2 ≤ d)
    (hq : ∀ n, c*|(rowProduct ds*q).coeff n| ≤ Q) (n : ℕ) :
    c*(ds.map (fun d => (d.factorial : ℤ)-1)).prod*|q.coeff n| ≤ Q := by
  induction ds generalizing c with
  | nil => simpa [rowProduct] using hq n
  | cons d ds ih =>
    have hd : 2 ≤ d := hds d (by simp)
    have hf : (2 : ℤ) ≤ d.factorial := by exact_mod_cast Nat.factorial_le hd
    have hb (j : ℕ) : (c*((d.factorial : ℤ)-1))*|(rowProduct ds*q).coeff j| ≤ Q := by
      apply weighted_quotient_bound d.factorial c Q d (rowProduct ds*q) (by omega) hc
      intro i
      simpa [rowProduct, mul_assoc] using hq i
    have hi := ih (c*((d.factorial : ℤ)-1)) (mul_nonneg hc (by omega))
      (fun e he => hds e (by simp [he])) hb
    simpa only [List.map_cons, List.prod_cons, mul_assoc] using hi

/-- An annihilator with one distant monomial added. -/
noncomputable def nearAnnihilator (B : ℤ) (d N : ℕ) : ℤ[X] :=
  annihilator B d + X^(N+d+1)

lemma nearAnnihilator_coeff_bound (B : ℤ) (d N n : ℕ) (hB : 1 ≤ B) (hd : 0 < d) :
    |(nearAnnihilator B d N).coeff n| ≤ B := by
  simp only [nearAnnihilator, annihilator, coeff_add, coeff_sub,
    coeff_C_mul_X_pow, coeff_one, coeff_X_pow]
  by_cases hn0 : n=0
  · subst n
    simp [show 0 ≠ d by omega]
    omega
  · by_cases hnd : n=d
    · subst n
      simp [show d ≠ 0 by omega, show d ≠ N+d+1 by omega, abs_of_nonneg (by omega : 0 ≤ B)]
    · by_cases hnN : n=N+d+1
      · subst n
        simp [show N+d+1 ≠ d by omega]
        omega
      · simp [hn0, hnd, hnN]
        omega

lemma nearAnnihilator_eval (B : ℤ) (d N : ℕ) (x : ℝ) (hx : (B : ℝ)*x^d=1) :
    (nearAnnihilator B d N).eval₂ (Int.castRingHom ℝ) x = x^(N+d+1) := by
  simp only [nearAnnihilator, annihilator, eval₂_add, eval₂_sub, eval₂_mul,
    eval₂_C, eval₂_pow, eval₂_X, eval₂_one, Int.coe_castRingHom, hx, sub_self, zero_add]

/-- These polynomials do not exactly cancel the chosen row. -/
theorem nearAnnihilator_not_dvd (B : ℤ) (d N : ℕ) (x : ℝ)
    (hx : 0 < x) (hroot : (B : ℝ)*x^d=1) :
    ¬ annihilator B d ∣ nearAnnihilator B d N := by
  rintro ⟨q, hq⟩
  have he := congrArg (fun p : ℤ[X] => p.eval₂ (Int.castRingHom ℝ) x) hq
  dsimp only at he
  rw [nearAnnihilator_eval B d N x hroot, eval₂_mul] at he
  have ha : (annihilator B d).eval₂ (Int.castRingHom ℝ) x = 0 := by
    simp only [annihilator, eval₂_sub, eval₂_mul, eval₂_C, eval₂_pow,
      eval₂_X, eval₂_one, Int.coe_castRingHom, hroot, sub_self]
  rw [ha, zero_mul] at he
  exact (pow_pos hx _).ne' he

open LambertDifferenceOperators LambertRawBounds LambertLongBoundedCombinations

noncomputable section

def nearRow (d N n : ℕ) : ℝ :=
  (d.factorial : ℝ)*geometricRowTail d (n+d)-geometricRowTail d n +
    geometricRowTail d (n+(N+d+1))

lemma nearRow_eq (d N n : ℕ) (hd : 0 < d) :
    nearRow d N n = geometricRowTail d (n+(N+d+1)) := by
  rw [nearRow, geometricRowTail_shift d hd]
  have hf : (d.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma nearRow_pos (d N n : ℕ) (hd : 2 ≤ d) : 0 < nearRow d N n := by
  rw [nearRow_eq d N n (by omega), geometricRowTail]
  have hf : (2 : ℝ) ≤ d.factorial := by exact_mod_cast Nat.factorial_le hd
  have hden : (0 : ℝ) < d.factorial-1 := by linarith
  positivity

/-- Despite a fixed coefficient budget d!, its normalized first-row
response is bounded by a quantity tending to zero with the support length. -/
theorem nearRow_uniform_bound (d N n : ℕ) (hd : 2 ≤ d) :
    rate d^n*|nearRow d N n| ≤ 2/rate d^(N+d+1) := by
  have hp := rate_pos d
  rw [abs_of_pos (nearRow_pos d N n hd), nearRow_eq d N n (by omega)]
  calc
    _ ≤ rate d^n*(2/rate d^(n+(N+d+1))) :=
      mul_le_mul_of_nonneg_left (row_le_rate d _ hd) (pow_nonneg hp.le n)
    _ = _ := by rw [pow_add]; field_simp

lemma nearRow_bound_tendsto (d : ℕ) (hd : 12 ≤ d) :
    Filter.Tendsto (fun N : ℕ => 2/rate d^(N+d+1)) Filter.atTop (nhds 0) := by
  have hp := rate_pos d
  have h2 := rate_ge_two d hd
  have hi : 0 ≤ 1/rate d := by positivity
  have hu : 1/rate d < 1 := (div_lt_one hp).mpr (by linarith)
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hi hu).mul_const
    ((1/rate d)^(d+1))
  have ht2 := ht.const_mul 2
  simp only [zero_mul, mul_zero] at ht2
  convert ht2 using 1
  funext N
  rw [show N+d+1=N+(d+1) by omega, pow_add]
  simp only [one_div_pow]
  ring

/-- There is no positive uniform normalized first-row lower bound for all
non-annihilating polynomials of coefficient height at most d!. -/
theorem arbitrarily_small_nonzero_nearRow (d : ℕ) (hd : 12 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n, 0 < nearRow d N n ∧ rate d^n*|nearRow d N n| < ε := by
  have he := (nearRow_bound_tendsto d hd).eventually (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
  refine ⟨N, fun n => ⟨nearRow_pos d N n (by omega), ?_⟩⟩
  exact (nearRow_uniform_bound d N n (by omega)).trans_lt (hN N le_rfl)

lemma nearFactorial_not_dvd (d N : ℕ) (hd : 12 ≤ d) :
    ¬ annihilator d.factorial d ∣ nearAnnihilator d.factorial d N := by
  have hp := rate_pos d
  apply nearAnnihilator_not_dvd d.factorial d N (1/rate d) (by positivity)
  rw [Int.cast_natCast, one_div_pow, rate_pow d (by omega), mul_one_div]
  exact div_self (by positivity)

/-- Applying any fixed earlier row-cancelling operator does not restore a
uniform positive separation of the first uncancelled row. -/
lemma nearRawRow_bound (ds : List ℕ) (d N n : ℕ) (hd : 2 ≤ d)
    (hds : ∀ k ∈ ds, k ≤ d) :
    rate d^n * |rawApply ds (nearRow d N) n| ≤
      2^ds.length*(2/rate d^(N+d+1)) := by
  have hp := rate_pos d
  have hr (m : ℕ) : |nearRow d N m| ≤ (2/rate d^(N+d+1))/rate d^m := by
    apply (le_div_iff₀ (pow_pos hp m)).mpr
    simpa only [mul_comm] using nearRow_uniform_bound d N m hd
  have hb := rawApply_bound ds (nearRow d N) (rate d) (2/rate d^(N+d+1)) hp
    (by positivity) (fun k hk => factorial_le_rate_pow k d (by omega) (hds k hk)) hr n
  have hm := mul_le_mul_of_nonneg_left hb (pow_nonneg hp.le n)
  convert hm using 1
  field_simp

/-- A precise limit on the attempted height extension: at fixed height d!,
nondivisibility does not give a positive degree-independent first-row bound. -/
theorem small_nondivisible_first_row (ds : List ℕ) (d : ℕ) (hd : 12 ≤ d)
    (hds : ∀ k ∈ ds, k ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ N,
      (∀ j, |(nearAnnihilator d.factorial d N).coeff j| ≤ (d.factorial : ℤ)) ∧
      (¬ annihilator d.factorial d ∣ nearAnnihilator d.factorial d N) ∧
      ∀ n, rate d^n*|rawApply ds (nearRow d N) n| < ε := by
  have ht := (nearRow_bound_tendsto d hd).const_mul ((2 : ℝ)^ds.length)
  simp only [mul_zero] at ht
  have he := ht.eventually (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
  refine ⟨N, fun j => nearAnnihilator_coeff_bound d.factorial d N j (by
      have hf : (0 : ℤ) < d.factorial := by positivity
      omega)
    (by omega), nearFactorial_not_dvd d N hd, fun n => ?_⟩
  exact (nearRawRow_bound ds d N n (by omega) hds).trans_lt (hN N le_rfl)

end
end LambertAnnihilatorHeight

#print axioms LambertAnnihilatorHeight.weighted_quotient_bound
#print axioms LambertAnnihilatorHeight.rowProduct_quotient_bound
#print axioms LambertAnnihilatorHeight.nearAnnihilator_not_dvd
#print axioms LambertAnnihilatorHeight.arbitrarily_small_nonzero_nearRow
#print axioms LambertAnnihilatorHeight.small_nondivisible_first_row
