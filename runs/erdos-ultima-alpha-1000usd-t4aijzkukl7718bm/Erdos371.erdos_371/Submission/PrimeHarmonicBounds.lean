import Submission.HarmonicCofactorCutoff

/-! Elementary quantitative estimates for prime reciprocal sums. The lower
bound uses the finite Euler product, not the prime number theorem. -/

namespace Erdos371
open Finset

noncomputable def reciprocalNatHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' := by intros; simp [mul_inv_rev, mul_comm]

lemma harmonic_le_primeEulerProduct (z : ℕ) :
    (harmonic z : ℝ) ≤ ∏ p ∈ (z+1).primesBelow, (1-(p : ℝ)⁻¹)⁻¹ := by
  classical
  have hp : ∀ {p : ℕ}, p.Prime → ‖reciprocalNatHom p‖ < 1 := by
    intro p hp
    change ‖(p : ℝ)⁻¹‖ < 1
    rw [norm_inv, Real.norm_natCast]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hE := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hp (z+1)
  let f : {n // n ∈ Icc 1 z} → (z+1).smoothNumbers := fun n =>
    ⟨n.val, Nat.mem_smoothNumbers_of_lt (mem_Icc.mp n.property).1 (by have := (mem_Icc.mp n.property).2; omega)⟩
  have hinj : Function.Injective f := by
    intro n m h
    exact Subtype.ext (congrArg (fun u : (z+1).smoothNumbers => u.val) h)
  have h := hE.2.summable.sum_le_tsum ((Icc 1 z).attach.image f) (fun n _ => by
    change 0 ≤ (n.val : ℝ)⁻¹
    positivity)
  rw [hE.2.tsum_eq, sum_image (fun _ _ _ _ he => hinj he)] at h
  change (∑ x ∈ (Icc 1 z).attach, (x.val : ℝ)⁻¹) ≤
    ∏ p ∈ (z+1).primesBelow, (1-(p : ℝ)⁻¹)⁻¹ at h
  rw [sum_attach (Icc 1 z) (fun n : ℕ => (n : ℝ)⁻¹)] at h
  simpa [harmonic_eq_sum_Icc] using h

lemma reciprocal_correction_sum_eq (z : ℕ) :
    (∑ p ∈ Icc 2 (z+1), ((1 : ℝ)/((p : ℝ)-1) - 1/p)) = 1-1/(z+1 : ℝ) := by
  induction z with
  | zero => simp
  | succ z ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    push_cast
    ring_nf

lemma prime_reciprocal_correction_le (z : ℕ) :
    (∑ p ∈ (z+1).primesBelow, ((1 : ℝ)/((p : ℝ)-1) - 1/p)) ≤ 1 := by
  have hsub : (z+1).primesBelow ⊆ Icc 2 (z+1) := by
    intro p hp
    obtain ⟨hpz, hpp⟩ := Nat.mem_primesBelow.mp hp
    exact mem_Icc.mpr ⟨hpp.two_le, hpz.le⟩
  calc
    _ ≤ ∑ p ∈ Icc 2 (z+1), ((1 : ℝ)/((p : ℝ)-1) - 1/p) := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_Icc.mp hp).1
      apply sub_nonneg.mpr
      exact one_div_le_one_div_of_le (by linarith) (by linarith)
    _ = 1-1/(z+1 : ℝ) := reciprocal_correction_sum_eq z
    _ ≤ 1 := by
      have h : (0 : ℝ) ≤ 1/(z+1 : ℝ) := by positivity
      linarith

lemma primeEulerProduct_le_exp (z : ℕ) :
    (∏ p ∈ (z+1).primesBelow, (1-(p : ℝ)⁻¹)⁻¹) ≤ Real.exp (primeHarmonic z + 1) := by
  have hlocal (p : ℕ) (hp : p ∈ (z+1).primesBelow) :
      0 ≤ (1-(p : ℝ)⁻¹)⁻¹ ∧ (1-(p : ℝ)⁻¹)⁻¹ ≤ Real.exp (1/((p : ℝ)-1)) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.two_le
    have hpos : 0 < 1-(p : ℝ)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ (by linarith))
    refine ⟨inv_nonneg.mpr hpos.le, ?_⟩
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    have he : (1-(p : ℝ)⁻¹)⁻¹ - 1 = 1/((p : ℝ)-1) := by
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      have hp1 : (p : ℝ)-1 ≠ 0 := by linarith
      field_simp
      ring
    rw [he] at h
    simpa only [Real.exp_log (inv_pos.mpr hpos)] using Real.exp_le_exp.mpr h
  calc
    _ ≤ ∏ p ∈ (z+1).primesBelow, Real.exp (1/((p : ℝ)-1)) :=
      prod_le_prod (fun p hp => (hlocal p hp).1) (fun p hp => (hlocal p hp).2)
    _ = Real.exp (∑ p ∈ (z+1).primesBelow, 1/((p : ℝ)-1)) := (Real.exp_sum _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h := prime_reciprocal_correction_le z
      rw [sum_sub_distrib] at h
      change _ - primeHarmonic z ≤ 1 at h
      linarith

/-- A quantitative lower bound for the prime harmonic sum, in exponential
form. In particular it gives `H(z) ≥ log log(z+1) - 1` for `z ≥ 1`. -/
theorem log_le_exp_primeHarmonic (z : ℕ) :
    Real.log (z+1 : ℝ) ≤ Real.exp (primeHarmonic z + 1) := by
  have h := (log_add_one_le_harmonic z).trans
    ((harmonic_le_primeEulerProduct z).trans (primeEulerProduct_le_exp z))
  simpa only [Nat.cast_add, Nat.cast_one] using h

theorem log_log_le_primeHarmonic_add_one (z : ℕ) (hz : 1 ≤ z) :
    Real.log (Real.log (z+1 : ℝ)) ≤ primeHarmonic z + 1 := by
  have hpos : 0 < Real.log (z+1 : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < z+1 by omega))
  simpa only [Real.log_exp] using Real.log_le_log hpos (log_le_exp_primeHarmonic z)

/-- The logarithmic saving furnished by the prime reciprocal mass. -/
theorem exp_neg_two_primeHarmonic_le (z : ℕ) (hz : 1 ≤ z) :
    Real.exp (-2*primeHarmonic z) ≤ Real.exp 2 / (Real.log (z+1 : ℝ))^2 := by
  have hpos : 0 < Real.log (z+1 : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < z+1 by omega))
  have h := log_le_exp_primeHarmonic z
  have hs : (Real.log (z+1 : ℝ))^2 ≤ (Real.exp (primeHarmonic z+1))^2 :=
    pow_le_pow_left₀ hpos.le h 2
  apply (le_div_iff₀ (sq_pos_of_pos hpos)).mpr
  have ht := mul_le_mul_of_nonneg_left hs (Real.exp_nonneg (-2*primeHarmonic z))
  convert ht using 1
  rw [sq, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

lemma primeHarmonic_monotone : Monotone primeHarmonic := by
  intro B C hBC
  unfold primeHarmonic primeReciprocalSum
  apply sum_le_sum_of_subset_of_nonneg
  · exact filter_subset_filter _ (range_mono (by omega))
  · intros; positivity

lemma primeHarmonic_square_step (B : ℕ) (hB : 2 ≤ B) :
    primeHarmonic (B^2) ≤ primeHarmonic B + 12 := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlogB : 0 < Real.log B := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hBN : B ≤ B^2 := by nlinarith
  have hmass := mediumPrimes_sum B (B^2) hBN
  have hweight : Real.log B * primeReciprocalSum (mediumPrimes B (B^2)) ≤
      ∑ p ∈ (B^2+1).primesBelow, Real.log (p : ℕ) / ((p : ℝ)-1) := by
    unfold primeReciprocalSum
    rw [mul_sum]
    calc
      _ ≤ ∑ p ∈ mediumPrimes B (B^2), Real.log (p : ℕ) / ((p : ℝ)-1) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨hpp, hBp, hpB⟩ := mem_mediumPrimes.mp hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
        have hlog : Real.log B ≤ Real.log p := Real.log_le_log hB0 (by exact_mod_cast hBp.le)
        have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
        calc
          _ = Real.log B / p := by ring
          _ ≤ Real.log p / p := div_le_div_of_nonneg_right hlog (by positivity)
          _ ≤ _ := div_le_div_of_nonneg_left hlogp (by linarith) (by linarith)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg sdiff_subset (fun p hp _ => by
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.two_le
        exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith))
  have hupper := prime_log_div_pred_sum_le (B^2+1)
  have hpow : B^2+1 ≤ B^3 := by nlinarith [Nat.mul_le_mul_left (B^2) hB]
  have hlogs : Real.log (B^2+1 : ℕ) ≤ 3*Real.log B := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (B^2+1 : ℕ))
      (show ((B^2+1 : ℕ) : ℝ) ≤ ((B^3 : ℕ) : ℝ) by exact_mod_cast hpow)
    simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using h
  nlinarith

/-- A coarse upper Mertens bound at doubly exponential endpoints. -/
theorem primeHarmonic_double_power_le (u : ℕ) :
    primeHarmonic (2^(2^u)) ≤ 12*(u+1 : ℝ) := by
  induction u with
  | zero => norm_num [primeHarmonic, primeReciprocalSum, Nat.primesBelow, sum_filter, sum_range_succ]
  | succ u ih =>
    have hB : 2 ≤ 2^(2^u) := by
      exact (Nat.le_pow (by positivity : 0 < 2^u)).trans_eq (by rfl)
    have h := primeHarmonic_square_step (2^(2^u)) hB
    have he : 2^(2^(u+1)) = (2^(2^u))^2 := by rw [pow_succ (2 : ℕ) u, pow_mul]
    rw [he]
    push_cast
    linarith

/-- A uniform upper bound using two integer logarithms. -/
theorem primeHarmonic_le_double_log (z : ℕ) :
    primeHarmonic z ≤ 12 * (Nat.log 2 (Nat.log 2 z) + 2 : ℝ) := by
  have h1 := Nat.lt_pow_succ_log_self (by decide : 1 < 2) z
  have h2 := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (Nat.log 2 z)
  have hz : z ≤ 2^(2^(Nat.log 2 (Nat.log 2 z)+1)) := by
    exact h1.le.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  have h := (primeHarmonic_monotone hz).trans
    (primeHarmonic_double_power_le (Nat.log 2 (Nat.log 2 z)+1))
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h

#print axioms exp_neg_two_primeHarmonic_le
#print axioms primeHarmonic_le_double_log
#print axioms log_le_exp_primeHarmonic
end Erdos371
