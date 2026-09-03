import FormalConjecturesUtil

/-!
A counterexample to uniform realness of adjacent autocorrelations over all
bounded complex completely multiplicative functions. This is NOT a
counterexample to Erdős 371: these functions are not largest-prime-factor
labels, nor are they nonnegative multiplicative functions.
-/

namespace Erdos371.MultiplicativeChirpObstruction

open Finset Filter
open scoped Topology

noncomputable def chirp (t : ℝ) : ℕ →*₀ ℂ where
  toFun n := if n = 0 then 0 else Complex.exp (((t * Real.log n : ℝ) : ℂ) * Complex.I)
  map_zero' := by simp
  map_one' := by simp
  map_mul' a b := by
    by_cases ha : a = 0
    · subst a; simp
    by_cases hb : b = 0
    · subst b; simp
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    simp only [if_neg ha, if_neg hb, if_neg (mul_ne_zero ha hb), Nat.cast_mul,
      Real.log_mul ha' hb', mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

lemma chirp_apply (t : ℝ) (n : ℕ) (hn : n ≠ 0) :
    chirp t n = Complex.exp (((t * Real.log n : ℝ) : ℂ) * Complex.I) := by
  simp [chirp, hn]

lemma chirp_norm_le_one (t : ℝ) (n : ℕ) : ‖chirp t n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [chirp_apply t n hn, Complex.norm_exp_ofReal_mul_I]

lemma chirp_correlation_im (t : ℝ) (n : ℕ) (hn : 0 < n) :
    (chirp t (n + 1) * (starRingEnd ℂ) (chirp t n)).im =
      Real.sin (t * (Real.log (n + 1 : ℕ) - Real.log n)) := by
  rw [chirp_apply t (n + 1) (by omega), chirp_apply t n hn.ne',
    ← Complex.exp_conj, ← Complex.exp_add]
  have he : (((t * Real.log (n + 1 : ℕ) : ℝ) : ℂ) * Complex.I) +
      (starRingEnd ℂ) (((t * Real.log n : ℝ) : ℂ) * Complex.I) =
      (((t * (Real.log (n + 1 : ℕ) - Real.log n) : ℝ) : ℂ) * Complex.I) := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I,
      Complex.ofReal_mul, Complex.ofReal_sub]
    ring
  rw [he, Complex.exp_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one,
    Real.exp_zero, one_mul]

private lemma log_increment_bounds (x : ℝ) (hx : 0 < x) :
    1 / (x + 1) ≤ Real.log (x + 1) - Real.log x ∧
      Real.log (x + 1) - Real.log x ≤ 1 / x := by
  have hx' : 0 < x + 1 := by linarith
  have hratio : 0 < (x + 1) / x := div_pos hx' hx
  have hl := Real.one_sub_inv_le_log_of_pos hratio
  have hu := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div hx'.ne' hx.ne'] at hl hu
  constructor
  · convert hl using 1; field_simp; ring
  · convert hu using 1; field_simp; ring

private lemma sine_lower (x : ℝ) (hx : 9 / 10 ≤ x) (hx' : x ≤ 2) :
    7 / 10 ≤ Real.sin x := by
  have hs : (7 : ℝ) / 10 ≤ Real.sin (9 / 10) := by
    have h := Real.sin_gt_sub_cube (x := (9 : ℝ) / 10) (by norm_num) (by norm_num)
    norm_num at h
    linarith
  have hp := Real.pi_gt_three
  by_cases h : x ≤ Real.pi / 2
  · exact hs.trans (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) h hx)
  · have hm : Real.sin (9 / 10) ≤ Real.sin (Real.pi - x) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
    rw [Real.sin_pi_sub] at hm
    exact hs.trans hm

noncomputable def incrementPhase (N n : ℕ) : ℝ :=
  (N : ℝ) * (Real.log (n + 1 : ℕ) - Real.log n)

lemma incrementPhase_bounds (N n : ℕ) (hn : 0 < n) :
    (N : ℝ) / (n + 1 : ℕ) ≤ incrementPhase N n ∧
      incrementPhase N n ≤ (N : ℝ) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := log_increment_bounds (n : ℝ) hn'
  constructor
  · simpa [incrementPhase, mul_div_assoc] using
      mul_le_mul_of_nonneg_left h.1 (Nat.cast_nonneg (α := ℝ) N)
  · simpa [incrementPhase, mul_div_assoc] using
      mul_le_mul_of_nonneg_left h.2 (Nat.cast_nonneg (α := ℝ) N)

lemma increment_sine_nonneg (N n : ℕ) (hn : 0 < n) (h : N / 3 < n) :
    0 ≤ Real.sin (incrementPhase N n) := by
  have hb := incrementPhase_bounds N n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : (N : ℝ) ≤ 3 * n := by exact_mod_cast (show N ≤ 3 * n by omega)
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · exact (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans hb.1
  · have hd : (N : ℝ) / n ≤ 3 := (div_le_iff₀ hn').mpr (by linarith)
    exact (hb.2.trans hd).trans Real.pi_gt_three.le

lemma increment_sine_high (N n : ℕ) (hN : 9 ≤ N) (hn : n ≤ N) (h : N / 2 < n) :
    7 / 10 ≤ Real.sin (incrementPhase N n) := by
  have hn0 : 0 < n := by omega
  have hb := incrementPhase_bounds N n hn0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1 : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hN' : (9 : ℝ) ≤ N := by exact_mod_cast hN
  have h2 : (N : ℝ) ≤ 2 * n := by exact_mod_cast (show N ≤ 2 * n by omega)
  apply sine_lower
  · apply le_trans _ hb.1
    apply (le_div_iff₀ hn1).mpr
    push_cast
    linarith
  · exact hb.2.trans ((div_le_iff₀ hn').mpr (by linarith))

/-- A uniform lower bound for the imaginary part of the adjacent correlation.
The function itself depends on the endpoint N. -/
theorem chirp_correlation_sum_lower (N : ℕ) (hN : 9 ≤ N) :
    (N : ℝ) / 60 ≤
      ∑ n ∈ Ioc 0 N, (chirp N (n + 1) * (starRingEnd ℂ) (chirp N n)).im := by
  have he (n : ℕ) (hn : n ∈ Ioc 0 N) :
      (chirp N (n + 1) * (starRingEnd ℂ) (chirp N n)).im =
        Real.sin (incrementPhase N n) := by
    exact chirp_correlation_im N n (mem_Ioc.mp hn).1
  rw [sum_congr rfl he]
  have h3 : N / 3 ≤ N / 2 := Nat.div_le_div_left (by norm_num) (by norm_num)
  have h2 : N / 2 ≤ N := Nat.div_le_self _ _
  have hlow : -((N / 3 : ℕ) : ℝ) ≤ ∑ n ∈ Ioc 0 (N / 3), Real.sin (incrementPhase N n) := by
    have h := sum_le_sum (s := Ioc 0 (N / 3)) (fun n _ => Real.neg_one_le_sin (incrementPhase N n))
    simpa using h
  have hmid : 0 ≤ ∑ n ∈ Ioc (N / 3) (N / 2), Real.sin (incrementPhase N n) := by
    apply sum_nonneg
    intro n hn
    exact increment_sine_nonneg N n (by have := (mem_Ioc.mp hn).1; omega) (mem_Ioc.mp hn).1
  have hhigh : (7 / 10 : ℝ) * ((N : ℝ) - ((N / 2 : ℕ) : ℝ)) ≤
      ∑ n ∈ Ioc (N / 2) N, Real.sin (incrementPhase N n) := by
    have h := sum_le_sum (s := Ioc (N / 2) N) (fun n hn =>
      increment_sine_high N n hN (mem_Ioc.mp hn).2 (mem_Ioc.mp hn).1)
    simpa [Nat.cast_sub h2, mul_comm] using h
  rw [← sum_Ioc_consecutive (fun n => Real.sin (incrementPhase N n)) (Nat.zero_le _) h2,
    ← sum_Ioc_consecutive (fun n => Real.sin (incrementPhase N n)) (Nat.zero_le _) h3]
  have hd2 : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := by exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := N) (n := 2))
  have hd3 : ((N / 3 : ℕ) : ℝ) ≤ (N : ℝ) / 3 := by exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := N) (n := 3))
  linarith

noncomputable def chirpCorrelationMean (N : ℕ) : ℝ :=
  (∑ n ∈ Ioc 0 N, (chirp N (n + 1) * (starRingEnd ℂ) (chirp N n)).im) / N

lemma chirpCorrelationMean_lower (N : ℕ) (hN : 9 ≤ N) :
    1 / 60 ≤ chirpCorrelationMean N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  unfold chirpCorrelationMean
  apply (le_div_iff₀ hN').mpr
  simpa [div_eq_mul_inv, mul_comm] using chirp_correlation_sum_lower N hN

/-- In particular, complete multiplicativity and unit modulus do not justify
uniformly real adjacent correlations for an endpoint-dependent family. -/
theorem chirpCorrelationMean_not_tendsto_zero :
    ¬ Tendsto chirpCorrelationMean atTop (nhds 0) := by
  intro h
  have he := h.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 60)
  obtain ⟨N, hN, heN⟩ := (eventually_ge_atTop (9 : ℕ)).and he |>.exists
  exact (chirpCorrelationMean_lower N hN).not_gt heN

/-- Complete multiplicativity gives uniform control in the starting point,
provided the multiplier itself is close to one. -/
lemma chirp_dilation_bound (t : ℝ) (k n : ℕ) :
    ‖chirp t (k * n) - chirp t n‖ ≤ ‖chirp t k - 1‖ := by
  rw [map_mul]
  have he : chirp t k * chirp t n - chirp t n = (chirp t k - 1) * chirp t n := by ring
  rw [he, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (chirp_norm_le_one t n)

/-- Compactness of the countable torus supplies an unbounded sequence of
integer parameters for which every fixed positive multiplier tends to one.
The adjacent imaginary bias survives along the same sequence. -/
theorem exists_chirp_subsequence_fixed_multipliers :
    ∃ a : ℕ → ℕ, Tendsto a atTop atTop ∧
      (∀ k : ℕ, 0 < k → Tendsto (fun j => chirp (a j) k) atTop (nhds 1)) ∧
      ∀ᶠ j : ℕ in atTop, 1 / 60 ≤ chirpCorrelationMean (a j) := by
  let u : ℕ → (ℕ → Circle) := fun N k => Circle.exp ((N : ℝ) * Real.log (k + 1 : ℕ))
  obtain ⟨z, φ, hφ, hconv⟩ := CompactSpace.tendsto_subseq u
  let a : ℕ → ℕ := fun j => φ (j + j) - φ j
  have ha (j : ℕ) : j ≤ a j := by
    have h := hφ.add_le_nat j j
    dsimp [a]
    omega
  have hat : Tendsto a atTop atTop := tendsto_atTop_mono ha tendsto_id
  have hd : Tendsto (fun j : ℕ => j + j) atTop atTop :=
    (show StrictMono (fun j : ℕ => j + j) by intro i j hij; dsimp; omega).tendsto_atTop
  have hc : Tendsto (fun j => u (φ (j + j)) / u (φ j)) atTop (nhds (1 : ℕ → Circle)) := by
    simpa only [div_self'] using (hconv.comp hd).div' hconv
  have he (j k : ℕ) : u (φ (j + j)) k / u (φ j) k =
      Circle.exp ((a j : ℝ) * Real.log (k + 1 : ℕ)) := by
    dsimp [u, a]
    rw [← Circle.exp_sub, ← sub_mul, Nat.cast_sub (hφ.monotone (by omega : j ≤ j + j))]
  have hk (k : ℕ) : Tendsto (fun j => chirp (a j) (k + 1)) atTop (nhds 1) := by
    have hh := (tendsto_pi_nhds.mp hc) k
    have hh' : Tendsto (fun j => Circle.exp ((a j : ℝ) * Real.log (k + 1 : ℕ)))
        atTop (nhds (1 : Circle)) := by
      simpa only [Pi.div_apply, Pi.one_apply, he] using hh
    have hcoe := (continuous_subtype_val.tendsto (1 : Circle)).comp hh'
    simpa only [Circle.coe_exp, Circle.coe_one, chirp_apply _ _ (by omega : k + 1 ≠ 0)] using hcoe
  refine ⟨a, hat, ?_, ?_⟩
  · intro k hk0
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0.ne'
    exact hk m
  · filter_upwards [hat.eventually_ge_atTop 9] with j hj
    exact chirpCorrelationMean_lower (a j) hj

/-- Even asymptotic invariance under every fixed multiplier, uniformly in
all starting points, does not imply real natural autocorrelations for
arbitrary endpoint-dependent complex multiplicative functions. -/
theorem exists_dilation_stable_biased_chirps :
    ∃ a : ℕ → ℕ, Tendsto a atTop atTop ∧
      (∀ k : ℕ, 0 < k → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ j : ℕ in atTop, ∀ n : ℕ,
          ‖chirp (a j) (k * n) - chirp (a j) n‖ < ε) ∧
      ∀ᶠ j : ℕ in atTop, 1 / 60 ≤ chirpCorrelationMean (a j) := by
  obtain ⟨a, hat, hk, hb⟩ := exists_chirp_subsequence_fixed_multipliers
  refine ⟨a, hat, ?_, hb⟩
  intro k hk0 ε hε
  have he := (Metric.tendsto_nhds.mp (hk k hk0)) ε hε
  filter_upwards [he] with j hj
  intro n
  exact (chirp_dilation_bound (a j) k n).trans_lt (by simpa only [dist_eq_norm] using hj)

#print axioms exists_dilation_stable_biased_chirps

#print axioms chirp_correlation_sum_lower
#print axioms chirpCorrelationMean_not_tendsto_zero

end Erdos371.MultiplicativeChirpObstruction
