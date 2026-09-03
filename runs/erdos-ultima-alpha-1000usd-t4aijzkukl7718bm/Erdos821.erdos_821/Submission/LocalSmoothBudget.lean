import Submission.EndpointSmoothUpper

/-!
# A local smooth-predecessor budget for each inverse-totient fiber

These bounds are unconditional and finite. They do not assert the higher-root
smooth-prime abundance required by the original conjecture.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821

set_option maxHeartbeats 2000000

noncomputable def localSmoothMass (k n : ℕ) (s : ℝ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => d ∈ smoothShiftedPredecessors k), (d : ℝ)^(-s)

lemma localSmoothMass_nonneg (k n : ℕ) (s : ℝ) : 0 ≤ localSmoothMass k n s := by
  exact Finset.sum_nonneg (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _)

/-- The finite support sum, with no assumption about an infinite series. -/
lemma shifted_divisor_weight_sum_local (k : ℕ) (hk : 1 ≤ k) (s : ℝ)
    (hs : 0 ≤ s) (hs1 : s < 1) (n : ℕ) (hn : 0 < n) :
    (∑ p ∈ shiftedPrimeDivisors n, ((p-1 : ℕ) : ℝ)^(-s)) ≤
      localSmoothMass k n s + (1/(1-s)) *
        ∑ q ∈ n.primeFactors, (q : ℝ)^((k : ℝ)*(1-s)-1) := by
  let P := shiftedPrimeDivisors n
  let D := P.image (fun p => p-1)
  have hD (d : ℕ) (hd : d ∈ D) : 0 < d ∧ (d+1).Prime ∧ d ∣ n := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨_, hpprime, hpdvd⟩ := Finset.mem_filter.mp hp
    exact ⟨Nat.sub_pos_of_lt hpprime.one_lt,
      by simpa only [Nat.sub_add_cancel hpprime.one_lt.le] using hpprime, hpdvd⟩
  have hinj : Set.InjOn (fun p : ℕ => p-1) (↑P : Set ℕ) := by
    intro p hp q hq h
    change p ∈ shiftedPrimeDivisors n at hp
    change q ∈ shiftedPrimeDivisors n at hq
    have hp2 := (Finset.mem_filter.mp hp).2.1.two_le
    have hq2 := (Finset.mem_filter.mp hq).2.1.two_le
    change p-1 = q-1 at h
    omega
  let E := D.filter (fun d => d ∉ smoothShiftedPredecessors k)
  have hrough := rough_divisor_weight_sum_sharp E n.primeFactors k hk s hs hs1
    (fun d hd => (hD d (Finset.mem_filter.mp hd).1).1)
    (fun q hq => Nat.pos_of_mem_primeFactors hq) (by
      intro d hd
      obtain ⟨hdD, hdns⟩ := Finset.mem_filter.mp hd
      have hnot : ¬∀ q ∈ d.primeFactors, q^k ≤ d := fun h => hdns ⟨(hD d hdD).2.1, h⟩
      push_neg at hnot
      obtain ⟨q, hq, hqd⟩ := hnot
      refine ⟨q, ?_, Nat.dvd_of_mem_primeFactors hq, hqd.le⟩
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hq,
        (Nat.dvd_of_mem_primeFactors hq).trans (hD d hdD).2.2, hn.ne'⟩)
  have hsmooth : (∑ d ∈ D.filter (fun d => d ∈ smoothShiftedPredecessors k), (d : ℝ)^(-s)) ≤
      localSmoothMass k n s := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨hdD, hds⟩ := Finset.mem_filter.mp hd
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨(hD d hdD).2.2, hn.ne'⟩, hds⟩
    · intro d hd hdn
      exact Real.rpow_nonneg (Nat.cast_nonneg d) _
  change (∑ p ∈ P, ((p-1 : ℕ) : ℝ)^(-s)) ≤ _
  rw [← Finset.sum_image (f := fun d : ℕ => (d : ℝ)^(-s)) hinj]
  change (∑ d ∈ D, (d : ℝ)^(-s)) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not D (fun d => d ∈ smoothShiftedPredecessors k)]
  exact add_le_add hsmooth hrough

/-- Every inverse-totient fiber satisfies this local finite Rankin bound. -/
theorem g_le_local_smooth_mass (k : ℕ) (hk : 1 ≤ k) (s : ℝ)
    (hs : 0 ≤ s) (hs1 : s < 1) (n : ℕ) (hn : 0 < n) :
    (g n : ℝ) ≤ (n : ℝ)^s * Real.exp
      (localSmoothMass k n s + (1/(1-s)) *
        ∑ q ∈ n.primeFactors, (q : ℝ)^((k : ℝ)*(1-s)-1)) := by
  calc
    (g n : ℝ) ≤ Real.exp (∑ p ∈ shiftedPrimeDivisors n, ((p-1 : ℕ) : ℝ)^(-s)) *
        (n : ℝ)^s := g_le_rpow_mul_exp_shifted n hn s hs
    _ ≤ Real.exp (localSmoothMass k n s + (1/(1-s)) *
        ∑ q ∈ n.primeFactors, (q : ℝ)^((k : ℝ)*(1-s)-1)) * (n : ℝ)^s :=
      mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (shifted_divisor_weight_sum_local k hk s hs hs1 n hn))
        (Real.rpow_nonneg (Nat.cast_nonneg n) s)
    _ = _ := mul_comm _ _

/-- The endpoint rough cost is exactly bounded by k times omega(n). -/
theorem g_le_local_endpoint (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 0 < n) :
    (g n : ℝ) ≤ (n : ℝ)^(1-1/(k : ℝ)) * Real.exp
      (localSmoothMass k n (1-1/(k : ℝ)) + (k : ℝ)*n.primeFactors.card) := by
  have hb := reciprocal_exponent_bounds k hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have he : (k : ℝ)*(1-(1-1/(k : ℝ)))-1 = 0 := by field_simp; ring
  have h := g_le_local_smooth_mass k hk (1-1/(k : ℝ)) hb.1 hb.2 n hn
  rw [he] at h
  simpa only [Real.rpow_zero, Finset.sum_const, nsmul_eq_mul, mul_one,
    sub_sub_cancel, one_div_one_div] using h

/-- A large fiber must pay its entire excess exponent in local smooth mass,
up to the explicit prime-support error. -/
theorem large_g_forces_local_smooth_mass (k : ℕ) (hk : 1 ≤ k) (γ : ℝ)
    (n : ℕ) (hn : 0 < n) (hg : (n : ℝ)^γ < g n) :
    (γ-(1-1/(k : ℝ)))*Real.log n <
      localSmoothMass k n (1-1/(k : ℝ)) + (k : ℝ)*n.primeFactors.card := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := hg.trans_le (g_le_local_endpoint k hk n hn)
  rw [Real.rpow_def_of_pos hnR, Real.rpow_def_of_pos hnR, ← Real.exp_add,
    Real.exp_lt_exp] at h
  nlinarith

/-- On any fixed exponent above the endpoint, the local mass is eventually
at least a fixed positive multiple of log n whenever the fiber is large. -/
theorem eventually_large_g_forces_local_smooth_mass (k : ℕ) (hk : 1 ≤ k)
    (γ : ℝ) (hγ : 1-1/(k : ℝ) < γ) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ)^γ < g n →
      ((γ-(1-1/(k : ℝ)))/4)*Real.log n < localSmoothMass k n (1-1/(k : ℝ)) := by
  let Δ := γ-(1-1/(k : ℝ))
  have hΔ : 0 < Δ := sub_pos.mpr hγ
  obtain ⟨A, hA⟩ := exists_sum_primeFactors_rpow_nonpos_le_log 0 k (Δ/2)
    (by norm_num) (Nat.cast_nonneg _) (half_pos hΔ)
  have hlim : Tendsto (fun n : ℕ => (Δ/4)*Real.log n) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity)
  filter_upwards [eventually_ge_atTop 1, hlim.eventually (eventually_ge_atTop A)] with n hn hAn
  intro hg
  have hn0 : 0 < n := by omega
  have hsupport := hA n hn0
  simp only [neg_zero, Real.rpow_zero, Finset.sum_const, nsmul_eq_mul, mul_one] at hsupport
  have hmass := large_g_forces_local_smooth_mass k hk γ n hn0 hg
  change Δ*Real.log n < _ at hmass
  change (Δ/4)*Real.log n < _
  nlinarith

noncomputable def largeSmoothShiftedDivisors (k n T : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => d ∈ smoothShiftedPredecessors k ∧ T < d)

/-- Splitting the local mass at a finite cutoff keeps the upper tail's
cardinality rather than replacing it by an infinite series. -/
lemma localSmoothMass_le_cutoff_card (k n T : ℕ) (hT : 0 < T) (s : ℝ)
    (hs : 0 ≤ s) (hs1 : s < 1) :
    localSmoothMass k n s ≤ (T : ℝ)^(1-s)/(1-s) +
      (largeSmoothShiftedDivisors k n T).card * (T : ℝ)^(-s) := by
  let D := n.divisors.filter (fun d => d ∈ smoothShiftedPredecessors k)
  have hsmall : (∑ d ∈ D.filter (fun d => d ≤ T), (d : ℝ)^(-s)) ≤
      (T : ℝ)^(1-s)/(1-s) := by
    apply le_trans _ (sum_Icc_neg_rpow_le T s hs hs1)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨hdD, hdT⟩ := Finset.mem_filter.mp hd
      have hddiv := (Finset.mem_filter.mp hdD).1
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hddiv, hdT⟩
    · intro d hd hdn
      exact Real.rpow_nonneg (Nat.cast_nonneg d) _
  have htail : (∑ d ∈ D.filter (fun d => ¬d ≤ T), (d : ℝ)^(-s)) ≤
      (largeSmoothShiftedDivisors k n T).card * (T : ℝ)^(-s) := by
    have hset : D.filter (fun d => ¬d ≤ T) = largeSmoothShiftedDivisors k n T := by
      ext d
      simp [D, largeSmoothShiftedDivisors, and_assoc]
    rw [hset]
    calc
      _ ≤ ∑ _d ∈ largeSmoothShiftedDivisors k n T, (T : ℝ)^(-s) := by
        apply Finset.sum_le_sum
        intro d hd
        have hTd := (Finset.mem_filter.mp hd).2.2
        exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hT)
          (by exact_mod_cast hTd.le) (neg_nonpos.mpr hs)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  change (∑ d ∈ D, (d : ℝ)^(-s)) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not D (fun d => d ≤ T)]
  exact add_le_add hsmall htail

/-- At a perfect-power cutoff the endpoint cost has no real-power terms. -/
lemma localSmoothMass_endpoint_le_cutoff_card (k : ℕ) (hk : 1 ≤ k)
    (n B : ℕ) (hB : 0 < B) :
    localSmoothMass k n (1-1/(k : ℝ)) ≤ (k : ℝ)*B +
      (largeSmoothShiftedDivisors k n (B^k)).card * ((B : ℝ)^(k-1))⁻¹ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hb := reciprocal_exponent_bounds k hk
  have hc := localSmoothMass_le_cutoff_card k n (B^k) (pow_pos hB k)
    (1-1/(k : ℝ)) hb.1 hb.2
  have he1 : (k : ℝ)*(1-(1-1/(k : ℝ))) = 1 := by field_simp; ring
  have he2 : (k : ℝ)*(-(1-1/(k : ℝ))) = -((k-1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk, Nat.cast_one]
    field_simp
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul hBR.le, he1, Real.rpow_one,
    ← Real.rpow_natCast_mul hBR.le, he2, Real.rpow_neg hBR.le,
    Real.rpow_natCast] at hc
  have hden : (B : ℝ)/(1-(1-1/(k : ℝ))) = (k : ℝ)*B := by
    rw [sub_sub_cancel]
    field_simp
  rw [hden] at hc
  exact hc

/-- A completely explicit count of the large smooth shifted divisors
required by a large fiber. The output n need not be a normalized record. -/
theorem large_g_forces_large_smooth_divisors (k : ℕ) (hk : 1 ≤ k)
    (B : ℕ) (hB : 0 < B) (γ : ℝ) (n : ℕ) (hn : 0 < n)
    (hg : (n : ℝ)^γ < g n) :
    (((γ-(1-1/(k : ℝ)))*Real.log n - (k : ℝ)*n.primeFactors.card - (k : ℝ)*B) *
      (B : ℝ)^(k-1)) < (largeSmoothShiftedDivisors k n (B^k)).card := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hc := localSmoothMass_endpoint_le_cutoff_card k hk n B hB
  have hm := large_g_forces_local_smooth_mass k hk γ n hn hg
  have hcount : (γ-(1-1/(k : ℝ)))*Real.log n -
      (k : ℝ)*n.primeFactors.card - (k : ℝ)*B <
        (largeSmoothShiftedDivisors k n (B^k)).card * ((B : ℝ)^(k-1))⁻¹ := by
    linarith
  have hBp : (0 : ℝ) < (B : ℝ)^(k-1) := pow_pos hBR _
  have h := mul_lt_mul_of_pos_right hcount hBp
  simpa only [mul_assoc, inv_mul_cancel₀ hBp.ne', mul_one] using h

/-- A fixed exponent above the endpoint forces polynomially many smooth
shifted divisors in log n, all beyond a comparable k-th power cutoff. -/
theorem eventually_large_g_forces_log_pow_many_smooth_divisors
    (k : ℕ) (hk : 1 ≤ k) (γ : ℝ) (hγ : 1-1/(k : ℝ) < γ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (n : ℝ)^γ < g n → C*(Real.log n)^k <
        (largeSmoothShiftedDivisors k n (⌊c*Real.log n⌋₊^k)).card := by
  let Δ := γ-(1-1/(k : ℝ))
  let c := Δ/(8*(k : ℝ))
  let C := (Δ/8)*(c/2)^(k-1)
  have hΔ : 0 < Δ := sub_pos.mpr hγ
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hc : 0 < c := div_pos hΔ (by positivity)
  have hC : 0 < C := by dsimp [C]; positivity
  have hkc : (k : ℝ)*c = Δ/8 := by dsimp [c]; field_simp
  refine ⟨c, C, hc, hC, ?_⟩
  have hlim : Tendsto (fun n : ℕ => c*Real.log n) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
  filter_upwards [eventually_large_g_forces_local_smooth_mass k hk γ hγ,
    hlim.eventually (eventually_ge_atTop 2)] with n hn hscale
  intro hg
  let B := ⌊c*Real.log n⌋₊
  have hB2 : 2 ≤ B := Nat.le_floor hscale
  have hB : 0 < B := by omega
  have hlog : 0 < Real.log n := by nlinarith
  have hBle : (B : ℝ) ≤ c*Real.log n := Nat.floor_le (by positivity)
  have hBlt : c*Real.log n < (B : ℝ)+1 := Nat.lt_floor_add_one _
  have hBge : (c/2)*Real.log n ≤ B := by nlinarith
  have hlocal := hn hg
  change (Δ/4)*Real.log n < _ at hlocal
  have hcut := localSmoothMass_endpoint_le_cutoff_card k hk n B hB
  have hcost : (k : ℝ)*B ≤ (Δ/8)*Real.log n := by
    calc
      _ ≤ (k : ℝ)*(c*Real.log n) := mul_le_mul_of_nonneg_left hBle hkR.le
      _ = _ := by rw [← mul_assoc, hkc]
  have htail : (Δ/8)*Real.log n <
      (largeSmoothShiftedDivisors k n (B^k)).card * ((B : ℝ)^(k-1))⁻¹ := by
    linarith
  have hBp : (0 : ℝ) < (B : ℝ)^(k-1) := pow_pos (by exact_mod_cast hB) _
  have hcount : ((Δ/8)*Real.log n)*(B : ℝ)^(k-1) <
      (largeSmoothShiftedDivisors k n (B^k)).card := by
    have h := mul_lt_mul_of_pos_right htail hBp
    simpa only [mul_assoc, inv_mul_cancel₀ hBp.ne', mul_one] using h
  apply lt_of_le_of_lt _ hcount
  have hp := pow_le_pow_left₀ (show 0 ≤ (c/2)*Real.log n by positivity) hBge (k-1)
  have h := mul_le_mul_of_nonneg_left hp (show 0 ≤ (Δ/8)*Real.log n by positivity)
  convert h using 1
  dsimp [C]
  have he : (Real.log n)^k = (Real.log n)^(k-1)*Real.log n := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  rw [mul_pow, he]
  ring

end Erdos821
