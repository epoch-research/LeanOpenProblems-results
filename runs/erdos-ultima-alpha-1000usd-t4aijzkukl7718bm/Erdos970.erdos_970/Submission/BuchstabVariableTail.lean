import Submission.BuchstabIteratedGrid

/-! Variable terminal cutoffs for the finite-prime Buchstab sums. The omitted
small-prime tails can be made arbitrarily small; the previous fixed cutoff13
is not used as a vanishing error. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real Filter FiniteSelberg
set_option maxHeartbeats 1000000

noncomputable def terminalCut (M L : ℝ) : ℕ := ⌊exp (L/M)⌋₊
noncomputable def terminalPart (M : ℝ) (k : ℕ) (L : ℝ) : Finset ℕ :=
  (nthPrime k).primesBelow.filter (fun p => p ≤ terminalCut M L)
noncomputable def terminalAllowance (B M : ℝ) : ℝ :=
  (9*B/35)/M^7+(18*B*WeightedMertens.sharpMomentError/5)/M^6

lemma terminalCut_pos (M L : ℝ) (hM : 0 < M) (hL : 0 ≤ L) : 0 < terminalCut M L :=
  Nat.floor_pos.mpr (one_le_exp (div_nonneg hL hM.le))

lemma terminalCut_log_le (M L : ℝ) (hM : 0 < M) (hL : 0 ≤ L) :
    M*log (terminalCut M L : ℝ) ≤ L := by
  have hc0 : (0 : ℝ) < terminalCut M L := by exact_mod_cast terminalCut_pos M L hM hL
  have hh := log_le_log hc0 (Nat.floor_le (exp_pos (L/M)).le)
  rw [log_exp] at hh
  have hm := mul_le_mul_of_nonneg_left hh hM.le
  have he : M*(L/M)=L := by field_simp
  simpa only [he] using hm

lemma terminalPart_subset (M : ℝ) (k : ℕ) (L : ℝ) :
    terminalPart M k L ⊆ (terminalCut M L+1).primesBelow := by
  intro p hp
  obtain ⟨hpk,hpc⟩ := mem_filter.mp hp
  exact WeightedMertens.mem_primes.mpr ⟨(Nat.mem_primesBelow.mp hpk).2,hpc⟩

lemma terminalAllowance_nonneg (B M : ℝ) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    0 ≤ terminalAllowance B M := by
  have := WeightedMertens.sharpMomentError_pos
  unfold terminalAllowance
  positivity

lemma terminalAllowance_le (B M : ℝ) (hB : 0 ≤ B) (hM : 1 ≤ M) :
    terminalAllowance B M ≤ (9*B/35+18*B*WeightedMertens.sharpMomentError/5)/M := by
  have hM0 : 0 < M := by linarith
  have hM7 : M ≤ M^7 := by
    have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ hM : 1 ≤ M^6) hM0.le
    nlinarith only [hh]
  have hM6 : M ≤ M^6 := by
    have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ hM : 1 ≤ M^5) hM0.le
    nlinarith only [hh]
  have he := WeightedMertens.sharpMomentError_pos
  have h7 := div_le_div_of_nonneg_left (show 0 ≤ 9*B/35 by positivity) hM0 hM7
  have h6 := div_le_div_of_nonneg_left (show 0 ≤ 18*B*WeightedMertens.sharpMomentError/5 by positivity) hM0 hM6
  unfold terminalAllowance
  calc
    _ ≤ (9*B/35)/M+(18*B*WeightedMertens.sharpMomentError/5)/M := add_le_add h7 h6
    _ = _ := by ring

lemma exists_small_terminalAllowance (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ M : ℝ, 13 ≤ M ∧ terminalAllowance B M < ε := by
  let A := 9*B/35+18*B*WeightedMertens.sharpMomentError/5
  let M := max 13 (A/ε+1)
  have h13 : 13 ≤ M := le_max_left _ _
  have hM0 : 0 < M := by linarith
  have hM : A/ε+1 ≤ M := le_max_right _ _
  refine ⟨M,h13,(terminalAllowance_le B M hB (by linarith)).trans_lt ?_⟩
  change A/M < ε
  apply (div_lt_iff₀ hM0).mpr
  have hh : A/ε < M := by linarith only [hM]
  have ht := (div_lt_iff₀ hε).mp hh
  linarith only [ht]

lemma exists_large_small_terminalAllowance (B ε R : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ M : ℝ, 13 ≤ M ∧ R < M ∧ terminalAllowance B M < ε := by
  let A := 9*B/35+18*B*WeightedMertens.sharpMomentError/5
  let M := max 13 (max (R+1) (A/ε+1))
  have h13 : 13 ≤ M := le_max_left _ _
  have hM0 : 0 < M := by linarith
  have hRM : R+1 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hM : A/ε+1 ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨M,h13,by linarith only [hRM],(terminalAllowance_le B M hB (by linarith)).trans_lt ?_⟩
  change A/M < ε
  apply (div_lt_iff₀ hM0).mpr
  have hh : A/ε < M := by linarith only [hM]
  have ht := (div_lt_iff₀ hε).mp hh
  linarith only [ht]

lemma normalized_variable_moment_le (S E L s R B M : ℝ)
    (hS : S ≤ (B/(s*L)^8)*(R^7/7+2*WeightedMertens.sharpMomentError*R^6))
    (hE : 0 ≤ E) (hEu : E ≤ (9/5)*L) (hL : 1 ≤ L) (hs : 1 ≤ s)
    (hR : 0 ≤ R) (hMR : M*R ≤ s*L) (hB : 0 ≤ B) (hM : 0 < M) :
    E*S ≤ terminalAllowance B M/s := by
  have hL0 : 0 < L := by linarith
  have hs0 : 0 < s := by linarith
  have hτ : 0 < s*L := mul_pos hs0 hL0
  have hRe : R ≤ s*L/M := (le_div_iff₀ hM).mpr (by nlinarith only [hMR])
  have h7 := pow_le_pow_left₀ hR hRe 7
  have h6 := pow_le_pow_left₀ hR hRe 6
  have herr := WeightedMertens.sharpMomentError_pos
  let V := (B/(s*L)^8)*(((s*L)/M)^7/7+2*WeightedMertens.sharpMomentError*((s*L)/M)^6)
  have hSV : S ≤ V := hS.trans (mul_le_mul_of_nonneg_left
    (add_le_add (div_le_div_of_nonneg_right h7 (by norm_num))
      (mul_le_mul_of_nonneg_left h6 (by positivity))) (by positivity))
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have heq : ((9/5)*L)*V = (9*B/35)/M^7/s+
      (18*B*WeightedMertens.sharpMomentError/5)/M^6/(s^2*L) := by
    dsimp [V]
    field_simp
    ring
  have hh := (mul_le_mul_of_nonneg_left hSV hE).trans
    (mul_le_mul_of_nonneg_right hEu hV)
  rw [heq] at hh
  have hden : s ≤ s^2*L := by nlinarith only [hs,hL]
  have hterm := div_le_div_of_nonneg_left
    (show 0 ≤ (18*B*WeightedMertens.sharpMomentError/5)/M^6 by positivity) hs0 hden
  unfold terminalAllowance
  apply hh.trans
  calc
    _ ≤ (9*B/35)/M^7/s+(18*B*WeightedMertens.sharpMomentError/5)/M^6/s := add_le_add le_rfl hterm
    _ = _ := by ring

lemma variable_initial_tail_finite (k W : ℕ) (hW : 0 < W)
    (hthreshold : 50*WeightedMertens.sharpMomentError ≤ log (W : ℝ))
    (hthreshold' : supportMassLogThreshold ≤ log (W : ℝ))
    (hRW : W*(firstHitWheel W)^2 ≤ nthPrime k) (hlog : 1 ≤ log (nthPrime k : ℝ))
    (hEuler : eulerMass (nthPrime k+1).primesBelow ≤ (9/5 : ℝ)*log (nthPrime k : ℝ))
    (M s : ℝ) (hM : 13 ≤ M) (hs : 1 ≤ s) :
    eulerMass (nthPrime k).primesBelow*
      (∑ p ∈ terminalPart M k (s*log (nthPrime k : ℝ)), scaledPrimeExcess (s*log (nthPrime k : ℝ)) p) ≤
      terminalAllowance initialTailCoefficient M/s := by
  let L := log (nthPrime k : ℝ)
  let R := terminalCut M (s*L)
  have hM0 : 0 < M := by linarith
  have hL : 0 < L := by dsimp [L]; linarith
  have hs0 : 0 < s := by linarith
  have hτ : 0 < s*L := mul_pos hs0 hL
  have hR : 0 < R := terminalCut_pos _ _ hM0 hτ.le
  have hMR : M*log (R : ℝ) ≤ s*L := terminalCut_log_le _ _ hM0 hτ.le
  have h13 : 13*log (R : ℝ) ≤ s*L :=
    (mul_le_mul_of_nonneg_right hM (log_natCast_nonneg R)).trans hMR
  have hsmall : (W : ℝ)*(firstHitWheel W : ℝ)^2 ≤ exp (s*L) := by
    have hWR : (W : ℝ)*(firstHitWheel W : ℝ)^2 ≤ nthPrime k := by exact_mod_cast hRW
    apply hWR.trans
    rw [← exp_log (show (0 : ℝ) < nthPrime k by exact_mod_cast (nthPrime_prime k).pos)]
    apply exp_le_exp.mpr
    change L ≤ s*L
    nlinarith only [hL,hs]
  have hsum := scaled_excess_sum_thirteenth_tail (terminalPart M k (s*L)) R W hR hW
    (terminalPart_subset M k (s*L)) (s*L) hτ h13 hsmall hthreshold hthreshold'
  have hS : (∑ p ∈ terminalPart M k (s*L), scaledPrimeExcess (s*L) p) ≤
      (initialTailCoefficient/(s*L)^8)*(log (R : ℝ)^7/7+2*WeightedMertens.sharpMomentError*log (R : ℝ)^6) := by
    convert hsum using 1 <;> dsimp [initialTailCoefficient] <;> ring
  exact normalized_variable_moment_le _ _ L s (log (R : ℝ)) initialTailCoefficient M hS
    (eulerMass_pos _ (fun p hp => (Nat.mem_primesBelow.mp hp).2)).le
    ((eulerMass_strict_prefix_le _ (nthPrime_prime k)).trans hEuler) hlog hs
    (log_natCast_nonneg R) hMR initialTailCoefficient_nonneg hM0

/-- Every refinement depth inherits one uniform variable-cutoff source tail. -/
theorem exists_variable_upper_tail (M : ℝ) (hM : 13 ≤ M) :
    ∃ N : ℕ, ∀ n k : ℕ, N ≤ nthPrime k → ∀ s : ℝ, 1 ≤ s →
      eulerMass (nthPrime k).primesBelow*
        (∑ p ∈ terminalPart M k (s*log (nthPrime k : ℝ)), primeUpperExcess n (s*log (nthPrime k : ℝ)) p) ≤
        terminalAllowance initialTailCoefficient M/s := by
  obtain ⟨W,hW,h1,h2⟩ := exists_tail_threshold_wheel
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((eventually_ge_atTop (W*(firstHitWheel W)^2)).and
    ((hlog.eventually_ge_atTop 1).and eventually_eulerMass_initial_le_nine_fifths_log))
  refine ⟨N,fun n k hk s hs => ?_⟩
  obtain ⟨hRW,hL,hEuler⟩ := hN (nthPrime k) hk
  apply le_trans _ (variable_initial_tail_finite k W hW h1 h2 hRW hL hEuler M s hM hs)
  apply mul_le_mul_of_nonneg_left _
    (eulerMass_pos _ (fun p hp => (Nat.mem_primesBelow.mp hp).2)).le
  apply sum_le_sum
  intro p hp
  have hpp := (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2
  exact (primeUpperExcess_le_zero n _ p).trans_eq (primeUpperExcess_zero _ p hpp)

/-- Arbitrarily small tails for the actual finite-prime upper excess, uniformly
in all depths and parent exponents s>=1. -/
theorem exists_vanishing_upper_tail (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 13 ≤ M ∧ ∃ N : ℕ, ∀ n k : ℕ, N ≤ nthPrime k → ∀ s : ℝ, 1 ≤ s →
      eulerMass (nthPrime k).primesBelow*
        (∑ p ∈ terminalPart M k (s*log (nthPrime k : ℝ)), primeUpperExcess n (s*log (nthPrime k : ℝ)) p) ≤ ε/s := by
  obtain ⟨M,hM,hT⟩ := exists_small_terminalAllowance initialTailCoefficient ε initialTailCoefficient_nonneg hε
  obtain ⟨N,hN⟩ := exists_variable_upper_tail M hM
  exact ⟨M,hM,N,fun n k hk s hs => (hN n k hk s hs).trans
    (div_le_div_of_nonneg_right hT.le (by linarith))⟩

lemma variable_lower_tail_finite (k W N : ℕ) (hW : 0 < W)
    (hNW : N ≤ W) (hN : LowerTailValid N)
    (hthreshold : supportMassLogThreshold ≤ log (W : ℝ))
    (hRW : W^3+W^2*(firstHitWheel W)^2 ≤ nthPrime k)
    (hlog : 1 ≤ log (nthPrime k : ℝ))
    (hEuler : eulerMass (nthPrime k+1).primesBelow ≤ (9/5 : ℝ)*log (nthPrime k : ℝ))
    (M s : ℝ) (hM : 13 ≤ M) (hs : 1 ≤ s) :
    eulerMass (nthPrime k).primesBelow*
      (∑ p ∈ terminalPart M k (s*log (nthPrime k : ℝ)), primeLowerDeficit (s*log (nthPrime k : ℝ)) p) ≤
      terminalAllowance lowerTailCoefficient M/s := by
  let L := log (nthPrime k : ℝ)
  let R := terminalCut M (s*L)
  have hM0 : 0 < M := by linarith
  have hL : 0 < L := by dsimp [L]; linarith
  have hs0 : 0 < s := by linarith
  have hτ : 0 < s*L := mul_pos hs0 hL
  have hR : 0 < R := terminalCut_pos _ _ hM0 hτ.le
  have hMR : M*log (R : ℝ) ≤ s*L := terminalCut_log_le _ _ hM0 hτ.le
  have h13 : 13*log (R : ℝ) ≤ s*L :=
    (mul_le_mul_of_nonneg_right hM (log_natCast_nonneg R)).trans hMR
  have hsmall : (W : ℝ)^3+(W : ℝ)^2*(firstHitWheel W : ℝ)^2 ≤ exp (s*L) := by
    have hWR : (W : ℝ)^3+(W : ℝ)^2*(firstHitWheel W : ℝ)^2 ≤ nthPrime k := by exact_mod_cast hRW
    apply hWR.trans
    rw [← exp_log (show (0 : ℝ) < nthPrime k by exact_mod_cast (nthPrime_prime k).pos)]
    apply exp_le_exp.mpr
    change L ≤ s*L
    nlinarith only [hL,hs]
  have hsmall1 : (W : ℝ)^3 ≤ exp (s*L) := by
    have hz : (0 : ℝ) ≤ (W : ℝ)^2*(firstHitWheel W : ℝ)^2 := by positivity
    linarith only [hsmall,hz]
  have hsmall2 : (W : ℝ)^2*(firstHitWheel W : ℝ)^2 ≤ exp (s*L) := by
    have hz : (0 : ℝ) ≤ (W : ℝ)^3 := by positivity
    linarith only [hsmall,hz]
  have hsum := lower_deficit_sum_le_moment (terminalPart M k (s*L)) R W N hR hW
    (terminalPart_subset M k (s*L)) hNW hN (s*L) hτ h13 hsmall1 hsmall2 hthreshold
  exact normalized_variable_moment_le _ _ L s (log (R : ℝ)) lowerTailCoefficient M hsum
    (eulerMass_pos _ (fun p hp => (Nat.mem_primesBelow.mp hp).2)).le
    ((eulerMass_strict_prefix_le _ (nthPrime_prime k)).trans hEuler) hlog hs
    (log_natCast_nonneg R) hMR lowerTailCoefficient_nonneg hM0

/-- The lower-deficit tail is uniform in refinement depth as well. -/
theorem exists_variable_lower_tail (M : ℝ) (hM : 13 ≤ M) :
    ∃ N : ℕ, ∀ n k : ℕ, N ≤ nthPrime k → ∀ s : ℝ, 1 ≤ s →
      eulerMass (nthPrime k).primesBelow*
        (∑ p ∈ terminalPart M k (s*log (nthPrime k : ℝ)), primeDeficit n (s*log (nthPrime k : ℝ)) p) ≤
        terminalAllowance lowerTailCoefficient M/s := by
  obtain ⟨N₀,hN₀⟩ := exists_lowerTailValid
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨W,hW,hNW,hWlog⟩ := ((eventually_ge_atTop 1).and
    ((eventually_ge_atTop N₀).and (hlog.eventually_ge_atTop supportMassLogThreshold))).exists
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((eventually_ge_atTop (W^3+W^2*(firstHitWheel W)^2)).and
    ((hlog.eventually_ge_atTop 1).and eventually_eulerMass_initial_le_nine_fifths_log))
  refine ⟨N,fun n k hk s hs => ?_⟩
  obtain ⟨hRW,hL,hEuler⟩ := hN (nthPrime k) hk
  apply le_trans _ (variable_lower_tail_finite k W N₀ (by omega) hNW hN₀ hWlog hRW hL hEuler M s hM hs)
  apply mul_le_mul_of_nonneg_left _
    (eulerMass_pos _ (fun p hp => (Nat.mem_primesBelow.mp hp).2)).le
  exact sum_le_sum (fun p _ => primeDeficit_le_zero n _ p)

theorem exists_vanishing_lower_tail (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 13 ≤ M ∧ ∃ N : ℕ, ∀ n k : ℕ, N ≤ nthPrime k → ∀ s : ℝ, 1 ≤ s →
      eulerMass (nthPrime k).primesBelow*
        (∑ p ∈ terminalPart M k (s*log (nthPrime k : ℝ)), primeDeficit n (s*log (nthPrime k : ℝ)) p) ≤ ε/s := by
  obtain ⟨M,hM,hT⟩ := exists_small_terminalAllowance lowerTailCoefficient ε lowerTailCoefficient_nonneg hε
  obtain ⟨N,hN⟩ := exists_variable_lower_tail M hM
  exact ⟨M,hM,N,fun n k hk s hs => (hN n k hk s hs).trans
    (div_le_div_of_nonneg_right hT.le (by linarith))⟩

#print axioms exists_variable_upper_tail
#print axioms exists_vanishing_upper_tail
#print axioms exists_variable_lower_tail
#print axioms exists_vanishing_lower_tail
end Erdos970.RecursiveSieve.Buchstab
