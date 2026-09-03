import Submission.BuchstabDoubleCostContraction

/-! The integer cube cutoff and all unit charges for the slow error profile. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Real Finset WeightedMertens
set_option maxHeartbeats 1600000

noncomputable def slowOuterCutoff (k : ℕ) (D : ℝ) : ℕ :=
  min (nthPrime k) ⌊exp (log D/3)⌋₊

lemma slowOuterCutoff_le_prime (k : ℕ) (D : ℝ) : slowOuterCutoff k D ≤ nthPrime k := min_le_left _ _

lemma slowOuterCutoff_le_exp (k : ℕ) (D : ℝ) :
    (slowOuterCutoff k D : ℝ) ≤ exp (log D/3) :=
  (show (slowOuterCutoff k D : ℝ) ≤ (⌊exp (log D/3)⌋₊ : ℝ) by
    exact_mod_cast (min_le_right (nthPrime k) ⌊exp (log D/3)⌋₊)).trans
    (Nat.floor_le (exp_pos _).le)

lemma slowOuterCutoff_lower (k : ℕ) (D : ℝ)
    (hpkD : (nthPrime k : ℝ) ≤ D) (hV : 12 ≤ log (nthPrime k : ℝ)) :
    exp (log (nthPrime k : ℝ)/4) ≤ (slowOuterCutoff k D : ℝ) := by
  let V := log (nthPrime k : ℝ)
  have hp0 : (0 : ℝ) < nthPrime k := by exact_mod_cast (nthPrime_prime k).pos
  have hVL : V ≤ log D := log_le_log hp0 hpkD
  have hV0 : 0 ≤ V := by dsimp [V]; linarith
  have hquarter : 1 ≤ exp (V/4) := one_le_exp (by positivity)
  have htwice : 2 ≤ exp (V/12) := by
    have hh := add_one_le_exp (V/12)
    dsimp [V] at hh
    linarith
  have hexp : 2*exp (V/4) ≤ exp (log D/3) := by
    have hh := mul_le_mul_of_nonneg_left htwice (exp_pos (V/4)).le
    rw [← exp_add] at hh
    have he : V/4+V/12 = V/3 := by ring
    rw [he] at hh
    exact (show 2*exp (V/4) ≤ exp (V/3) by simpa only [mul_comm] using hh).trans
      (exp_le_exp.mpr (by linarith only [hVL]))
  have hf := Nat.lt_floor_add_one (exp (log D/3))
  have hfloor : exp (V/4) ≤ (⌊exp (log D/3)⌋₊ : ℝ) := by linarith
  unfold slowOuterCutoff
  rw [Nat.cast_min]
  apply le_min _ hfloor
  calc
    exp (V/4) ≤ exp V := exp_le_exp.mpr (by linarith only [hV0])
    _ = (nthPrime k : ℝ) := exp_log hp0

lemma slowOuterCutoff_properties (k : ℕ) (D : ℝ)
    (hpkD : (nthPrime k : ℝ) ≤ D) (hV : 12 ≤ log (nthPrime k : ℝ)) :
    2 ≤ slowOuterCutoff k D ∧
    log (nthPrime k : ℝ)/4 ≤ log (slowOuterCutoff k D : ℝ) ∧
    log (slowOuterCutoff k D : ℝ) ≤ log (nthPrime k : ℝ) ∧
    3*log (slowOuterCutoff k D : ℝ) ≤ log D := by
  have hh := slowOuterCutoff_lower k D hpkD hV
  have he : 2 ≤ exp (log (nthPrime k : ℝ)/4) := by
    have h := add_one_le_exp (log (nthPrime k : ℝ)/4)
    linarith
  have hR : 2 ≤ slowOuterCutoff k D := by exact_mod_cast he.trans hh
  have hR0 : (0 : ℝ) < slowOuterCutoff k D := by exact_mod_cast (show 0 < slowOuterCutoff k D by omega)
  have hl := log_le_log (exp_pos _) hh
  rw [log_exp] at hl
  have hu := log_le_log hR0 (show (slowOuterCutoff k D : ℝ) ≤ (nthPrime k : ℝ) by
    exact_mod_cast slowOuterCutoff_le_prime k D)
  have hcut := log_le_log hR0 (slowOuterCutoff_le_exp k D)
  rw [log_exp] at hcut
  exact ⟨hR,hl,hu,by linarith only [hcut]⟩

lemma kept_child_le_slowOuterCutoff (k : ℕ) (i : Fin k) (D : ℝ)
    (hkeep : primeKeep nthPrime i.val (D*primeMarginal i.val)) :
    nthPrime i.val ≤ slowOuterCutoff k D := by
  have hp0 : (0 : ℝ) < nthPrime i.val := by exact_mod_cast (nthPrime_prime i.val).pos
  have hc : (nthPrime i.val : ℝ)^2 ≤ D/(nthPrime i.val : ℝ) := by
    simpa only [primeKeep,primeMarginal,mul_one_div] using hkeep
  have hc3 : (nthPrime i.val : ℝ)^3 ≤ D := by
    have hh := (le_div_iff₀ hp0).mp hc
    simpa only [pow_succ] using hh
  have hl := log_le_log (pow_pos hp0 3) hc3
  rw [log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have he := exp_le_exp.mpr (show log (nthPrime i.val : ℝ) ≤ log D/3 by linarith only [hl])
  rw [exp_log hp0] at he
  exact le_min (nthPrime_strictMono i.isLt).le (Nat.le_floor he)

/-- The root and every possible retained-child unit use at most 1/50 of the
profile at logarithmic boundary scale at least 100. -/
lemma slow_units_le (k : ℕ) (D : ℝ) (hpkD : (nthPrime k : ℝ) ≤ D)
    (hV : 100 ≤ log (nthPrime k : ℝ)) :
    1+(slowOuterCutoff k D : ℝ) ≤ (1/50 : ℝ)*slowLevelShape k D := by
  let V := log (nthPrime k : ℝ)
  let L := log D
  have hp0 : (0 : ℝ) < nthPrime k := by exact_mod_cast (nthPrime_prime k).pos
  have hD0 : 0 < D := hp0.trans_le hpkD
  have hVL : V ≤ L := log_le_log hp0 hpkD
  have hV0 : 0 < V := by dsimp [V]; linarith
  have hL0 : 0 ≤ L := by linarith
  have hsmall : (2/3 : ℝ)/V ≤ 1/6 := (div_le_iff₀ hV0).mpr (by dsimp [V]; linarith)
  have hpoly := pow_div_factorial_le_exp (V/2) (by positivity) 3
  norm_num only [Nat.factorial,Nat.reduceMul,Nat.cast_ofNat] at hpoly
  have hv : 100 ≤ V := hV
  have hsq : 4800 ≤ V^2 := by nlinarith only [sq_nonneg (V-100),hv]
  have hcub := mul_le_mul_of_nonneg_right hsq hV0.le
  have hbig : 100*V ≤ exp (V/2) := by nlinarith only [hpoly,hcub]
  have hbigL : 100*V ≤ exp (L/2) := hbig.trans (exp_le_exp.mpr (by linarith only [hVL]))
  have hfactor := mul_le_mul_of_nonneg_right hbigL (exp_pos (L/3)).le
  rw [← exp_add] at hfactor
  have hsum : L/2+L/3 = 5*L/6 := by ring
  rw [hsum] at hfactor
  have hshape : exp (5*L/6)/V ≤ slowLevelShape k D := by
    unfold slowLevelShape
    rw [show D=exp L by exact (exp_log hD0).symm,log_exp,← exp_add]
    apply div_le_div_of_nonneg_right _ hV0.le
    apply exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right hsmall hL0
    change 5*L/6 ≤ L+(-2/3 : ℝ)*L/V
    have he : ((2/3 : ℝ)/V)*L = (2/3 : ℝ)*L/V := by ring
    rw [he] at hm
    have he' : L+(-2/3 : ℝ)*L/V=L-(2/3 : ℝ)*L/V := by ring
    rw [he']
    linarith only [hm]
  have htwice : 2*exp (L/3) ≤ (1/50 : ℝ)*slowLevelShape k D := by
    have hh : 100*exp (L/3) ≤ exp (5*L/6)/V :=
      (le_div_iff₀ hV0).mpr (by nlinarith only [hfactor])
    linarith only [hh,hshape]
  have hone : 1 ≤ exp (L/3) := one_le_exp (by positivity)
  have hcut := slowOuterCutoff_le_exp k D
  change (slowOuterCutoff k D : ℝ) ≤ exp (L/3) at hcut
  linarith only [hone,hcut,htwice]

#print axioms slowOuterCutoff_properties
#print axioms slow_units_le
end Erdos970.RecursiveSieve.Buchstab
