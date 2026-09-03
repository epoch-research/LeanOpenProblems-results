import Submission.LogPrimeSums

/-!
Density of ratios of arbitrarily large primes. This is used only as a topological
prime-pair construction; it does not establish the prescribed-slope conjecture.
-/
namespace Erdos972PrimeRatioDensity

open Finset Filter Complex
open Erdos972LogPrimeBlocks Erdos972PrimeRatioKernel Erdos972KernelPoleLower Erdos972LogPrimeSums

/-- Every real log-ratio interval is attained by arbitrarily large primes in both
coordinates. -/
theorem exists_primes_log_ratio_close (c δ : ℝ) (hδ : 0 < δ) (B : ℕ) :
    ∃ p q : ℕ, B < p ∧ B < q ∧ p.Prime ∧ q.Prime ∧
      |Real.log q - Real.log p - c| < δ := by
  classical
  by_contra hn
  have havoid : ∀ p q : ℕ, B < p → B < q → p.Prime → q.Prime →
      δ ≤ |Real.log q - Real.log p - c| := by
    intro p q hpB hqB hp hq
    exact le_of_not_gt (fun h => hn ⟨p, q, hpB, hqB, hp, hq, h⟩)
  let R := rowConstant δ
  have hR : 0 ≤ R := rowConstant_nonneg δ
  obtain ⟨T, hT⟩ := exists_nat_gt (8192 * R + 1)
  have hTpos : (0 : ℝ) < T := by linarith
  have hT1 : 1 ≤ T := by exact_mod_cast (show (1 : ℝ) ≤ T by linarith)
  obtain ⟨C, hC, hpole⟩ := eventually_window_pole_bound B T hTpos.le
  let η : ℝ := 1 / (8 * Real.pi * (|c| + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hphase : 2 * Real.pi * η * |c| ≤ 1 / 2 := by
    have he : 2 * Real.pi * η * |c| = |c| / (4 * (|c| + 1)) := by
      dsimp [η]
      field_simp; ring
    rw [he]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith [abs_nonneg c]
  let F : ℝ := C + 1 / (2 * Real.pi * η)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hlarge : ∀ᶠ u : ℕ in atTop,
      8 * C ≤ (u : ℝ) ∧ 1 / (4 * η) ≤ (u : ℝ) ∧ |c| ≤ (u : ℝ) ∧
        2048 * T * F ^ 2 < (u : ℝ) := by
    exact (tendsto_natCast_atTop_atTop : Tendsto (fun u : ℕ => (u : ℝ)) atTop atTop).eventually
      (show ∀ᶠ y : ℝ in atTop, 8 * C ≤ y ∧ 1 / (4 * η) ≤ y ∧ |c| ≤ y ∧
        2048 * T * F ^ 2 < y from
        (eventually_ge_atTop _).and ((eventually_ge_atTop _).and
          ((eventually_ge_atTop _).and (eventually_gt_atTop _))))
  obtain ⟨u, hu1, hpole, hCu, hηu, hcu, huF⟩ :=
    ((eventually_ge_atTop (1 : ℕ)).and (hpole.and hlarge)).exists
  have hu : 0 < u := by omega
  have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have huR1 : (1 : ℝ) ≤ u := by exact_mod_cast hu1
  have hsmall : 1 / (4 * (u : ℝ)) ≤ η := by
    have hh := (div_le_iff₀ (show 0 < 4 * η by positivity)).mp hηu
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  let S := primeWindow B (u ^ 2)
  let w := primeWeight (1 / (u : ℝ))
  let x : ℕ → ℝ := fun p => Real.log p
  let D : ℝ := 4 * (u : ℝ) ^ 2
  let H : ℕ := T * (4 * u ^ 2)
  have hD : 0 < D := by dsimp [D]; positivity
  have hH : (H : ℝ) = 4 * (T : ℝ) * (u : ℝ) ^ 2 := by dsimp [H]; push_cast; ring
  have hHlarge : 2 * u ≤ H := by
    have hh := Nat.mul_le_mul_right (4 * u ^ 2) hT1
    dsimp [H]
    nlinarith
  have huH : u ≤ H := by omega
  have hHdiff : (H : ℝ) / 2 ≤ ((H - u : ℕ) : ℝ) := by
    rw [Nat.cast_sub huH]
    have hh : 2 * (u : ℝ) ≤ H := by exact_mod_cast hHlarge
    linarith
  have hratio : (H : ℝ) / D = T := by rw [hH]; dsimp [D]; field_simp
  have hpole' (t : ℝ) (ht : |t| ≤ (H : ℝ) / D) :
      ‖weightedExpSum S w x t - pole (1 / u) t‖ ≤ C := by
    apply hpole t
    rwa [hratio] at ht
  have hlower := pairEnergy_lower_of_pole S w x c C η H u hu hC.le hCu hη hphase hsmall hpole'
  change ((H - u : ℕ) : ℝ) * u * ((u : ℝ) ^ 2 / 128) - (H : ℝ) ^ 2 * F ^ 2 ≤
    pairEnergy S w x c D H at hlower
  have hmass : (∑ p ∈ S, w p) ≤ 2 * u :=
    mass_le_of_pole_zero S w x huR (by linarith)
      (hpole 0 (by simp))
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime := (mem_primeWindow hp).2.1
  have hcoord (p : ℕ) (hp : p ∈ S) : 0 ≤ Real.log p ∧ Real.log p ≤ (u : ℝ) ^ 2 := by
    have hh := (mem_primeWindow hp).2.2
    simpa only [Nat.cast_pow] using hh
  have hsmallcoord (p : ℕ) (hp : p ∈ S) (q : ℕ) (hq : q ∈ S) :
      |Real.log q - Real.log p - c| ≤ D / 2 := by
    have hp' := hcoord p hp
    have hq' := hcoord q hq
    have hc' : |c| ≤ (u : ℝ) ^ 2 := by nlinarith
    dsimp [D]
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp hc').1, (abs_le.mp hc').2]
  have hgap (p : ℕ) (hp : p ∈ S) (q : ℕ) (hq : q ∈ S) :
      δ ≤ |Real.log q - Real.log p - c| :=
    havoid p q (mem_primeWindow hp).1 (mem_primeWindow hq).1 (hS p hp) (hS q hq)
  have hupper := pairEnergy_upper_of_avoids (show 0 ≤ 1 / (u : ℝ) by positivity)
    hD hδ S H hS hsmallcoord hgap
  change pairEnergy S w x c D H ≤ D ^ 2 * R * (∑ p ∈ S, w p) at hupper
  have hup : pairEnergy S w x c D H ≤ (32 * R * u) * (u : ℝ) ^ 4 := by
    apply hupper.trans
    calc
      _ ≤ D ^ 2 * R * (2 * u) := mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = _ := by dsimp [D]; ring
  have hlo : ((T : ℝ) * u / 64 - 16 * (T : ℝ) ^ 2 * F ^ 2) * (u : ℝ) ^ 4 ≤
      pairEnergy S w x c D H := by
    apply le_trans _ hlower
    calc
      _ = ((H : ℝ) / 2) * u * ((u : ℝ) ^ 2 / 128) - (H : ℝ) ^ 2 * F ^ 2 := by rw [hH]; ring
      _ ≤ _ := sub_le_sub_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hHdiff (Nat.cast_nonneg u))
          (by positivity)) _
  have hcoef := (mul_le_mul_iff_left₀ (pow_pos huR 4)).mp (hlo.trans hup)
  have hRu : 32 * R * (u : ℝ) ≤ (T : ℝ) * u / 128 := by
    have hm := mul_le_mul_of_nonneg_right (show 4096 * R ≤ (T : ℝ) by linarith) huR.le
    linarith
  have hFu : 16 * (T : ℝ) ^ 2 * F ^ 2 < (T : ℝ) * u / 128 := by
    have hm := mul_lt_mul_of_pos_left huF hTpos
    nlinarith
  linarith

/-- Prime ratios meet every positive interval, with both primes above any
prescribed threshold. -/
theorem exists_primes_ratio_mem {a b : ℝ} (ha : 0 < a) (hab : a < b) (B : ℕ) :
    ∃ p q : ℕ, B < p ∧ B < q ∧ p.Prime ∧ q.Prime ∧
      a < (q : ℝ) / p ∧ (q : ℝ) / p < b := by
  have hb : 0 < b := ha.trans hab
  have hlog : Real.log a < Real.log b := Real.log_lt_log ha hab
  obtain ⟨p, q, hpB, hqB, hp, hq, hclose⟩ := exists_primes_log_ratio_close
    ((Real.log a + Real.log b) / 2) ((Real.log b - Real.log a) / 2) (by linarith) B
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hclose
  have hleft : Real.log a < Real.log q - Real.log p := by linarith
  have hright : Real.log q - Real.log p < Real.log b := by linarith
  have hl := Real.exp_lt_exp.mpr hleft
  have hr := Real.exp_lt_exp.mpr hright
  rw [Real.exp_log ha, Real.exp_sub, Real.exp_log (Nat.cast_pos.mpr hq.pos),
    Real.exp_log (Nat.cast_pos.mpr hp.pos)] at hl
  rw [Real.exp_log hb, Real.exp_sub, Real.exp_log (Nat.cast_pos.mpr hq.pos),
    Real.exp_log (Nat.cast_pos.mpr hp.pos)] at hr
  exact ⟨p, q, hpB, hqB, hp, hq, hl, hr⟩

#print axioms exists_primes_ratio_mem
#print axioms exists_primes_log_ratio_close

end Erdos972PrimeRatioDensity
