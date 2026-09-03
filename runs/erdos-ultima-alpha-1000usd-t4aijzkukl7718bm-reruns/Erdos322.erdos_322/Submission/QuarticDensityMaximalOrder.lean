import Submission.DivisorMaximalOrder
import Submission.QuarticFiberUpper

/-! An explicit divisor-scale upper bound for quartic congruence certificates.
This is not an upper bound for the exact representation count. -/
namespace Erdos322Research.QuarticDensityMaximalOrder
noncomputable section
open Finset Filter DivisorMaximalOrder QuarticFiberBasic QuarticFiberUpper
open scoped Classical Topology
set_option maxHeartbeats 0
set_option Elab.async false

/-- Uniform in every residue and every modulus up to N. -/
theorem all_fibers_divisor_scale_up_to (N q n : ℕ)
    (hN : 65536 ≤ N) (hq : 0 < q) (hqN : q ≤ N) :
    (fiberCount q n : ℝ) ≤
      Real.exp (128*Real.log (N : ℝ)/Real.log (Real.log (N : ℝ)))*(q : ℝ)^3 := by
  have hc : (fiberCount q n : ℝ) ≤ (q.divisors.card : ℝ)^8*(q : ℝ)^3 := by
    exact_mod_cast all_fibers_upper q hq n
  have hd := divisor_count_upper_up_to N q hN hq hqN
  calc
    (fiberCount q n : ℝ) ≤ (q.divisors.card : ℝ)^8*(q : ℝ)^3 := hc
    _ ≤ (Real.exp (16*Real.log (N : ℝ)/Real.log (Real.log (N : ℝ))))^8*(q : ℝ)^3 := by gcongr
    _ = _ := by rw [← Real.exp_nat_mul]; congr 2; ring

/-- The same estimate directly bounds the normalized congruence density. -/
theorem normalized_fiber_upper (N q n : ℕ)
    (hN : 65536 ≤ N) (hq : 0 < q) (hqN : q ≤ N) :
    (fiberCount q n : ℝ)/(q : ℝ)^3 ≤
      Real.exp (128*Real.log (N : ℝ)/Real.log (Real.log (N : ℝ))) := by
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < (q : ℝ)^3)).mpr
    (all_fibers_divisor_scale_up_to N q n hN hq hqN)

/-- A concrete sufficient logarithmic threshold for the density to be at
most N^epsilon. The quantifiers include ALL moduli q<=N and ALL residues. -/
theorem normalized_fiber_le_power (N q n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hN : 65536 ≤ N) (hq : 0 < q) (hqN : q ≤ N)
    (hlog : 128/ε ≤ Real.log (Real.log (N : ℝ))) :
    (fiberCount q n : ℝ)/(q : ℝ)^3 ≤ (N : ℝ)^ε := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hLp : 0 < Real.log (Real.log (N : ℝ)) := (div_pos (by norm_num) hε).trans_le hlog
  have hmul : 128 ≤ ε*Real.log (Real.log (N : ℝ)) := by
    have hh := (div_le_iff₀ hε).mp hlog
    nlinarith
  have he : 128*Real.log (N : ℝ)/Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ)*ε := by
    apply (div_le_iff₀ hLp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmul (Real.log_nonneg hN1)]
  calc
    (fiberCount q n : ℝ)/(q : ℝ)^3 ≤ _ := normalized_fiber_upper N q n hN hq hqN
    _ ≤ Real.exp (Real.log (N : ℝ)*ε) := Real.exp_le_exp.mpr he
    _ = (N : ℝ)^ε := (Real.rpow_def_of_pos hNp ε).symm

/-- Therefore every modulus-and-residue certificate is eventually below each
fixed positive power of a target-size bound N. -/
theorem all_normalized_fibers_eventually_le_power (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, 0 < q → q ≤ N → ∀ n : ℕ,
      (fiberCount q n : ℝ)/(q : ℝ)^3 ≤ (N : ℝ)^ε := by
  have ht : Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_ge_atTop 65536, ht.eventually_ge_atTop (128/ε)] with N hN hlog
  intro q hq hqN n
  exact normalized_fiber_le_power N q n ε hε hN hq hqN hlog

lemma fiber_count_le_box (q n : ℕ) : fiberCount q n ≤ q^4 := by
  have hh := Fintype.card_subtype_le (fun x : Fin 4 → Fin q ↦ (∑ i, (x i : ℕ)^4) ≡ n [MOD q])
  simpa only [fiberCount,Fiber,Fintype.card_fun,Fintype.card_fin] using hh

/-- Exponential normalized density forces a modulus of at least r^(c*r)
size. Thus the r*log(r) height cost cannot be removed by optimizing this
full-box congruence certificate. This is NOT a bound on an exact count. -/
theorem exponential_density_height_barrier (r q n : ℕ) (hr : 16 ≤ r) (hq : 0 < q)
    (hlarge : (2 : ℝ)^r < (fiberCount q n : ℝ)/(q : ℝ)^3) :
    (r : ℝ)^((r : ℝ)/512) < q := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hrp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hgrid : (fiberCount q n : ℝ)/(q : ℝ)^3 ≤ q := by
    apply (div_le_iff₀ (pow_pos hqp _)).mpr
    have hh : (fiberCount q n : ℝ) ≤ (q : ℝ)^4 := by exact_mod_cast fiber_count_le_box q n
    convert hh using 1; ring
  have hqr : (2 : ℝ)^r < q := hlarge.trans_le hgrid
  have hqrNat : 2^r < q := by exact_mod_cast hqr
  have hqbig : 65536 ≤ q := by
    have hh : 2^16 ≤ 2^r := Nat.pow_le_pow_right (by decide) hr
    norm_num at hh
    omega
  have htwo : 1/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have htwoUp : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have htwoPos : 0 < Real.log 2 := by linarith
  have hrlog : 2 ≤ Real.log (r : ℝ) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 16)
      (by exact_mod_cast hr : (16 : ℝ) ≤ r)
    have he : Real.log 16=4*Real.log 2 := by rw [show (16 : ℝ)=2^4 by norm_num,Real.log_pow]; norm_num
    rw [he] at hh
    linarith
  have hlogqr : (r : ℝ)*Real.log 2 ≤ Real.log (q : ℝ) := by
    have hh := Real.log_lt_log (by positivity : (0 : ℝ) < (2 : ℝ)^r) hqr
    simpa only [Real.log_pow] using hh.le
  have hloglog2 : -1 ≤ Real.log (Real.log 2) := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 1/2) htwo
    have he : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
    rw [he] at hh
    linarith
  have hLL : Real.log (r : ℝ)/2 ≤ Real.log (Real.log (q : ℝ)) := by
    have hh := Real.log_le_log (mul_pos hrp htwoPos) hlogqr
    rw [Real.log_mul hrp.ne' htwoPos.ne'] at hh
    linarith
  have hLLp : 0 < Real.log (Real.log (q : ℝ)) := by linarith
  have hupper := normalized_fiber_upper q q n hqbig hq le_rfl
  have hlogupper := Real.log_lt_log (by positivity : (0 : ℝ) < (2 : ℝ)^r) (hlarge.trans_le hupper)
  rw [Real.log_pow,Real.log_exp] at hlogupper
  have hstrict := (lt_div_iff₀ hLLp).mp hlogupper
  have hproduct : ((r : ℝ)/2)*(Real.log (r : ℝ)/2) ≤
      ((r : ℝ)*Real.log 2)*Real.log (Real.log (q : ℝ)) := by
    exact mul_le_mul (by nlinarith : (r : ℝ)/2 ≤ (r : ℝ)*Real.log 2) hLL
      (by linarith) (by positivity)
  have hfinal : Real.log (r : ℝ)*((r : ℝ)/512) < Real.log (q : ℝ) := by nlinarith
  rw [Real.rpow_def_of_pos hrp]
  exact (Real.exp_lt_exp.mpr hfinal).trans_eq (Real.exp_log hqp)

/-- The same lower height cost applies to a positive exact target divisible
by the certifying modulus. It bounds only what that certificate can supply. -/
theorem exponential_certificate_target_barrier (r q N : ℕ)
    (hr : 16 ≤ r) (hq : 0 < q) (hN : 0 < N) (hd : q ∣ N)
    (hlarge : (2 : ℝ)^r < (fiberCount q 0 : ℝ)/(q : ℝ)^3) :
    (r : ℝ)^((r : ℝ)/512) < N :=
  (exponential_density_height_barrier r q 0 hr hq hlarge).trans_le
    (by exact_mod_cast Nat.le_of_dvd hN hd)

end
end Erdos322Research.QuarticDensityMaximalOrder
