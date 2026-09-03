import Submission.PrefixEnergyIdentity

/-! Comparable multiplier denominators compare the actual shorter ordinary
prefix means. The explicit rounding error is retained. -/
namespace Erdos371.FiniteInformation
open Finset
set_option autoImplicit false

lemma prefixMean_quotient_comparable (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (N p q : ℕ) (hp : 0 < p) (hpq : p ≤ q)
    (δ : ℝ) (hδ : 0 ≤ δ) (hclose : (1-δ)*(q : ℝ) ≤ p) :
    |prefixMean (N/p) f-prefixMean (N/q) f| ≤ 2*δ+2*q/N := by
  by_cases hN0 : N=0
  · subst N
    simp only [Nat.zero_div,sub_self,abs_zero,Nat.cast_zero,div_zero,add_zero]
    positivity
  have hN : 0 < N := Nat.pos_of_ne_zero hN0
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hpr : 0 < (p : ℝ) := by exact_mod_cast hp
  have hq : 0 < q := hp.trans_le hpq
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
  by_cases hqN : q ≤ N
  · let U := N/p
    let M := N/q
    have hM : 0 < M := Nat.div_pos hqN hq
    have hU : 0 < U := Nat.div_pos (hpq.trans hqN) hp
    have hMU : M ≤ U := Nat.div_le_div_left hpq hp
    have hUr : 0 < (U : ℝ) := by exact_mod_cast hU
    have hMr : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
    have hUp : (p : ℝ)*U ≤ N := by exact_mod_cast Nat.mul_div_le N p
    have hMq : (N : ℝ) ≤ q*(M+1) := by
      exact_mod_cast (Nat.lt_mul_div_succ N hq).le
    have hlow : (N : ℝ)/q-1 ≤ M := by
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hqr).mpr
      nlinarith
    have hlow0 : 0 ≤ (N : ℝ)/q-1 := by
      apply sub_nonneg.mpr
      apply (one_le_div hqr).mpr
      exact_mod_cast hqN
    have hUup : (U : ℝ) ≤ (N : ℝ)/p := (le_div_iff₀ hpr).mpr (by nlinarith)
    have hfrac : ((N : ℝ)/q-1)/((N : ℝ)/p) ≤ (M : ℝ)/U := by
      exact (div_le_div_of_nonneg_left hlow0 hUr hUup).trans
        (div_le_div_of_nonneg_right hlow hUr.le)
    have he : ((N : ℝ)/q-1)/((N : ℝ)/p) = (p : ℝ)/q-(p : ℝ)/N := by
      field_simp
    rw [he] at hfrac
    have hcp : 1-δ ≤ (p : ℝ)/q := (le_div_iff₀ hqr).mpr hclose
    have hpdiv : (p : ℝ)/N ≤ q/N := div_le_div_of_nonneg_right (by exact_mod_cast hpq) hNr.le
    have hrem : (U-M : ℕ)/(U : ℝ) ≤ δ+q/N := by
      rw [Nat.cast_sub hMU,sub_div,div_self hUr.ne']
      linarith
    have hb := prefixMean_endpoint_bound M U hM hMU f 1 (fun n _ => hf n)
    simp only [mul_one] at hb
    change |prefixMean U f-prefixMean M f| ≤ _
    calc
      _ ≤ 2*(U-M : ℕ)/(U : ℝ) := hb
      _ ≤ 2*(δ+q/N) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hrem (by norm_num)
      _ = _ := by ring
  · have hz : N/q=0 := Nat.div_eq_of_lt (by omega)
    rw [hz,show prefixMean 0 f=0 by simp [prefixMean],sub_zero]
    have hqN' : (N : ℝ) ≤ q := by exact_mod_cast (show N ≤ q by omega)
    have hr : 1 ≤ (q : ℝ)/N := (one_le_div hNr).mpr hqN'
    apply (prefixMean_unit_bound f hf (N/p)).trans
    rw [mul_div_assoc]
    linarith

#print axioms prefixMean_quotient_comparable
end Erdos371.FiniteInformation
