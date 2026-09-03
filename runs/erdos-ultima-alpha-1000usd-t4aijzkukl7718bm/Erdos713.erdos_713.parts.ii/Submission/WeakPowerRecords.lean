import FormalConjecturesUtil
import Submission.CompactCloneAudit

/-! Two-sided power records require only one diverging lower-exponent ratio
and one vanishing higher-exponent ratio. They do not require a leading constant. -/
open Filter Asymptotics Finset
open scoped Topology
namespace Erdos713FutureRecords

lemma past_record_of_limit {f : ℕ → ℝ} {r : ℝ}
    (hlim : Tendsto (fun n : ℕ => f n/(n : ℝ)^r) atTop atTop) (N : ℕ) :
    ∃ n, N ≤ n ∧ 0 < n ∧ 0 < f n ∧
      ∀ j, j ≤ n → f j/(j : ℝ)^r ≤ f n/(n : ℝ)^r := by
  let g : ℕ → ℝ := fun n => f n/(n : ℝ)^r
  obtain ⟨j,hj,hsmall⟩ := (range (N+1)).exists_max_image g ⟨0,by simp⟩
  obtain ⟨p,hp⟩ := (hlim.eventually_gt_atTop (max (g j) 0)).exists
  obtain ⟨n,hn,hmax⟩ := (range (p+1)).exists_max_image g ⟨p,by simp⟩
  have hnlarge : max (g j) 0 < g n := hp.trans_le (hmax p (by simp))
  have hN : N < n := by
    by_contra hNn
    have hh := hsmall n (mem_range.mpr (by omega))
    exact (not_lt_of_ge hh) ((le_max_left _ _).trans_lt hnlarge)
  have hnp : 0 < n := by omega
  have hpos : 0 < f n :=
    (div_pos_iff_of_pos_right (Real.rpow_pos_of_pos (by exact_mod_cast hnp) r)).mp
      ((le_max_right _ _).trans_lt hnlarge)
  refine ⟨n,hN.le,hnp,hpos,?_⟩
  intro k hk
  exact hmax k (mem_range.mpr (by have := mem_range.mp hn; omega))

lemma two_sided_record_of_limits {f : ℕ → ℝ} {r s : ℝ} (hrs : r < s)
    (hlo : Tendsto (fun n : ℕ => f n/(n : ℝ)^r) atTop atTop)
    (hhi : Tendsto (fun n : ℕ => f n/(n : ℝ)^s) atTop (𝓝 0)) (N : ℕ) :
    ∃ n, N ≤ n ∧ 0 < n ∧ 0 < f n ∧
      (∀ j, 0 < j → j ≤ n → f j/(j : ℝ)^r ≤ f n/(n : ℝ)^r) ∧
      (∀ j, n ≤ j → f j/(j : ℝ)^s ≤ f n/(n : ℝ)^s) := by
  obtain ⟨m,hm,hmp,hmf,hpast⟩ := past_record_of_limit hlo N
  obtain ⟨n,hmn,hnpos,htail⟩ := exists_tail_max hhi m
    (div_pos hmf (Real.rpow_pos_of_pos (by exact_mod_cast hmp) s))
  have hnp : 0 < n := hmp.trans_le hmn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnp
  have hnf : 0 < f n := (div_pos_iff_of_pos_right (Real.rpow_pos_of_pos hnreal s)).mp hnpos
  have htransfer {j : ℕ} (hjp : 0 < j) (hjn : j ≤ n)
      (hj : f j/(j : ℝ)^s ≤ f n/(n : ℝ)^s) :
      f j/(j : ℝ)^r ≤ f n/(n : ℝ)^r := by
    rw [change_ratio f r s hjp,change_ratio f r s hnp]
    exact mul_le_mul hj
      (Real.rpow_le_rpow (Nat.cast_nonneg j) (by exact_mod_cast hjn) (by linarith))
      (Real.rpow_nonneg (Nat.cast_nonneg j) (s-r)) hnpos.le
  refine ⟨n,hm.trans hmn,hnp,hnf,?_,fun j hj => htail j (hmn.trans hj)⟩
  intro j hjp hjn
  by_cases hjm : j ≤ m
  · exact (hpast j hjm).trans (htransfer hmp hmn (htail m le_rfl))
  · exact htransfer hjp hjn (htail j (by omega))

lemma small_increment_with_past_of_limits {f : ℕ → ℝ} {a r s : ℝ}
    (har : a < r) (hr : 1 ≤ r) (hrs : r < s)
    (hlo : Tendsto (fun n : ℕ => f n/(n : ℝ)^a) atTop atTop)
    (hhi : Tendsto (fun n : ℕ => f n/(n : ℝ)^r) atTop (𝓝 0)) (N : ℕ) :
    ∃ n, N ≤ n ∧ 0 < n ∧ 0 < f n ∧
      (∀ j, 0 < j → j ≤ n → f j/(j : ℝ)^a ≤ f n/(n : ℝ)^a) ∧
      (n : ℝ)*(f (n+1)-f n) ≤ s*f n := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp (eventual_increment_upper hr hrs)
  obtain ⟨n,hn,hnp,hnf,hpast,hfuture⟩ := two_sided_record_of_limits har hlo hhi (max N M)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnp
  refine ⟨n,by omega,hnp,hnf,hpast,?_⟩
  let C : ℝ := f n/(n : ℝ)^r
  have hC : 0 < C := div_pos hnf (Real.rpow_pos_of_pos hnr r)
  have he : C*(n : ℝ)^r = f n := div_mul_cancel₀ _ (Real.rpow_pos_of_pos hnr r).ne'
  have hstep : f (n+1) ≤ C*((n : ℝ)+1)^r := by
    have hh := hfuture (n+1) (by omega)
    simp only [Nat.cast_add,Nat.cast_one] at hh
    rw [div_le_iff₀ (Real.rpow_pos_of_pos (show (0 : ℝ) < n+1 by positivity) r)] at hh
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  have hu := hM n (by omega)
  have hpow : (n : ℝ)*(n : ℝ)^(r-1) = (n : ℝ)^r := by
    rw [Real.rpow_sub hnr,Real.rpow_one]
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hu (show 0 ≤ (n : ℝ)*C by positivity)
  have hmul2 := mul_le_mul_of_nonneg_left hstep hnr.le
  have hex : (n : ℝ)*C*((n : ℝ)^r) = (n : ℝ)*f n := by rw [mul_assoc,he]
  have hex2 : (n : ℝ)*C*(s*(n : ℝ)^(r-1)) = s*f n := by
    calc
      _ = s*C*((n : ℝ)*(n : ℝ)^(r-1)) := by ring
      _ = s*f n := by rw [hpow,mul_assoc,he]
  rw [hex2] at hmul
  nlinarith

#print axioms past_record_of_limit
#print axioms two_sided_record_of_limits
#print axioms small_increment_with_past_of_limits
end Erdos713FutureRecords
