import Submission.FixedMaxMultiplicativeSymmetry
import Submission.PrimeLogQuantization

/-! The fixed-function approximation is not uniform in its forbidden set.
Also, fixing the scale parameter in the actual prime-log labels gives a
single top label on a density-one set, not the moving-scale distribution. -/
namespace Erdos371.FixedPrimeAvoidance
open Finset Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

lemma tail_avoidance_mean_zero (K : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, avoid {p | K < p} n)/N) atTop (𝓝 0) := by
  have ht := (density_iff_count (fun n => Nat.maxPrimeFac n ≤ K+1) 0).mp
    (bounded_maxPrimeFac_hasDensity_zero (K+1))
  apply squeeze_zero (fun N => div_nonneg (sum_nonneg fun n _ => (avoid_bounds _ n).1) (Nat.cast_nonneg N)) _ ht
  intro N
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  rw [← sum_boole]
  apply sum_le_sum
  intro n _
  by_cases hn : Nat.maxPrimeFac n ≤ K+1
  · rw [if_pos hn]
    exact (avoid_bounds _ n).2
  · rw [if_neg hn]
    have hn1 : 1 < n := lt_of_lt_of_le (by omega : 1 < Nat.maxPrimeFac n) Nat.maxPrimeFac_le
    have hnot : ¬∀ p, p.Prime → p ∈ {p | K < p} → ¬p ∣ n := by
      intro h
      exact h (Nat.maxPrimeFac n) (Nat.prime_maxPrimeFac_of_one_lt n hn1) (by simp; omega) Nat.maxPrimeFac_dvd
    simp only [avoid,if_neg hnot,le_refl]

lemma tail_primeCut_empty (K : ℕ) : primeCut {p | K < p} K = ∅ := by
  ext p
  simp only [primeCut,mem_filter,mem_range,Set.mem_setOf_eq,Finset.notMem_empty,iff_false]
  omega

/-- For each proposed universal truncation K, a fixed forbidden set can make
the truncation error tend to one. This does not disprove uniform SKEW decay. -/
theorem finite_prime_truncation_error_can_tend_to_one (K : ℕ) :
    ∃ B : Set ℕ, Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, |avoid B n-finiteAvoid (primeCut B K) n|)/N) atTop (𝓝 1) := by
  refine ⟨{p | K < p},?_⟩
  have ht := (tail_avoidance_mean_zero K).const_sub 1
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [tail_primeCut_empty]
  simp only [finiteAvoid,Finset.notMem_empty,false_implies,implies_true,if_true]
  have he (n : ℕ) : |avoid {p | K < p} n-1| = 1-avoid {p | K < p} n := by
    rw [abs_of_nonpos (sub_nonpos.mpr (avoid_bounds _ n).2)]
    ring
  simp_rw [he,sum_sub_distrib,sum_const,card_range,nsmul_eq_mul,mul_one,sub_div,div_self hNr]

/-- The finite-prime approximation cannot be made uniform over forbidden
sets, even when their prime cut at the proposed truncation is empty. -/
theorem no_uniform_finite_prime_approximation :
    ¬∃ K, ∀ B : Set ℕ, ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ range N, |avoid B n-finiteAvoid (primeCut B K) n|)/N < (1/2 : ℝ) := by
  rintro ⟨K,hK⟩
  obtain ⟨B,hB⟩ := finite_prime_truncation_error_can_tend_to_one K
  have hl := hB.eventually (lt_mem_nhds (by norm_num : (1/2 : ℝ) < 1))
  obtain ⟨N,hN,hN'⟩ := ((hK B).and hl).exists
  exact hN.not_gt hN'

lemma unitQuantize_eq_top (Q : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    unitQuantize Q x = ⟨Q,Nat.lt_succ_self Q⟩ := by
  have hf : Q ≤ ⌊(Q : ℝ)*x⌋₊ := by
    have hh := Nat.floor_mono (le_mul_of_one_le_right (Nat.cast_nonneg Q : (0 : ℝ) ≤ Q) hx)
    simpa only [Nat.floor_natCast] using hh
  exact Fin.ext (min_eq_left hf)

lemma primeQuantLabel_eq_top_of_large (Q X n : ℕ) (hX : 1 < X)
    (hn : X ≤ Nat.maxPrimeFac n) : primeQuantLabel Q X n = ⟨Q,Nat.lt_succ_self Q⟩ := by
  apply unitQuantize_eq_top
  unfold normalizedPrimeLog primeLog
  have hlog : 0 < Real.log X := Real.log_pos (by exact_mod_cast hX)
  apply (one_le_div hlog).mpr
  exact Real.log_le_log (by exact_mod_cast (show 0 < X by omega)) (by exact_mod_cast hn)

/-- Freezing the scale parameter X makes all finite labels collapse to the
top label in natural density. This is distinct from the diagonal X=N. -/
theorem fixed_primeQuantLabel_top_density (Q X : ℕ) (hX : 1 < X) :
    {n | primeQuantLabel Q X n = ⟨Q,Nat.lt_succ_self Q⟩}.HasDensity 1 := by
  apply (density_iff_of_exception
    (fun n => primeQuantLabel Q X n = ⟨Q,Nat.lt_succ_self Q⟩) (fun _ => True)
    (fun n => Nat.maxPrimeFac n ≤ X) ?_ (bounded_maxPrimeFac_hasDensity_zero X) 1).mpr
  · rw [density_iff_count]
    have he : (fun N : ℕ => (((range N).filter (fun _ => True)).card : ℝ)/N) =ᶠ[atTop] fun _ => (1 : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
      simp [show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne']
    exact tendsto_const_nhds.congr' he.symm
  · intro n hn
    simp only [iff_true]
    exact primeQuantLabel_eq_top_of_large Q X n hX (by omega)

#print axioms no_uniform_finite_prime_approximation
#print axioms fixed_primeQuantLabel_top_density
end Erdos371.FixedPrimeAvoidance
