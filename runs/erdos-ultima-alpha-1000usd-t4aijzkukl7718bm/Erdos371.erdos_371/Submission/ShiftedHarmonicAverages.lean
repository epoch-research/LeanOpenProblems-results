import Submission.DecreasingPrefixMixture
import Submission.HarmonicEmpiricalMeasure

/-! Harmonic averages on arbitrary positive intervals. All errors are uniform
in the lower endpoint and depend on the interval's total harmonic mass. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false

noncomputable def positiveRawSum (T : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 T, F n/(n : ℝ)

noncomputable def shiftedHarmonicRaw (A N : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ n ∈ range (N+1), F (A+n+1)/(A+n+1 : ℝ)

noncomputable def shiftedHarmonicMass (A N : ℕ) : ℝ := shiftedHarmonicRaw A N (fun _ => 1)
noncomputable def shiftedHarmonicMean (A N : ℕ) (F : ℕ → ℝ) : ℝ :=
  shiftedHarmonicRaw A N F/shiftedHarmonicMass A N

lemma shiftedHarmonicRaw_eq_sub (A N : ℕ) (F : ℕ → ℝ) :
    shiftedHarmonicRaw A N F = positiveRawSum (A+N+1) F-positiveRawSum A F := by
  unfold positiveRawSum
  simp only [sum_Icc_one_eq_sum_range,Nat.cast_add,Nat.cast_one]
  rw [show A+N+1=A+(N+1) by omega,sum_range_add]
  simp only [Nat.cast_add]
  unfold shiftedHarmonicRaw
  ring

lemma shiftedHarmonicMass_pos (A N : ℕ) : 0 < shiftedHarmonicMass A N := by
  unfold shiftedHarmonicMass shiftedHarmonicRaw
  apply sum_pos'
  · intro n _; positivity
  · exact ⟨0,mem_range.mpr (by omega),by positivity⟩

lemma shiftedHarmonicMass_le_length (A N : ℕ) : shiftedHarmonicMass A N ≤ N+1 := by
  calc
    _ ≤ ∑ _n ∈ range (N+1), (1 : ℝ) := by
      unfold shiftedHarmonicMass shiftedHarmonicRaw
      apply sum_le_sum
      intro n _
      exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) A; have := Nat.cast_nonneg (α := ℝ) n; linarith)
    _ = _ := by simp

lemma shiftedHarmonicMean_add (A N : ℕ) (F G : ℕ → ℝ) :
    shiftedHarmonicMean A N (fun n => F n+G n) = shiftedHarmonicMean A N F+shiftedHarmonicMean A N G := by
  simp only [shiftedHarmonicMean,shiftedHarmonicRaw,add_div,sum_add_distrib]

lemma shiftedHarmonicMean_sub (A N : ℕ) (F G : ℕ → ℝ) :
    shiftedHarmonicMean A N (fun n => F n-G n) = shiftedHarmonicMean A N F-shiftedHarmonicMean A N G := by
  simp only [shiftedHarmonicMean,shiftedHarmonicRaw,sub_div,sum_sub_distrib]

lemma shiftedHarmonicMean_const_mul (A N : ℕ) (c : ℝ) (F : ℕ → ℝ) :
    shiftedHarmonicMean A N (fun n => c*F n) = c*shiftedHarmonicMean A N F := by
  simp only [shiftedHarmonicMean,shiftedHarmonicRaw,mul_div_assoc,← mul_sum]

lemma shiftedHarmonicMean_const (A N : ℕ) (c : ℝ) : shiftedHarmonicMean A N (fun _ => c) = c := by
  have he := shiftedHarmonicMean_const_mul A N c (fun _ => 1)
  have hOne : shiftedHarmonicMean A N (fun _ => 1) = 1 :=
    div_self (shiftedHarmonicMass_pos A N).ne'
  simpa only [mul_one,hOne] using he

lemma shiftedHarmonicMean_mono (A N : ℕ) (F G : ℕ → ℝ) (h : ∀ n, F n ≤ G n) :
    shiftedHarmonicMean A N F ≤ shiftedHarmonicMean A N G := by
  apply div_le_div_of_nonneg_right _ (shiftedHarmonicMass_pos A N).le
  apply sum_le_sum
  intro n _
  exact div_le_div_of_nonneg_right (h _) (by positivity)

lemma shiftedHarmonicMean_abs_le (A N : ℕ) (F : ℕ → ℝ) :
    |shiftedHarmonicMean A N F| ≤ shiftedHarmonicMean A N (fun n => |F n|) := by
  unfold shiftedHarmonicMean shiftedHarmonicRaw
  rw [abs_div,abs_of_pos (shiftedHarmonicMass_pos A N)]
  apply div_le_div_of_nonneg_right _ (shiftedHarmonicMass_pos A N).le
  apply (abs_sum_le_sum_abs _ _).trans_eq
  apply sum_congr rfl
  intro n _
  rw [abs_div,abs_of_pos (by positivity : (0 : ℝ) < A+n+1)]

lemma shiftedHarmonicMean_abs_difference_le (A N : ℕ) (F G : ℕ → ℝ) :
    |shiftedHarmonicMean A N F-shiftedHarmonicMean A N G| ≤
      shiftedHarmonicMean A N (fun n => |F n-G n|) := by
  rw [← shiftedHarmonicMean_sub]
  exact shiftedHarmonicMean_abs_le A N _

lemma shiftedHarmonicMean_unit_bound (A N : ℕ) (F : ℕ → ℝ) (hF : ∀ n, |F n| ≤ 1) :
    |shiftedHarmonicMean A N F| ≤ 1 := by
  exact (shiftedHarmonicMean_abs_le A N F).trans
    ((shiftedHarmonicMean_mono A N _ _ hF).trans_eq (shiftedHarmonicMean_const A N 1))

lemma shifted_reciprocal_antitone (A : ℕ) : Antitone (fun n : ℕ => (1 : ℝ)/(A+n+1)) := by
  intro n m hnm
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (show A+n+1≤A+m+1 by omega))

lemma shiftedHarmonicMean_prefix_mixture (A N : ℕ) (F : ℕ → ℝ) :
    shiftedHarmonicMean A N F =
      mean (decreasingPrefixLaw (fun n => (1 : ℝ)/(A+n+1)) N (fun _ _ => by positivity)
        ((shifted_reciprocal_antitone A).antitoneOn _) (shiftedHarmonicMass_pos A N))
        (fun i => prefixMean (harmonicPrefixLength N i) (fun n => F (A+n+1))) := by
  rw [decreasingPrefixLaw_representation]
  unfold shiftedHarmonicMean shiftedHarmonicRaw shiftedHarmonicMass
  congr 1
  apply sum_congr rfl
  intro n _
  ring

lemma nonnegative_prefix_global_bound (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n ∧ F n ≤ 1)
    (hlim : Tendsto (fun N => prefixMean N F) atTop (𝓝 0)) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, (∑ n ∈ range N, F n) ≤ ε*N+C := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hlim.eventually_lt_const hε)
  refine ⟨K,Nat.cast_nonneg K,?_⟩
  intro N
  by_cases hN : N=0
  · subst N; simp
  by_cases hNK : K ≤ N
  · have hNr : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
    have hmean := hK N hNK
    unfold prefixMean at hmean
    have hs := (div_lt_iff₀ hNr).mp hmean
    linarith [Nat.cast_nonneg (α := ℝ) K]
  · have hs : (∑ n ∈ range N, F n) ≤ N := by
      simpa using (sum_le_sum (s := range N) (fun n _ => (hF n).2))
    have hnK : (N : ℝ) ≤ K := by exact_mod_cast (by omega : N ≤ K)
    have he : 0 ≤ ε*(N : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg N)
    linarith

lemma shifted_prefix_bound (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) (ε C : ℝ)
    (hbound : ∀ N : ℕ, (∑ n ∈ range N, F n) ≤ ε*N+C) (A k : ℕ) (hk : 0 < k) :
    prefixMean k (fun n => F (A+n+1)) ≤ ε+(ε*(A+1 : ℝ)+C)/k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hs := hbound (A+1+k)
  rw [sum_range_add] at hs
  have hnon := sum_nonneg (s := range (A+1)) (fun n _ => hF n)
  have he : (∑ n ∈ range k, F (A+1+n)) = ∑ n ∈ range k, F (A+n+1) := by
    apply sum_congr rfl
    intro n _
    congr 1; omega
  rw [he] at hs
  unfold prefixMean
  apply (div_le_iff₀ hkR).mpr
  have hden : (ε+(ε*(A+1 : ℝ)+C)/(k : ℝ))*(k : ℝ) = ε*k+ε*(A+1 : ℝ)+C := by field_simp; ring
  rw [hden]
  push_cast at hs
  linarith

/-- Uniform Abel bound. A nonnegative sequence with a small global prefix
mean has a small mean on every interval of large harmonic mass. -/
lemma shiftedHarmonicMean_of_prefix_bound (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n)
    (ε C : ℝ) (_hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, (∑ n ∈ range N, F n) ≤ ε*N+C) (A N : ℕ) :
    shiftedHarmonicMean A N F ≤ ε+(ε+C)/shiftedHarmonicMass A N := by
  rw [shiftedHarmonicMean_prefix_mixture]
  let ρ := decreasingPrefixLaw (fun n => (1 : ℝ)/(A+n+1)) N (fun _ _ => by positivity)
    ((shifted_reciprocal_antitone A).antitoneOn _) (shiftedHarmonicMass_pos A N)
  have hm := mean_mono ρ _ _ (fun i => shifted_prefix_bound F hF ε C hbound A
    (harmonicPrefixLength N i) (harmonicPrefixLength_pos N i))
  have hid (i : Fin (N+1)) : ε+(ε*(A+1 : ℝ)+C)/(harmonicPrefixLength N i : ℝ) =
      ε+(ε*(A+1 : ℝ)+C)*((1 : ℝ)/harmonicPrefixLength N i) := by ring
  simp_rw [hid] at hm
  rw [mean_add,mean_const,mean_const_mul] at hm
  dsimp only [ρ] at hm
  rw [decreasingPrefixLaw_reciprocal_length] at hm
  have hAC : (ε*(A+1 : ℝ)+C)*(1/(A+0+1 : ℝ)) ≤ ε+C := by
    have ha : (1 : ℝ) ≤ A+1 := by have := Nat.cast_nonneg (α := ℝ) A; linarith
    have hap : (0 : ℝ) < A+1 := by positivity
    simp only [add_zero,mul_one_div]
    apply (div_le_iff₀ hap).mpr
    nlinarith
  simp only [Nat.cast_zero] at hm
  apply hm.trans
  change ε+(ε*(A+1 : ℝ)+C)*(1/(A+0+1 : ℝ)/shiftedHarmonicMass A N) ≤ _
  rw [← mul_div_assoc]
  exact add_le_add le_rfl (div_le_div_of_nonneg_right hAC (shiftedHarmonicMass_pos A N).le)

/-- Natural mean zero for a nonnegative bounded sequence implies harmonic
mean zero uniformly along all intervals whose harmonic mass tends to infinity. -/
theorem shiftedHarmonicMean_zero_of_nonnegative_prefix_zero (F : ℕ → ℝ)
    (hF : ∀ n, 0 ≤ F n ∧ F n ≤ 1)
    (hlim : Tendsto (fun N => prefixMean N F) atTop (𝓝 0))
    (A M : ℕ → ℕ) (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop) :
    Tendsto (fun j => shiftedHarmonicMean (A j) (M j) F) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := nonnegative_prefix_global_bound F hF hlim (ε/2) (by positivity)
  have ht : Tendsto (fun j => (ε/2+C)/shiftedHarmonicMass (A j) (M j)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hH
  filter_upwards [ht.eventually_lt_const (by positivity : (0 : ℝ) < ε/2)] with j hj
  have hb := shiftedHarmonicMean_of_prefix_bound F (fun n => (hF n).1) (ε/2) C (by positivity) hC hbound (A j) (M j)
  have hn : 0 ≤ shiftedHarmonicMean (A j) (M j) F := by
    have hh := shiftedHarmonicMean_mono (A j) (M j) (fun _ => 0) F (fun n => (hF n).1)
    simpa only [shiftedHarmonicMean_const] using hh
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hn]
  linarith

lemma positiveRawSum_shift_bound (T : ℕ) (F : ℕ → ℝ) (hF : ∀ n, |F n| ≤ 1) :
    |positiveRawSum T (fun n => F (n+1))-positiveRawSum T F| ≤ 2 := by
  cases T with
  | zero => simp [positiveRawSum]
  | succ N =>
    have h := harmonicMean_succ_error N F hF
    unfold harmonicMean at h
    rw [← sub_div,abs_div,abs_of_pos (harmonic_real_pos N)] at h
    have hh := (div_le_div_iff₀ (harmonic_real_pos N) (harmonic_real_pos N)).mp h
    change _ ≤ _ at hh
    exact (mul_le_mul_iff_left₀ (harmonic_real_pos N)).mp hh

lemma shiftedHarmonicMean_shift_bound (A N : ℕ) (F : ℕ → ℝ) (hF : ∀ n, |F n| ≤ 1) :
    |shiftedHarmonicMean A N (fun n => F (n+1))-shiftedHarmonicMean A N F| ≤
      4/shiftedHarmonicMass A N := by
  have h₁ := positiveRawSum_shift_bound (A+N+1) F hF
  have h₂ := positiveRawSum_shift_bound A F hF
  unfold shiftedHarmonicMean
  rw [← sub_div,abs_div,abs_of_pos (shiftedHarmonicMass_pos A N)]
  apply div_le_div_of_nonneg_right _ (shiftedHarmonicMass_pos A N).le
  rw [shiftedHarmonicRaw_eq_sub,shiftedHarmonicRaw_eq_sub]
  have he : (positiveRawSum (A+N+1) (fun n => F (n+1))-positiveRawSum A (fun n => F (n+1))) -
      (positiveRawSum (A+N+1) F-positiveRawSum A F) =
      (positiveRawSum (A+N+1) (fun n => F (n+1))-positiveRawSum (A+N+1) F) -
        (positiveRawSum A (fun n => F (n+1))-positiveRawSum A F) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

#print axioms shiftedHarmonicMean_zero_of_nonnegative_prefix_zero
#print axioms shiftedHarmonicMean_shift_bound
end Erdos371.FiniteInformation
