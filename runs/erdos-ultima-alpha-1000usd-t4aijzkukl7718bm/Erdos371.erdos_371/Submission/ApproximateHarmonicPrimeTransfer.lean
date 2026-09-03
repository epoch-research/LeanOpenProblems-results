import Submission.FixedComparisonApproximation

/-! Harmonic prime transfer for a fixed finite label sequence whose fixed
multipliers are invariant in natural mean, rather than pointwise. -/
namespace Erdos371.FiniteInformation
open Finset Filter BlockPrimes EntropyScales
open scoped Topology
set_option autoImplicit false

lemma harmonicMean_add (N : ℕ) (F G : ℕ → ℝ) :
    harmonicMean N (fun n => F n+G n) = harmonicMean N F+harmonicMean N G := by
  simp only [harmonicMean,add_div,sum_add_distrib]

lemma harmonicMean_mono (N : ℕ) (F G : ℕ → ℝ) (h : ∀ n, F n ≤ G n) :
    harmonicMean (N+1) F ≤ harmonicMean (N+1) G := by
  apply div_le_div_of_nonneg_right _ (harmonic_real_pos N).le
  apply sum_le_sum
  intro n hn
  exact div_le_div_of_nonneg_right (h n) (Nat.cast_nonneg n)

noncomputable def labelDilationDefect {A : Type*} (p : ℕ) (L : ℕ → A) (n : ℕ) : ℝ := by
  classical
  exact if L (p*n) ≠ L n then 1 else 0

lemma labelDilationDefect_abs_le {A : Type*} (p : ℕ) (L : ℕ → A) (n : ℕ) :
    |labelDilationDefect p L n| ≤ 1 := by
  unfold labelDilationDefect
  split_ifs <;> norm_num

noncomputable def harmonicDilationBudget {A : Type*} (N p : ℕ) (L : ℕ → A) : ℝ :=
  p/(harmonic (N+1) : ℝ)+2*harmonicMean (N+1) (labelDilationDefect p L)+
    2*harmonicMean (N+1) (fun m => labelDilationDefect p L (m+1))

/-- Exact dilation plus an explicit bound for both label defects. The bound
is uniform over all unit-bounded pair observables. -/
lemma harmonic_approximate_dilation_error {A : Type*} (N p : ℕ) (hp : 0 < p)
    (L : ℕ → A) (C : A → A → ℝ) (hC : ∀ a b, |C a b| ≤ 1) :
    |harmonicGapDiscrepancy (N+1) p L C-
      (harmonicMean (N+1) (fun m => C (L m) (L (m+1)))-
        harmonicMean (N+1) (fun m => C (L m) (L (m+p))))| ≤ harmonicDilationBudget N p L := by
  classical
  let V (m : ℕ) := C (L (p*m)) (L (p*(m+1)))
  let W (m : ℕ) := C (L m) (L (m+1))
  let A : ℝ := p*harmonicMean (N+1) (fun m => if p ∣ m then C (L m) (L (m+p)) else 0)
  have hd : A = (∑ m ∈ Icc 1 ((N+1)/p), V m/(m : ℝ))/(harmonic (N+1) : ℝ) := by
    dsimp [A,harmonicMean]
    simp only [ite_div,zero_div]
    rw [← mul_div_assoc,harmonic_dilation_sum p (N+1) hp]
    congr 1
  have htail : |A-harmonicMean (N+1) V| ≤ p/(harmonic (N+1) : ℝ) := by
    rw [hd,harmonicMean,← sub_div,abs_div,abs_of_pos (harmonic_real_pos N),abs_sub_comm]
    exact div_le_div_of_nonneg_right (harmonic_div_endpoint_bound p (N+1) hp V (fun m => hC _ _))
      (harmonic_real_pos N).le
  have hdiff : |harmonicMean (N+1) V-harmonicMean (N+1) W| ≤
      2*harmonicMean (N+1) (labelDilationDefect p L)+
        2*harmonicMean (N+1) (fun m => labelDilationDefect p L (m+1)) := by
    apply (harmonicMean_abs_difference_le N V W).trans
    have hm := harmonicMean_mono N (fun m => |V m-W m|)
      (fun m => 2*labelDilationDefect p L m+2*labelDilationDefect p L (m+1))
      (fun m => bounded_pair_observable_change C hC _ _ _ _)
    simpa only [harmonicMean_add,harmonicMean_const_mul] using hm
  unfold harmonicGapDiscrepancy
  rw [sub_sub_sub_cancel_right]
  change |A-harmonicMean (N+1) W| ≤ _
  exact (abs_sub_le A (harmonicMean (N+1) V) (harmonicMean (N+1) W)).trans
    ((add_le_add htail hdiff).trans_eq (by dsimp [harmonicDilationBudget]; ring))

lemma harmonicDilationBudget_zero {A : Type*} (p : ℕ) (L : ℕ → A)
    (hL : Tendsto (fun N => prefixMean N (labelDilationDefect p L)) atTop (𝓝 0)) :
    Tendsto (fun N => harmonicDilationBudget N p L) atTop (𝓝 0) := by
  have hd := harmonicMean_zero_of_prefixMean_zero (labelDilationDefect p L)
    (labelDilationDefect_abs_le p L) hL
  have hs := prefixMean_succ_zero (fun _ => labelDilationDefect p L)
    (fun _ => labelDilationDefect_abs_le p L) hL
  have hd' := harmonicMean_zero_of_prefixMean_zero (fun n => labelDilationDefect p L (n+1))
    (fun n => labelDilationDefect_abs_le p L (n+1)) hs
  have ht : Tendsto (fun N : ℕ => (p : ℝ)/(harmonic (N+1) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop harmonic_real_tendsto
  simpa only [harmonicDilationBudget,mul_zero,add_zero] using (ht.add (hd.const_mul 2)).add (hd'.const_mul 2)

/-- One scale works for a fixed label process with negligible dilation
errors. The finite horizon is uniform in that process. -/
theorem approximate_harmonic_prime_transfer {A : Type*} [Fintype A]
    (H₀ : ℕ) (hH₀ : 8 ≤ H₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ K > 0, ∀ L : ℕ → A,
      (∀ p, 0 < p → Tendsto (fun N => prefixMean N (labelDilationDefect p L)) atTop (𝓝 0)) →
      ∀ᶠ N : ℕ in atTop, ∃ n < K,
      ∀ C : A → A → ℝ, (∀ a b, |C a b| ≤ 1) →
        |harmonicMean (N+1) (fun m => C (L m) (L (m+1)))-
          (∑ p ∈ halfBlockPrimes (factorialScale H₀ n),
            harmonicMean (N+1) (fun m => C (L m) (L (m+p)))) /
              (halfBlockPrimes (factorialScale H₀ n)).card| < ε := by
  classical
  obtain ⟨K,hK,htrans⟩ := harmonic_prime_gap_transfer (A := A) H₀ hH₀ (ε/2) (by positivity)
  let B := (range K).sup (factorialScale H₀)
  refine ⟨K,hK,?_⟩
  intro L hL
  have he : ∀ᶠ N : ℕ in atTop, ∀ p : Icc 1 B, harmonicDilationBudget N p L < ε/2 := by
    apply eventually_all.mpr
    intro p
    exact (harmonicDilationBudget_zero p L (hL p (mem_Icc.mp p.property).1)).eventually_lt_const (by positivity)
  filter_upwards [htrans,he] with N htrans he
  obtain ⟨n,hn,hscale⟩ := htrans L
  refine ⟨n,hn,?_⟩
  intro C hC
  let S := halfBlockPrimes (factorialScale H₀ n)
  have hH : factorialScale H₀ n ≤ B := le_sup (mem_range.mpr hn)
  have hS : S.Nonempty := halfBlockPrimes_nonempty _
    (le_trans (by omega : 4 ≤ H₀) (factorialScale_ge H₀ n))
  let V (p : ℕ) := harmonicMean (N+1) (fun m => C (L m) (L (m+p)))
  have herr : |(∑ p ∈ S, (harmonicGapDiscrepancy (N+1) p L C-(V 1-V p)))/(S.card : ℝ)| ≤ ε/2 := by
    apply abs_finset_average_le S hS
    intro p hp
    obtain ⟨hpp,hpH⟩ := mem_halfBlockPrimes.mp hp
    have hpB : p ≤ B := by omega
    exact (harmonic_approximate_dilation_error N p hpp.pos L C hC).trans
      (he ⟨p,mem_Icc.mpr ⟨hpp.pos,hpB⟩⟩).le
  have heq : (∑ p ∈ S, (V 1-V p))/(S.card : ℝ) = V 1-(∑ p ∈ S,V p)/(S.card : ℝ) := by
    rw [sum_sub_distrib,sub_div,sum_const,nsmul_eq_mul]
    have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hS).ne'
    field_simp
  rw [sum_sub_distrib,sub_div,heq,abs_sub_comm] at herr
  have hs := hscale C hC
  change |(∑ p ∈ S,harmonicGapDiscrepancy (N+1) p L C)/(S.card : ℝ)| < ε/2 at hs
  have htri := abs_sub_le (V 1-(∑ p ∈ S,V p)/(S.card : ℝ))
    ((∑ p ∈ S,harmonicGapDiscrepancy (N+1) p L C)/(S.card : ℝ)) 0
  simp only [sub_zero] at htri
  change |V 1-(∑ p ∈ S,V p)/(S.card : ℝ)| < ε
  linarith

#print axioms harmonic_approximate_dilation_error
#print axioms approximate_harmonic_prime_transfer
end Erdos371.FiniteInformation
