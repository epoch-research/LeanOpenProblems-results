import Submission.CertifiedSparseRestorationMenuExplore
import Submission.MonotoneClippingExplore

/-! Conditional all-target upper clipping with exact harmonic brackets.
The negligible deletion-budget hypothesis is explicit and is not supplied
by the known weak power-saving exceptional estimates. -/
namespace Erdos66CertifiedGlobalUpperClipping
open Filter AdditiveCombinatorics Erdos66Counting Erdos66Fractional
  Erdos66ClampedPrefixContinuation Erdos66UniformSparseRestorationMenu
  Erdos66CertifiedSparseRestorationMenu Erdos66SublogPatternInvariants
  Erdos66MonotoneClipping Erdos66Explore
open scoped Classical Topology
set_option maxHeartbeats 3500000

lemma tail_core_union (A D : Set ℕ) (hDA : D ⊆ A) (N : ℕ) :
    A\{d | d∈D ∧ N ≤ d} = (A\D)∪(cutoff D N : Set ℕ) := by
  ext a
  simp only [Set.mem_diff,Set.mem_setOf_eq,Set.mem_union,Finset.mem_coe,mem_cutoff]
  constructor
  · rintro ⟨ha,he⟩
    by_cases hd : a∈D
    · exact Or.inr ⟨by by_contra hn; exact he ⟨hd,by omega⟩,hd⟩
    · exact Or.inl ⟨ha,hd⟩
  · rintro (⟨ha,hd⟩ | ⟨haN,hd⟩)
    · exact ⟨ha,fun h ↦ hd h.1⟩
    · exact ⟨hDA hd,fun h ↦ by omega⟩

/-- Restoring the finite untreated initial part costs only a bounded
representation increment. Both qualitative invariants survive. -/
theorem exists_certified_full_restoration
    (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (hB : SmallBoundary A) (hT : SublogCentral A)
    (D : Set ℕ) (hDA : D ⊆ A)
    (hdec : Tendsto (fun n : ℕ ↦ (count D n : ℝ)/Real.sqrt ((n : ℝ)*Real.log n)) atTop (𝓝 0)) :
    ∃ B : Set ℕ, A\D ⊆ B ∧ (∀ L, PrefixBrackets profile B L) ∧
      SmallBoundary B ∧ SublogCentral B ∧
      Tendsto (fun n : ℕ ↦ ((sumRep B n : ℝ)-sumRep (A\D) n)/Real.log n) atTop (𝓝 0) := by
  obtain ⟨F,hFA,hFT,hmenu⟩ := exists_certified_sparse_restoration_menu A hbr hB hT D hDA hdec
  obtain ⟨N,hN⟩ := hmenu 1 (by norm_num)
  let E : Set ℕ := {d | d∈D ∧ N ≤ d}
  have hED : E ⊆ D := fun _ h ↦ h.1
  obtain ⟨hcore,hbr',hinc,hlim⟩ := hN E hED (fun _ h ↦ h.2)
  let B := restoredFrom A hbr F E
  have hcore' : A\D ⊆ B := (Set.diff_subset_diff_right hED).trans hcore
  have hmono (n : ℕ) : 0 ≤ (sumRep B n : ℝ)-sumRep (A\D) n := by
    exact sub_nonneg.mpr (by exact_mod_cast sumRep_mono hcore' n)
  have hbounded (n : ℕ) : (sumRep B n : ℝ)-sumRep (A\D) n ≤
      ((sumRep B n : ℝ)-sumRep (A\E) n)+2*((cutoff D N).card : ℝ) := by
    have hh := Erdos66PredecessorCutoffTransfer.sumRep_union_finset (A\D) (cutoff D N) n
    rw [←tail_core_union A D hDA N] at hh
    have hh' : (sumRep (A\E) n : ℝ) ≤ sumRep (A\D) n+2*((cutoff D N).card : ℝ) := by
      exact_mod_cast hh
    linarith only [hh']
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hupperlim := hlim.add (hlog.const_div_atTop (2*((cutoff D N).card : ℝ)))
  simp only [add_zero] at hupperlim
  refine ⟨B,hcore',hbr',(hFT E).1,(hFT E).2,?_⟩
  apply squeeze_zero (fun n ↦ div_nonneg (hmono n) (Real.log_natCast_nonneg n)) ?_ hupperlim
  intro n
  have hh := div_le_div_of_nonneg_right (hbounded n) (Real.log_natCast_nonneg n)
  simpa only [add_div] using hh

/-- Every upper cap is handled simultaneously. What must be checked is the
actual excess budget, not just density zero of the exceptional targets. -/
theorem exists_certified_upper_clipping_under_budget
    (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (hB : SmallBoundary A) (hT : SublogCentral A)
    (q : ℕ → ℕ) (hq : ∀ n, 1 ≤ q n)
    (hbudget : Tendsto (fun N : ℕ ↦
      (∑ n∈Finset.range (2*N), (excess (sumRep A n) (q n) : ℝ))/
        Real.sqrt ((N : ℝ)*Real.log N)) atTop (𝓝 0)) :
    ∃ B C : Set ℕ, C ⊆ A ∧ C ⊆ B ∧ (∀ n, sumRep C n ≤ q n) ∧
      (∀ L, PrefixBrackets profile B L) ∧ SmallBoundary B ∧ SublogCentral B ∧
      Tendsto (fun n : ℕ ↦ ((sumRep B n : ℝ)-sumRep C n)/Real.log n) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ ↦ max ((sumRep B n : ℝ)-(q n : ℝ)) 0/Real.log n) atTop (𝓝 0) := by
  obtain ⟨C,hCA,hcap,hsmall⟩ := exists_simultaneous_upper_clipping A q hq
  have hdec : Tendsto (fun N : ℕ ↦ (count (A\C) N : ℝ)/Real.sqrt ((N : ℝ)*Real.log N)) atTop (𝓝 0) := by
    apply squeeze_zero (fun N ↦ div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) ?_ hbudget
    intro N
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact_mod_cast hsmall N
  obtain ⟨B,hcore,hbr',hB',hT',hlim⟩ := exists_certified_full_restoration A hbr hB hT
    (A\C) Set.diff_subset hdec
  have hCC : A\(A\C)=C := by ext a; simp only [Set.mem_diff]; constructor <;> tauto
  rw [hCC] at hcore hlim
  refine ⟨B,C,hCA,hcore,hcap,hbr',hB',hT',hlim,?_⟩
  apply squeeze_zero (fun n ↦ div_nonneg (le_max_right _ _) (Real.log_natCast_nonneg n)) ?_ hlim
  intro n
  apply div_le_div_of_nonneg_right _ (Real.log_natCast_nonneg n)
  have hm : (sumRep C n : ℝ) ≤ sumRep B n := by exact_mod_cast sumRep_mono hcore n
  have hc : (sumRep C n : ℝ) ≤ q n := by exact_mod_cast hcap n
  exact max_le (by linarith only [hc]) (by linarith only [hm])

lemma upper_limit_of_excess_limit (B : Set ℕ) (q : ℕ → ℕ) (c : ℝ)
    (hq : Tendsto (fun n : ℕ ↦ (q n : ℝ)/Real.log n) atTop (𝓝 c))
    (hB : Tendsto (fun n : ℕ ↦ max ((sumRep B n : ℝ)-(q n : ℝ)) 0/Real.log n) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ n : ℕ in atTop, (sumRep B n : ℝ)/Real.log n ≤ c+ε := by
  intro ε hε
  have hh := hq.add hB
  simp only [add_zero] at hh
  filter_upwards [hh.eventually_le_const (show c<c+ε by linarith)] with n hn
  have hp := div_le_div_of_nonneg_right (le_max_left ((sumRep B n : ℝ)-(q n : ℝ)) 0)
    (Real.log_natCast_nonneg n)
  rw [sub_div] at hp
  linarith only [hp,hn]

end Erdos66CertifiedGlobalUpperClipping
