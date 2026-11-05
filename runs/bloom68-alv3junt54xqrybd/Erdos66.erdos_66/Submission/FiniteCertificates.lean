import Submission.Reduction

/-!
# Finite certificates for the Erdős 66 compactness reduction

These are equivalences and conditional reductions, not existence proofs.
A certificate only controls representations up to its horizon.  A lookahead-pruned
certificate also bounds the representations already forced by its prefix up to
twice the horizon.  All parameters are preserved by the pruning equivalence.
This module imports only the proved reduction, not the conjecture specification.
-/

open Filter AdditiveCombinatorics
open scoped Topology
set_option linter.style.namespace false
set_option linter.style.stubs false
set_option linter.style.openClassical false

namespace Erdos66.Compactness

/-- The restriction of a set to the integers from `0` through `M`, inclusive. -/
noncomputable def prefixFinset (A : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (M + 1)).filter (fun i => i ∈ A)

@[simp] lemma mem_prefixFinset {A : Set ℕ} {M i : ℕ} :
    i ∈ prefixFinset A M ↔ i ≤ M ∧ i ∈ A := by
  classical
  simp [prefixFinset]

lemma prefixFinset_subset_range (A : Set ℕ) (M : ℕ) :
    prefixFinset A M ⊆ Finset.range (M + 1) := by
  classical
  exact Finset.filter_subset _ _

lemma sumRep_prefixFinset (A : Set ℕ) {M n : ℕ} (hn : n ≤ M) :
    sumRep (prefixFinset A M : Set ℕ) n = sumRep A n := by
  apply sumRep_prefix_local
  intro i hi
  simp only [Finset.mem_coe, mem_prefixFinset, and_iff_right (hi.trans hn)]

lemma sumRep_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    sumRep A n ≤ sumRep B n := by
  classical
  rw [sumRep_def, sumRep_def]
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, h hp.2.1, h hp.2.2⟩

lemma sumRep_ratio_mono {A B : Set ℕ} (h : A ⊆ B) (n : ℕ) :
    (sumRep A n : ℝ) / Real.log n ≤ (sumRep B n : ℝ) / Real.log n :=
  div_le_div_of_nonneg_right (Nat.cast_le.mpr (sumRep_mono h n))
    (Real.log_natCast_nonneg n)

/-- A two-sided approximation on the interval `N0 ≤ n ≤ M`. -/
def PrefixCertificate (c : ℝ) (e : ℕ → ℝ) (N0 M : ℕ) (A : Set ℕ) : Prop :=
  ∀ n : ℕ, N0 ≤ n → n ≤ M → |(sumRep A n : ℝ) / Real.log n - c| ≤ e n

/-- A certificate encoded by a finite subset of the prescribed prefix. -/
def FinsetCertificate (c : ℝ) (e : ℕ → ℝ) (N0 M : ℕ) (F : Finset ℕ) : Prop :=
  F ⊆ Finset.range (M + 1) ∧ PrefixCertificate c e N0 M (F : Set ℕ)

/-- Upper bounds through `2 * M` prune prefixes that already force too many sums.
The quotient formulation also makes sense at `n = 0, 1`, where Lean's logarithm
and division conventions give a zero quotient. -/
def LookaheadCertificate (c : ℝ) (e : ℕ → ℝ) (N0 M : ℕ) (F : Finset ℕ) : Prop :=
  FinsetCertificate c e N0 M F ∧
    ∀ n : ℕ, N0 ≤ n → n ≤ 2 * M →
      (sumRep (F : Set ℕ) n : ℝ) / Real.log n ≤ c + e n

/-- At a single horizon, arbitrary sets and prefix-restricted finsets give
exactly the same certificates. -/
theorem finite_prefix_certificate_iff_finset (c : ℝ) (e : ℕ → ℝ) (N0 M : ℕ) :
    (∃ A : Set ℕ, PrefixCertificate c e N0 M A) ↔
      ∃ F : Finset ℕ, FinsetCertificate c e N0 M F := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨prefixFinset A M, prefixFinset_subset_range A M, ?_⟩
    intro n hn hM
    simpa only [sumRep_prefixFinset A hM] using hA n hn hM
  · rintro ⟨F, _, hF⟩
    exact ⟨(F : Set ℕ), hF⟩

/-- The finite-prefix compactness criterion can be expressed entirely by finsets. -/
theorem finite_prefix_certificates_iff_finset (c : ℝ) (e : ℕ → ℝ) (N0 : ℕ) :
    (∀ M, ∃ A : Set ℕ, PrefixCertificate c e N0 M A) ↔
      ∀ M, ∃ F : Finset ℕ, FinsetCertificate c e N0 M F := by
  constructor
  · intro h M
    exact (finite_prefix_certificate_iff_finset c e N0 M).mp (h M)
  · intro h M
    exact (finite_prefix_certificate_iff_finset c e N0 M).mpr (h M)

/-- Looking ahead preserves the *same* `c`, `e`, and `N0`.
For the forward direction, restrict a certificate at `2 * M` to `M`:
the old representations agree through `M` and can only decrease afterwards. -/
theorem finset_certificates_iff_lookahead (c : ℝ) (e : ℕ → ℝ) (N0 : ℕ) :
    (∀ M, ∃ F : Finset ℕ, FinsetCertificate c e N0 M F) ↔
      ∀ M, ∃ F : Finset ℕ, LookaheadCertificate c e N0 M F := by
  constructor
  · intro h M
    obtain ⟨F, _, hF⟩ := h (2 * M)
    refine ⟨prefixFinset (F : Set ℕ) M,
      ⟨prefixFinset_subset_range (F : Set ℕ) M, ?_⟩, ?_⟩
    · intro n hn hM
      rw [sumRep_prefixFinset (F : Set ℕ) hM]
      exact hF n hn (by omega)
    · intro n hn hM
      have hmono := sumRep_ratio_mono (A := (prefixFinset (F : Set ℕ) M : Set ℕ))
        (B := (F : Set ℕ)) (fun i hi => (mem_prefixFinset.mp hi).2) n
      have hupper := le_of_abs_le (hF n hn hM)
      linarith
  · intro h M
    obtain ⟨F, hF⟩ := h M
    exact ⟨F, hF.1⟩

/-- Fixed-parameter equivalence with the lookahead-pruned compactness criterion.
No positivity or convergence hypothesis is needed for this finite equivalence. -/
theorem finite_prefix_certificates_iff_lookahead (c : ℝ) (e : ℕ → ℝ) (N0 : ℕ) :
    (∀ M, ∃ A : Set ℕ, PrefixCertificate c e N0 M A) ↔
      ∀ M, ∃ F : Finset ℕ, LookaheadCertificate c e N0 M F :=
  (finite_prefix_certificates_iff_finset c e N0).trans
    (finset_certificates_iff_lookahead c e N0)

/-- Away from the two zero-logarithm indices, the pruning bounds are genuine
unnormalized representation-count caps. -/
theorem lookahead_certificate_iff_count_caps (c : ℝ) (e : ℕ → ℝ)
    (N0 M : ℕ) (F : Finset ℕ) (hN0 : 2 ≤ N0) :
    LookaheadCertificate c e N0 M F ↔
      FinsetCertificate c e N0 M F ∧
        ∀ n : ℕ, N0 ≤ n → n ≤ 2 * M →
          (sumRep (F : Set ℕ) n : ℝ) ≤ (c + e n) * Real.log n := by
  constructor
  · rintro ⟨hF, hu⟩
    refine ⟨hF, fun n hn hM => ?_⟩
    have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    exact (div_le_iff₀ hlog).mp (hu n hn hM)
  · rintro ⟨hF, hu⟩
    refine ⟨hF, fun n hn hM => ?_⟩
    have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    exact (div_le_iff₀ hlog).mpr (hu n hn hM)

/-- The count-cap version of the fixed-parameter compactness criterion. -/
theorem finite_prefix_certificates_iff_lookahead_count_caps
    (c : ℝ) (e : ℕ → ℝ) (N0 : ℕ) (hN0 : 2 ≤ N0) :
    (∀ M, ∃ A : Set ℕ, PrefixCertificate c e N0 M A) ↔
      ∀ M, ∃ F : Finset ℕ, FinsetCertificate c e N0 M F ∧
        ∀ n : ℕ, N0 ≤ n → n ≤ 2 * M →
          (sumRep (F : Set ℕ) n : ℝ) ≤ (c + e n) * Real.log n := by
  refine (finite_prefix_certificates_iff_lookahead c e N0).trans ?_
  exact forall_congr' fun M => exists_congr fun F =>
    lookahead_certificate_iff_count_caps c e N0 M F hN0

/-- The precise approximation/compactness equivalence, with no claimed witness. -/
theorem nonzero_limit_iff_finite_prefix_certificates :
    (∃ (A : Set ℕ) (c : ℝ), c ≠ 0 ∧
      Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) ↔
    ∃ c : ℝ, 0 < c ∧ ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∃ N0 : ℕ, ∀ M, ∃ A : Set ℕ, PrefixCertificate c e N0 M A := by
  constructor
  · rintro ⟨A, c, hc, h⟩
    refine ⟨c, positive_limit_of_sumRep hc h,
      (fun n => |(sumRep A n : ℝ) / Real.log n - c|), ?_, 2, ?_⟩
    · have hsub := h.sub (tendsto_const_nhds (x := c))
      simpa only [sub_self, abs_zero] using hsub.abs
    · intro M
      exact ⟨A, fun _ _ _ => le_rfl⟩
  · rintro ⟨c, hc, e, he, N0, hfin⟩
    obtain ⟨A, hAc, hA⟩ := finite_prefix_approximation_gives_limit c hc e he N0 hfin
    exact ⟨A, c, hAc, hA⟩

/-- Equivalent finset-only formulation of the nonzero-limit question. -/
theorem nonzero_limit_iff_finset_certificates :
    (∃ (A : Set ℕ) (c : ℝ), c ≠ 0 ∧
      Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) ↔
    ∃ c : ℝ, 0 < c ∧ ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∃ N0 : ℕ, ∀ M, ∃ F : Finset ℕ, FinsetCertificate c e N0 M F := by
  rw [nonzero_limit_iff_finite_prefix_certificates]
  constructor
  · rintro ⟨c, hc, e, he, N0, h⟩
    exact ⟨c, hc, e, he, N0, (finite_prefix_certificates_iff_finset c e N0).mp h⟩
  · rintro ⟨c, hc, e, he, N0, h⟩
    exact ⟨c, hc, e, he, N0, (finite_prefix_certificates_iff_finset c e N0).mpr h⟩

/-- Equivalent lookahead-pruned formulation of the nonzero-limit question. -/
theorem nonzero_limit_iff_lookahead_certificates :
    (∃ (A : Set ℕ) (c : ℝ), c ≠ 0 ∧
      Tendsto (fun n : ℕ => (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) ↔
    ∃ c : ℝ, 0 < c ∧ ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∃ N0 : ℕ, ∀ M, ∃ F : Finset ℕ, LookaheadCertificate c e N0 M F := by
  rw [nonzero_limit_iff_finset_certificates]
  constructor
  · rintro ⟨c, hc, e, he, N0, h⟩
    exact ⟨c, hc, e, he, N0, (finset_certificates_iff_lookahead c e N0).mp h⟩
  · rintro ⟨c, hc, e, he, N0, h⟩
    exact ⟨c, hc, e, he, N0, (finset_certificates_iff_lookahead c e N0).mpr h⟩

/-- Changing membership only inside `D` adds at most two representations per
changed member: one for each position in the ordered pair. -/
lemma sumRep_le_of_agree_off_finset {A B : Set ℕ} (D : Finset ℕ)
    (h : ∀ i, i ∉ D → (i ∈ A ↔ i ∈ B)) (n : ℕ) :
    sumRep A n ≤ sumRep B n + 2 * D.card := by
  classical
  rw [sumRep_def, sumRep_def]
  let S := (Finset.antidiagonal n).filter (fun p => p.1 ∈ A ∧ p.2 ∈ A)
  let T := (Finset.antidiagonal n).filter (fun p => p.1 ∈ B ∧ p.2 ∈ B)
  let C₁ := (Finset.antidiagonal n).filter (fun p => p.1 ∈ D)
  let C₂ := (Finset.antidiagonal n).filter (fun p => p.2 ∈ D)
  change S.card ≤ T.card + 2 * D.card
  have hc₁ : C₁.card ≤ D.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      simp only [C₁, Finset.mem_coe, Finset.mem_filter] at hp
      exact hp.2
    · intro p hp q hq hpq
      simp only [C₁, Finset.mem_coe, Finset.mem_filter, Finset.mem_antidiagonal] at hp hq
      apply Prod.ext
      · exact hpq
      · omega
  have hc₂ : C₂.card ≤ D.card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro p hp
      simp only [C₂, Finset.mem_coe, Finset.mem_filter] at hp
      exact hp.2
    · intro p hp q hq hpq
      simp only [C₂, Finset.mem_coe, Finset.mem_filter, Finset.mem_antidiagonal] at hp hq
      apply Prod.ext
      · omega
      · exact hpq
  have hsub : S \ T ⊆ C₁ ∪ C₂ := by
    intro p hp
    obtain ⟨hp, hpt⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hp0, hpA1, hpA2⟩ := Finset.mem_filter.mp hp
    by_cases h1 : p.1 ∈ D
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hp0, h1⟩))
    by_cases h2 : p.2 ∈ D
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hp0, h2⟩))
    exact (hpt (Finset.mem_filter.mpr
      ⟨hp0, (h _ h1).mp hpA1, (h _ h2).mp hpA2⟩)).elim
  have hdiff := (Finset.card_le_card hsub).trans (Finset.card_union_le C₁ C₂)
  have htotal := Finset.card_le_card_sdiff_add_card (s := S) (t := T)
  omega

/-- A uniform two-sided representation-count bound for a finite membership change. -/
lemma abs_sumRep_sub_le_of_agree_off_finset {A B : Set ℕ} (D : Finset ℕ)
    (h : ∀ i, i ∉ D → (i ∈ A ↔ i ∈ B)) (n : ℕ) :
    |(sumRep A n : ℝ) - (sumRep B n : ℝ)| ≤ 2 * (D.card : ℝ) := by
  have hab : (sumRep A n : ℝ) ≤ (sumRep B n : ℝ) + 2 * (D.card : ℝ) := by
    exact_mod_cast sumRep_le_of_agree_off_finset D h n
  have hba : (sumRep B n : ℝ) ≤ (sumRep A n : ℝ) + 2 * (D.card : ℝ) := by
    exact_mod_cast sumRep_le_of_agree_off_finset D (fun i hi => (h i hi).symm) n
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- In particular, a finite symmetric difference gives the bound `2 * |A △ B|`. -/
lemma abs_sumRep_sub_le_of_finite_symmDiff {A B : Set ℕ}
    (hD : (symmDiff A B).Finite) (n : ℕ) :
    |(sumRep A n : ℝ) - (sumRep B n : ℝ)| ≤ 2 * (hD.toFinset.card : ℝ) := by
  apply abs_sumRep_sub_le_of_agree_off_finset hD.toFinset
  intro i hi
  have hi' : i ∉ symmDiff A B := fun hmem => hi (hD.mem_toFinset.mpr hmem)
  rw [Set.mem_symmDiff] at hi'
  tauto

end Erdos66.Compactness

/- Axiom audit of every declaration introduced in this module. -/
#print axioms Erdos66.Compactness.prefixFinset
#print axioms Erdos66.Compactness.mem_prefixFinset
#print axioms Erdos66.Compactness.prefixFinset_subset_range
#print axioms Erdos66.Compactness.sumRep_prefixFinset
#print axioms Erdos66.Compactness.sumRep_mono
#print axioms Erdos66.Compactness.sumRep_ratio_mono
#print axioms Erdos66.Compactness.PrefixCertificate
#print axioms Erdos66.Compactness.FinsetCertificate
#print axioms Erdos66.Compactness.LookaheadCertificate
#print axioms Erdos66.Compactness.finite_prefix_certificate_iff_finset
#print axioms Erdos66.Compactness.finite_prefix_certificates_iff_finset
#print axioms Erdos66.Compactness.finset_certificates_iff_lookahead
#print axioms Erdos66.Compactness.finite_prefix_certificates_iff_lookahead
#print axioms Erdos66.Compactness.lookahead_certificate_iff_count_caps
#print axioms Erdos66.Compactness.finite_prefix_certificates_iff_lookahead_count_caps
#print axioms Erdos66.Compactness.nonzero_limit_iff_finite_prefix_certificates
#print axioms Erdos66.Compactness.nonzero_limit_iff_finset_certificates
#print axioms Erdos66.Compactness.nonzero_limit_iff_lookahead_certificates
#print axioms Erdos66.Compactness.sumRep_le_of_agree_off_finset
#print axioms Erdos66.Compactness.abs_sumRep_sub_le_of_agree_off_finset
#print axioms Erdos66.Compactness.abs_sumRep_sub_le_of_finite_symmDiff
