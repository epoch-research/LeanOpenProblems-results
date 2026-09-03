import Submission.SignedRepairIncidenceExplore

/-! A necessary incidence contrast for density-preserving signed repairs.
Even arbitrary simultaneous deletions and insertions cannot repair persistent
macroscopic deficits while all changed-point midpoint degrees remain nearly
constant. The degree regularity is a hypothesis, not an asserted property
of every candidate or completion. -/
namespace Erdos66SignedRepairStability
open Filter AdditiveCombinatorics Erdos66Counting Erdos66SignedRepairIncidence
  Erdos66UnrestrictedRepairIncidence
open scoped Classical Topology
set_option maxHeartbeats 1800000

/-- No symmetric-difference smallness, monotonicity, finite-exchange, or
point-reuse assumption occurs in this finite-sequence endpoint. -/
theorem same_mass_regular_edits_empty (A B T : ℕ → Finset ℕ) (R L : ℕ → ℝ)
    (a δ β η : ℝ) (hη : 0≤η) (hgap : 2*a*η<δ)
    (hA : Tendsto (fun k ↦ ((A k).card : ℝ)/R k) atTop (𝓝 a))
    (hB : Tendsto (fun k ↦ ((B k).card : ℝ)/R k) atTop (𝓝 a))
    (hdata : ∀ᶠ k in atTop, 0<L k ∧ 0<R k ∧
      (∀ n∈T k, (sumRep (A k : Set ℕ) n : ℝ)+δ*L k ≤ sumRep (B k : Set ℕ) n) ∧
      (∀ x∈B k\A k,
        |R k*midpointDegree (A k) (B k) (T k) x-β*(T k).card*L k| ≤ η*(T k).card*L k) ∧
      (∀ x∈A k\B k,
        |R k*midpointDegree (A k) (B k) (T k) x-β*(T k).card*L k| ≤ η*(T k).card*L k)) :
    ∀ᶠ k in atTop, T k=∅ := by
  have hh : Tendsto (fun k ↦ β*(((B k).card : ℝ)/R k-((A k).card : ℝ)/R k)+
      η*(((A k).card : ℝ)/R k+((B k).card : ℝ)/R k)) atTop (𝓝 (2*a*η)) := by
    convert ((hB.sub hA).const_mul β).add ((hA.add hB).const_mul η) using 1
    ring
  filter_upwards [hdata,hh.eventually (gt_mem_nhds hgap)] with k hk hlt
  by_contra he
  obtain ⟨hL,hR,hg,hF,hD⟩ := hk
  have hT := Finset.nonempty_iff_ne_empty.mpr he
  have hb := normalized_signed_budget (A k) (B k) (T k) hT δ (L k) (R k) β η hL hR hη hg hF hD
  have hnorm : δ ≤ β*(((B k).card : ℝ)/R k-((A k).card : ℝ)/R k)+
      η*(((A k).card : ℝ)/R k+((B k).card : ℝ)/R k) := by
    have hd := (le_div_iff₀ hR).mpr hb
    convert hd using 1 <;> ring
  linarith

/-- Infinite sets are truncated only for exact local accounting. A and B
may differ at infinitely many points, in either direction. -/
theorem same_counting_regular_edits_empty (A B : Set ℕ) (T : ℕ → Finset ℕ)
    (R L : ℕ → ℝ) (a δ β η : ℝ) (hη : 0≤η) (hgap : 2*a*η<δ)
    (hA : Tendsto (fun N ↦ (count A N : ℝ)/R N) atTop (𝓝 a))
    (hB : Tendsto (fun N ↦ (count B N : ℝ)/R N) atTop (𝓝 a))
    (hdata : ∀ᶠ N in atTop, 0<L N ∧ 0<R N ∧
      (∀ n∈T N, n<N) ∧
      (∀ n∈T N, (sumRep A n : ℝ)+δ*L N ≤ sumRep B n) ∧
      (∀ x<N, x∈(B\A)∪(A\B) →
        |R N*midpointDegree (cutoff A N) (cutoff B N) (T N) x-β*(T N).card*L N| ≤
          η*(T N).card*L N)) :
    ∀ᶠ N in atTop, T N=∅ := by
  apply same_mass_regular_edits_empty (fun N ↦ cutoff A N) (fun N ↦ cutoff B N)
    T R L a δ β η hη hgap hA hB
  filter_upwards [hdata] with N hN
  obtain ⟨hL,hR,hT,hg,hd⟩ := hN
  refine ⟨hL,hR,?_,?_,?_⟩
  · intro n hn
    rw [cutoff_sumRep A (hT n hn),cutoff_sumRep B (hT n hn)]
    exact hg n hn
  · intro x hx
    obtain ⟨hxb,hxa⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hx,hxb⟩ := mem_cutoff.mp hxb
    exact hd x hx (Or.inl ⟨hxb,fun ha ↦ hxa (mem_cutoff.mpr ⟨hx,ha⟩)⟩)
  · intro x hx
    obtain ⟨hxa,hxb⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hx,hxa⟩ := mem_cutoff.mp hxa
    exact hd x hx (Or.inr ⟨hxa,fun hb ↦ hxb (mem_cutoff.mpr ⟨hx,hb⟩)⟩)

/-- Persistent deficits force a fixed positive relative incidence contrast
at changed points. The center beta is arbitrary. -/
theorem same_counting_frequent_contrast (A B : Set ℕ) (T : ℕ → Finset ℕ)
    (R L : ℕ → ℝ) (a δ : ℝ) (hδ : 0<δ)
    (hA : Tendsto (fun N ↦ (count A N : ℝ)/R N) atTop (𝓝 a))
    (hB : Tendsto (fun N ↦ (count B N : ℝ)/R N) atTop (𝓝 a))
    (hdata : ∀ᶠ N in atTop, 0<L N ∧ 0<R N ∧ (∀ n∈T N, n<N) ∧
      (∀ n∈T N, (sumRep A n : ℝ)+δ*L N ≤ sumRep B n))
    (hT : ∃ᶠ N in atTop, (T N).Nonempty) :
    ∃ η>0, ∀ β : ℝ, ∃ᶠ N in atTop, ∃ x<N, x∈(B\A)∪(A\B) ∧
      η*(T N).card*L N <
        |R N*midpointDegree (cutoff A N) (cutoff B N) (T N) x-β*(T N).card*L N| := by
  let η := δ/(4*(|a|+1))
  have hd : 0<4*(|a|+1) := by positivity
  have hη : 0<η := div_pos hδ hd
  have hgap : 2*a*η<δ := by
    dsimp [η]
    rw [←mul_div_assoc]
    apply (div_lt_iff₀ hd).mpr
    have ha := le_abs_self a
    nlinarith
  refine ⟨η,hη,fun β ↦ ?_⟩
  by_contra hh
  have hr := not_frequently.mp hh
  have he := same_counting_regular_edits_empty A B T R L a δ β η hη.le hgap hA hB (by
    filter_upwards [hdata,hr] with N hN hbad
    refine ⟨hN.1,hN.2.1,hN.2.2.1,hN.2.2.2,?_⟩
    intro x hx hxAB
    exact le_of_not_gt (fun hlt ↦ hbad ⟨x,hx,hxAB,hlt⟩))
  obtain ⟨N,hN,hNe⟩ := (hT.and_eventually he).exists
  simpa only [hNe,Finset.not_nonempty_empty] using hN

/-- Specialization to a hypothetical logarithmic-limit completion, allowing
unrestricted signed replacement rather than just addition. The base counting
asymptotic is explicit and is not inferred from density-one convergence. -/
theorem same_coefficient_frequent_contrast (A B : Set ℕ) (c : ℝ) (hc : c≠0)
    (hB : Tendsto (fun n ↦ (sumRep B n : ℝ)/Real.log n) atTop (𝓝 c))
    (hA : Tendsto (fun N ↦ (count A N : ℝ)/Real.sqrt ((N : ℝ)*Real.log N))
      atTop (𝓝 (2*Real.sqrt (c/Real.pi))))
    (T : ℕ → Finset ℕ) (δ : ℝ) (hδ : 0<δ)
    (hdata : ∀ᶠ N in atTop, (∀ n∈T N, n<N) ∧
      (∀ n∈T N, (sumRep A n : ℝ)+δ*Real.log N ≤ sumRep B n))
    (hT : ∃ᶠ N in atTop, (T N).Nonempty) :
    ∃ η>0, ∀ β : ℝ, ∃ᶠ N in atTop, ∃ x<N, x∈(B\A)∪(A\B) ∧
      η*(T N).card*Real.log N <
        |Real.sqrt ((N : ℝ)*Real.log N)*
          midpointDegree (cutoff A N) (cutoff B N) (T N) x-β*(T N).card*Real.log N| := by
  apply same_counting_frequent_contrast A B T
    (fun N ↦ Real.sqrt ((N : ℝ)*Real.log N)) (fun N ↦ Real.log N)
    (2*Real.sqrt (c/Real.pi)) δ hδ hA
    (Erdos66TauberianProfile.witness_counting_profile hc hB) _ hT
  filter_upwards [hdata,eventually_ge_atTop 2] with N hN hN2
  have hNr : (1 : ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hlog : 0<Real.log (N : ℝ) := Real.log_pos hNr
  exact ⟨hlog,Real.sqrt_pos.mpr (mul_pos (by linarith) hlog),hN⟩

end Erdos66SignedRepairStability
