import Submission.Spec

/-!
# Foundational reductions for the extremal function in `Submission.Spec`

These lemmas use only the definition of `Erdos241.f`. They do not establish
or refute the proposed asymptotic: the obstruction below requires an
independent construction producing a fixed-factor cubic excess at
arbitrarily large positive values of `N`.
-/

open Filter Finset
open scoped Asymptotics Topology

namespace Erdos241

/-- The multiset `B_r` property used in the definition of `f`. -/
def IsBrSet (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ m₁ m₂ : Multiset ℕ,
    m₁.card = r → m₂.card = r →
    (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
    m₁.sum = m₂.sum → m₁ = m₂

/-- The empty set is admissible, including when `r = 0`. -/
theorem isBrSet_empty (r : ℕ) : IsBrSet r ∅ := by
  intro m₁ m₂ _ _ h₁ h₂ _
  have hm₁ : m₁ = 0 :=
    Multiset.eq_zero_of_forall_notMem fun x hx ↦ Finset.notMem_empty x (h₁ x hx)
  have hm₂ : m₂ = 0 :=
    Multiset.eq_zero_of_forall_notMem fun x hx ↦ Finset.notMem_empty x (h₂ x hx)
  exact hm₁.trans hm₂.symm

/-- Every admissible subset of `{1, …, N}` gives a lower bound for `f N r`. -/
theorem card_le_f {N r : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Icc 1 N) (hBr : IsBrSet r A) : A.card ≤ f N r := by
  classical
  unfold f
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA, hBr⟩)

/-- The finite supremum in `f` is attained by an admissible set. -/
theorem exists_maximizer (N r : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ IsBrSet r A ∧ A.card = f N r := by
  classical
  let candidates := (Icc 1 N).powerset.filter (IsBrSet r)
  have hnonempty : candidates.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨?_, isBrSet_empty r⟩⟩
    exact Finset.mem_powerset.mpr (Finset.empty_subset _)
  obtain ⟨A, hA, hcard⟩ := candidates.exists_mem_eq_sup hnonempty Finset.card
  obtain ⟨hsub, hBr⟩ := Finset.mem_filter.mp hA
  exact ⟨A, Finset.mem_powerset.mp hsub, hBr, hcard.symm⟩

/-- Enlarging the ambient interval cannot decrease the extremal cardinality. -/
theorem f_monotone (r : ℕ) : Monotone (fun N ↦ f N r) := by
  intro N M hNM
  change f N r ≤ f M r
  obtain ⟨A, hA, hBr, hcard⟩ := exists_maximizer N r
  rw [← hcard]
  refine card_le_f (fun x hx ↦ ?_) hBr
  obtain ⟨hx₁, hxN⟩ := Finset.mem_Icc.mp (hA hx)
  exact Finset.mem_Icc.mpr ⟨hx₁, hxN.trans hNM⟩

/-- The proposed asymptotic forces the normalized cube to tend to one. -/
theorem tendsto_cube_ratio_of_isEquivalent
    (h : (fun N ↦ (f N 3 : ℝ)) ~[atTop]
      (fun N ↦ (N : ℝ) ^ ((1 : ℝ) / 3))) :
    Tendsto (fun N ↦ (f N 3 : ℝ) ^ 3 / (N : ℝ)) atTop (𝓝 1) := by
  have hroot (N : ℕ) : ((N : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (N : ℝ) := by
    simpa only [one_div, Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow (n := 3) (Nat.cast_nonneg (α := ℝ) N) (by decide)
  have hcube : (fun N ↦ (f N 3 : ℝ) ^ 3) ~[atTop] (fun N ↦ (N : ℝ)) := by
    have hp := h.pow 3
    change (fun N ↦ (f N 3 : ℝ) ^ 3) ~[atTop]
      (fun N ↦ ((N : ℝ) ^ ((1 : ℝ) / 3)) ^ 3) at hp
    simpa only [hroot] using hp
  have hne : ∀ᶠ N : ℕ in atTop, (N : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact ne_of_gt (Nat.cast_pos.mpr hN)
  exact (Asymptotics.isEquivalent_iff_tendsto_one hne).mp hcube

/-- Cubic normalization is equivalent to the proposed asymptotic.
The denominator is nonzero eventually, so the value at `N = 0` is irrelevant. -/
theorem isEquivalent_iff_tendsto_cube_ratio :
    ((fun N ↦ (f N 3 : ℝ)) ~[atTop]
      (fun N ↦ (N : ℝ) ^ ((1 : ℝ) / 3))) ↔
    Tendsto (fun N ↦ (f N 3 : ℝ) ^ 3 / (N : ℝ)) atTop (𝓝 1) := by
  constructor
  · exact tendsto_cube_ratio_of_isEquivalent
  · intro h
    have hne : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((1 : ℝ) / 3) ≠ 0 := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
      exact ne_of_gt (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _)
    apply (Asymptotics.isEquivalent_iff_tendsto_one hne).mpr
    have hroot (N : ℕ) :
        ((f N 3 : ℝ) ^ 3 / (N : ℝ)) ^ ((1 : ℝ) / 3) =
          (f N 3 : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [Real.div_rpow (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)]
      congr 1
      simpa only [one_div, Nat.cast_ofNat] using
        Real.pow_rpow_inv_natCast (n := 3) (Nat.cast_nonneg (α := ℝ) (f N 3)) (by decide)
    have ht := h.rpow_const (p := (1 : ℝ) / 3) (Or.inl (one_ne_zero : (1 : ℝ) ≠ 0))
    simpa only [Real.one_rpow, hroot] using ht

/-- A fixed cubic excess at arbitrarily large positive `N` rules out the
proposed asymptotic. This is a conditional obstruction, not a construction
of such an excess. -/
theorem not_isEquivalent_of_cubic_excess {c : ℝ} (hc : 1 < c)
    (hlarge : ∀ M : ℕ, ∃ N : ℕ,
      M ≤ N ∧ 0 < N ∧ c * (N : ℝ) ≤ (f N 3 : ℝ) ^ 3) :
    ¬ ((fun N ↦ (f N 3 : ℝ)) ~[atTop]
      (fun N ↦ (N : ℝ) ^ ((1 : ℝ) / 3))) := by
  intro h
  have hlt := (tendsto_cube_ratio_of_isEquivalent h).eventually (eventually_lt_nhds hc)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hlt
  obtain ⟨N, hMN, hN, hbound⟩ := hlarge M
  have hpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hupper : (f N 3 : ℝ) ^ 3 < c * (N : ℝ) :=
    (div_lt_iff₀ hpos).mp (hM N hMN)
  exact (not_lt_of_ge hbound) hupper

/-- It suffices to produce admissible candidates with a fixed cubic excess
at arbitrarily large positive `N`; their cardinalities are bounded by `f`. -/
theorem not_isEquivalent_of_candidate_cubic_excess {c : ℝ} (hc : 1 < c)
    (hlarge : ∀ M : ℕ, ∃ (N : ℕ) (A : Finset ℕ),
      M ≤ N ∧ 0 < N ∧ A ⊆ Icc 1 N ∧ IsBrSet 3 A ∧
        c * (N : ℝ) ≤ (A.card : ℝ) ^ 3) :
    ¬ ((fun N ↦ (f N 3 : ℝ)) ~[atTop]
      (fun N ↦ (N : ℝ) ^ ((1 : ℝ) / 3))) := by
  apply not_isEquivalent_of_cubic_excess hc
  intro M
  obtain ⟨N, A, hMN, hN, hA, hBr, hbound⟩ := hlarge M
  refine ⟨N, hMN, hN, hbound.trans ?_⟩
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast card_le_f hA hBr) 3

end Erdos241

-- Keep the dependency audit reproducible when this file is compiled.
#print axioms Erdos241.IsBrSet
#print axioms Erdos241.isBrSet_empty
#print axioms Erdos241.card_le_f
#print axioms Erdos241.exists_maximizer
#print axioms Erdos241.f_monotone
#print axioms Erdos241.tendsto_cube_ratio_of_isEquivalent
#print axioms Erdos241.isEquivalent_iff_tendsto_cube_ratio
#print axioms Erdos241.not_isEquivalent_of_cubic_excess
#print axioms Erdos241.not_isEquivalent_of_candidate_cubic_excess
