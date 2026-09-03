import FormalConjecturesUtil

/-! A topological reformulation of the unresolved prime-pair covering problem. -/
namespace Erdos972Topology

def primeSet (α : ℝ) : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ Nat.Prime ⌊α * p⌋₊}

/-- Slopes admitting a prime pair beyond a given denominator bound, with strict margins. -/
def primeTail (N : ℕ) : Set ℝ :=
  {α | ∃ p q : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime q ∧
    (q : ℝ) < α * p ∧ α * p < (q : ℝ) + 1}

/-- Each finite-bound prime-pair condition is open in the slope. -/
theorem isOpen_primeTail (N : ℕ) : IsOpen (primeTail N) := by
  rw [isOpen_iff_mem_nhds]
  rintro α ⟨p, q, hNp, hp, hq, hlo, hhi⟩
  have ho : IsOpen ((fun x : ℝ => x * p) ⁻¹' Set.Ioo (q : ℝ) (q + 1)) :=
    isOpen_Ioo.preimage (continuous_id.mul continuous_const)
  apply Filter.mem_of_superset (ho.mem_nhds ⟨hlo, hhi⟩)
  intro β hβ
  exact ⟨p, q, hNp, hp, hq, hβ.1, hβ.2⟩

/-- For irrational nonnegative slopes the open covering condition is exact. -/
theorem infinite_iff_mem_all_primeTail {α : ℝ} (hα : 0 ≤ α) (hI : Irrational α) :
    (primeSet α).Infinite ↔ ∀ N : ℕ, α ∈ primeTail N := by
  rw [Set.infinite_iff_exists_gt]
  constructor
  · intro h N
    obtain ⟨p, hp, hNp⟩ := h N
    refine ⟨p, ⌊α * p⌋₊, hNp, hp.1, hp.2, ?_, Nat.lt_floor_add_one _⟩
    exact lt_of_le_of_ne (Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg p)))
      ((hI.mul_natCast hp.1.ne_zero).ne_nat _).symm
  · intro h N
    obtain ⟨p, q, hNp, hp, hq, hlo, hhi⟩ := h N
    refine ⟨p, ⟨hp, ?_⟩, hNp⟩
    have hf : ⌊α * p⌋₊ = q :=
      (Nat.floor_eq_iff (mul_nonneg hα (Nat.cast_nonneg p))).mpr ⟨hlo.le, hhi⟩
    simpa only [hf] using hq

/-- The tails form a decreasing family of open sets. -/
theorem primeTail_antitone : Antitone primeTail := by
  intro N M hNM α hα
  obtain ⟨p, q, hMp, hp, hq, hlo, hhi⟩ := hα
  exact ⟨p, q, hNM.trans_lt hMp, hp, hq, hlo, hhi⟩

/-- The set satisfying every strict prime-pair condition is a G-delta set. -/
theorem isGδ_all_primeTail : IsGδ (⋂ N : ℕ, primeTail N) :=
  IsGδ.iInter (fun N => (isOpen_primeTail N).isGδ)

/-- A disproof is exactly an irrational point above one in one of the closed complements. -/
theorem negation_iff_closed_exception :
    (¬ (∀ α > 1, Irrational α → (primeSet α).Infinite)) ↔
      ∃ N : ℕ, ∃ α : ℝ, 1 < α ∧ Irrational α ∧ α ∈ (primeTail N)ᶜ := by
  classical
  constructor
  · intro h
    push_neg at h
    obtain ⟨α, hα, hI, hf⟩ := h
    have hn : ¬ ∀ N, α ∈ primeTail N := by
      intro ha
      exact ((infinite_iff_mem_all_primeTail (by linarith) hI).mpr ha) hf
    push_neg at hn
    obtain ⟨N, hN⟩ := hn
    exact ⟨N, α, hα, hI, hN⟩
  · rintro ⟨N, α, hα, hI, hN⟩ h
    exact hN ((infinite_iff_mem_all_primeTail (by linarith) hI).mp (h α hα hI) N)

/-- The sets in the counterexample criterion really are closed. -/
theorem isClosed_primeTail_compl (N : ℕ) : IsClosed (primeTail N)ᶜ :=
  (isOpen_primeTail N).isClosed_compl

/-- Integer slopes lie on excluded boundaries of all the strict prime-pair intervals. -/
theorem natCast_not_mem_primeTail (a N : ℕ) : (a : ℝ) ∉ primeTail N := by
  rintro ⟨p, q, _, _, _, hlo, hhi⟩
  have hlo' : q < a * p := by exact_mod_cast hlo
  have hhi' : a * p < q + 1 := by exact_mod_cast hhi
  omega

/-- A prime-pair window with both a lower and an upper denominator bound. -/
def primeWindow (N M : ℕ) : Set ℝ :=
  {α | ∃ p q : ℕ, N < p ∧ p ≤ M ∧ Nat.Prime p ∧ Nat.Prime q ∧
    (q : ℝ) < α * p ∧ α * p < (q : ℝ) + 1}

theorem isOpen_primeWindow (N M : ℕ) : IsOpen (primeWindow N M) := by
  rw [isOpen_iff_mem_nhds]
  rintro α ⟨p, q, hNp, hpM, hp, hq, hlo, hhi⟩
  have ho : IsOpen ((fun x : ℝ => x * p) ⁻¹' Set.Ioo (q : ℝ) (q + 1)) :=
    isOpen_Ioo.preimage (continuous_id.mul continuous_const)
  apply Filter.mem_of_superset (ho.mem_nhds ⟨hlo, hhi⟩)
  intro β hβ
  exact ⟨p, q, hNp, hpM, hp, hq, hβ.1, hβ.2⟩

/-- A compact set covered by a prime tail has a uniform finite prime bound. -/
theorem compact_tail_uniform {K : Set ℝ} (hK : IsCompact K) (N : ℕ)
    (hcover : K ⊆ primeTail N) :
    ∃ M : ℕ, ∀ α ∈ K, ∃ p : ℕ, N < p ∧ p ≤ M ∧ p ∈ primeSet α := by
  classical
  have hc : K ⊆ ⋃ M : ℕ, primeWindow N M := by
    intro α hα
    obtain ⟨p, q, hNp, hp, hq, hlo, hhi⟩ := hcover hα
    exact Set.mem_iUnion.mpr ⟨p, p, q, hNp, le_rfl, hp, hq, hlo, hhi⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover (primeWindow N) (isOpen_primeWindow N) hc
  refine ⟨F.sup id, ?_⟩
  intro α hα
  obtain ⟨M, hMF⟩ := Set.mem_iUnion.mp (hF hα)
  obtain ⟨hM, p, q, hNp, hpM, hp, hq, hlo, hhi⟩ := Set.mem_iUnion.mp hMF
  refine ⟨p, hNp, hpM.trans (Finset.le_sup (f := id) hM), hp, ?_⟩
  have hf : ⌊α * p⌋₊ = q := (Nat.floor_eq_iff' hq.ne_zero).mpr ⟨hlo.le, hhi⟩
  simpa only [hf] using hq

/-- The original assertion is equivalent to uniform finite bounds on each compact
set made entirely of admissible irrational slopes. -/
theorem conjecture_iff_compact_uniform :
    (∀ α > 1, Irrational α → (primeSet α).Infinite) ↔
      ∀ K : Set ℝ, IsCompact K →
        (∀ α ∈ K, 1 < α ∧ Irrational α) →
          ∀ N : ℕ, ∃ M : ℕ, ∀ α ∈ K,
            ∃ p : ℕ, N < p ∧ p ≤ M ∧ p ∈ primeSet α := by
  constructor
  · intro hC K hK hKI N
    apply compact_tail_uniform hK N
    intro α hα
    obtain ⟨ha, hI⟩ := hKI α hα
    exact (infinite_iff_mem_all_primeTail (by linarith) hI).mp (hC α ha hI) N
  · intro hU α hα hI
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨M, hM⟩ := hU {α} isCompact_singleton (by simpa using And.intro hα hI) N
    obtain ⟨p, hNp, _, hp⟩ := hM α (Set.mem_singleton α)
    exact ⟨p, hp, hNp⟩

/-- Arbitrarily long finite gaps would disprove the conjecture if the slopes could
be kept inside one compact set consisting entirely of admissible irrationals. -/
theorem disproof_of_compact_gaps {K : Set ℝ} (hK : IsCompact K)
    (hKI : ∀ α ∈ K, 1 < α ∧ Irrational α) (N : ℕ)
    (hgap : ∀ M : ℕ, ∃ α ∈ K, ∀ p : ℕ, N < p → p ≤ M → p ∉ primeSet α) :
    ¬ (∀ α > 1, Irrational α → (primeSet α).Infinite) := by
  intro hC
  obtain ⟨M, hM⟩ := conjecture_iff_compact_uniform.mp hC K hK hKI N
  obtain ⟨α, hα, ha⟩ := hgap M
  obtain ⟨p, hNp, hpM, hp⟩ := hM α hα
  exact ha p hNp hpM hp

#print axioms infinite_iff_mem_all_primeTail
#print axioms negation_iff_closed_exception
#print axioms isGδ_all_primeTail
#print axioms conjecture_iff_compact_uniform
#print axioms disproof_of_compact_gaps
end Erdos972Topology
