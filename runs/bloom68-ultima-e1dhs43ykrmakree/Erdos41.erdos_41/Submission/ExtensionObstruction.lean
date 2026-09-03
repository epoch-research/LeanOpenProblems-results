import Submission.FlagExamples

/-!
# A small balanced prefix with no extension

The obstruction is specific to four-element restricted-B3 sets, which need not
be restricted-B2. It does not address extension of prefixes of size at least five.
-/

namespace Work

def deadFlag : Fin 4 → ℕ := ![1, 2, 3, 4]

theorem deadFlag_strictMono : StrictMono deadFlag := by decide

theorem deadFlag_triples : NtupleCondition (Set.range deadFlag) 3 := by
  have hRange : Set.range deadFlag =
      (↑((Finset.univ : Finset (Fin 4)).image deadFlag) : Set ℕ) := by
    ext a
    simp
  rw [hRange]
  apply ntupleCondition_of_sum_injOn_powersetCard
  decide

theorem deadFlag_cubic_bound {K : ℕ} (hK : 1 ≤ K) (i : Fin 4) :
    deadFlag i ≤ K * (i.val + 1)^3 := by
  have h : deadFlag i ≤ 1 * (i.val + 1)^3 := by
    have hall : ∀ j : Fin 4, deadFlag j ≤ 1 * (j.val + 1)^3 := by decide
    exact hall i
  exact h.trans (Nat.mul_le_mul_right _ hK)

theorem finiteCubicFlag_dead_four {K : ℕ} (hK : 1 ≤ K) : FiniteCubicFlag K 4 :=
  ⟨deadFlag, deadFlag_strictMono, deadFlag_cubic_bound hK, deadFlag_triples⟩

/-- Every fifth point beyond this prefix gives a forbidden equality of triple-subset sums. -/
theorem deadFlag_no_extension {A : Set ℕ}
    (hPrefix : Set.range deadFlag ⊆ A) {x : ℕ} (hxA : x ∈ A) (hx : 4 < x) :
    ¬ NtupleCondition A 3 := by
  intro hTriple
  have h1 : 1 ∈ A := hPrefix ⟨0, rfl⟩
  have h2 : 2 ∈ A := hPrefix ⟨1, rfl⟩
  have h3 : 3 ∈ A := hPrefix ⟨2, rfl⟩
  have h4 : 4 ∈ A := hPrefix ⟨3, rfl⟩
  have hx1 : x ≠ 1 := by omega
  have hx2 : x ≠ 2 := by omega
  have hx3 : x ≠ 3 := by omega
  have hx4 : x ≠ 4 := by omega
  have heq : ({1, 4, x} : Finset ℕ) = {2, 3, x} := by
    apply hTriple
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a ha
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> assumption
    · intro a ha
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl <;> assumption
    · simp [Ne.symm hx1, Ne.symm hx4]
    · simp [Ne.symm hx2, Ne.symm hx3]
    · simp [Ne.symm hx1, Ne.symm hx2, Ne.symm hx3, Ne.symm hx4]
      omega
  have hmem : 1 ∈ ({2, 3, x} : Finset ℕ) := heq ▸ (by simp)
  simp [Ne.symm hx1] at hmem

end Work

#print axioms Work.finiteCubicFlag_dead_four
#print axioms Work.deadFlag_no_extension
