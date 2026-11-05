import Submission.DigitColors
import Submission.PairedCore

/-!
# Color-oriented residue pairs

The two sides are intersections of opposite congruence classes with the
fixed global prime-digit colors.  Consequently all pairs at one prime
are coherently oriented, even before empty or self-opposite pairs are
removed.  No injectivity assumption on the vertex labels is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos126Aux.ResidueBlocks

variable {ι : Type*} [Fintype ι]

noncomputable def leftClass (a : ι → ℕ) (p k r : ℕ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => a i ≡ r [MOD p ^ k] ∧ primeColor p (a i) = true)

noncomputable def rightClass (a : ι → ℕ) (p k r : ℕ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => p ^ k ∣ a i + r ∧ primeColor p (a i) = false)

noncomputable def block (a : ι → ℕ) (p k r : ℕ) : Paired.Block ι where
  left := leftClass a p k r
  right := rightClass a p k r
  weight := Real.log (p : ℝ)

def Active (a : ι → ℕ) (p k r : ℕ) : Prop :=
  (leftClass a p k r).Nonempty ∧ (rightClass a p k r).Nonempty ∧ ¬p ^ k ∣ 2 * r

@[simp] theorem mem_leftClass (a : ι → ℕ) (p k r : ℕ) (i : ι) :
    i ∈ leftClass a p k r ↔ a i ≡ r [MOD p ^ k] ∧ primeColor p (a i) = true := by
  classical
  simp [leftClass]

@[simp] theorem mem_rightClass (a : ι → ℕ) (p k r : ℕ) (i : ι) :
    i ∈ rightClass a p k r ↔ p ^ k ∣ a i + r ∧ primeColor p (a i) = false := by
  classical
  simp [rightClass]

@[simp] theorem block_left (a : ι → ℕ) (p k r : ℕ) :
    (block a p k r).left = leftClass a p k r := rfl

@[simp] theorem block_right (a : ι → ℕ) (p k r : ℕ) :
    (block a p k r).right = rightClass a p k r := rfl

@[simp] theorem block_weight (a : ι → ℕ) (p k r : ℕ) :
    (block a p k r).weight = Real.log (p : ℝ) := rfl

theorem left_right_disjoint (a : ι → ℕ) (p k r l s : ℕ) (i : ι)
    (hi : i ∈ leftClass a p k r) : i ∉ rightClass a p l s := by
  intro hj
  have h := (mem_leftClass a p k r i).1 hi
  have h' := (mem_rightClass a p l s i).1 hj
  rw [h.2] at h'
  exact Bool.noConfusion h'.2

theorem block_valid (a : ι → ℕ) (p k r : ℕ) (h : Active a p k r) :
    (block a p k r).Valid := by
  refine ⟨h.1, h.2.1, ?_, Real.log_natCast_nonneg p⟩
  intro i hi
  exact left_right_disjoint a p k r k r i hi

private theorem nested_of_residue (a : ι → ℕ) (p k r l s : ℕ)
    (hkl : k ≤ l) (hsr : s ≡ r [MOD p ^ k]) :
    leftClass a p l s ⊆ leftClass a p k r ∧
      rightClass a p l s ⊆ rightClass a p k r := by
  have hd : p ^ k ∣ p ^ l := pow_dvd_pow p hkl
  constructor
  · intro i hi
    obtain ⟨hm, hc⟩ := (mem_leftClass a p l s i).1 hi
    exact (mem_leftClass a p k r i).2 ⟨(hm.of_dvd hd).trans hsr, hc⟩
  · intro i hi
    obtain ⟨hm, hc⟩ := (mem_rightClass a p l s i).1 hi
    have hz : a i + r ≡ 0 [MOD p ^ k] :=
      (hsr.add_left (a i)).symm.trans ((hd.trans hm).modEq_zero_nat)
    exact (mem_rightClass a p k r i).2 ⟨Nat.modEq_zero_iff_dvd.1 hz, hc⟩

private theorem nested_or_disjoint_of_le (a : ι → ℕ) (p k r l s : ℕ)
    (hkl : k ≤ l) :
    (leftClass a p l s ⊆ leftClass a p k r ∧
      rightClass a p l s ⊆ rightClass a p k r) ∨
    (∀ i, (i ∈ leftClass a p k r ∨ i ∈ rightClass a p k r) →
      i ∉ leftClass a p l s ∧ i ∉ rightClass a p l s) := by
  classical
  by_cases h : ∃ i, (i ∈ leftClass a p k r ∨ i ∈ rightClass a p k r) ∧
      (i ∈ leftClass a p l s ∨ i ∈ rightClass a p l s)
  · obtain ⟨i, hi, hj⟩ := h
    left
    apply nested_of_residue a p k r l s hkl
    have hd : p ^ k ∣ p ^ l := pow_dvd_pow p hkl
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact (((mem_leftClass a p l s i).1 hj).1.of_dvd hd).symm.trans
        ((mem_leftClass a p k r i).1 hi).1
    · exact False.elim (left_right_disjoint a p k r l s i hi hj)
    · exact False.elim (left_right_disjoint a p l s k r i hj hi)
    · have hr := ((mem_rightClass a p k r i).1 hi).1.modEq_zero_nat
      have hs := (hd.trans ((mem_rightClass a p l s i).1 hj).1).modEq_zero_nat
      exact (hs.trans hr.symm).add_left_cancel' (a i)
  · right
    intro i hi
    exact ⟨fun hj => h ⟨i, hi, Or.inl hj⟩, fun hj => h ⟨i, hi, Or.inr hj⟩⟩

/-- Prime-wise strong laminarity, with simultaneous containment on both
oriented sides.  This does not require either pair to be occupied. -/
theorem block_compatible (a : ι → ℕ) (p k r l s : ℕ) :
    ((block a p k r).left ⊆ (block a p l s).left ∧
      (block a p k r).right ⊆ (block a p l s).right) ∨
    ((block a p l s).left ⊆ (block a p k r).left ∧
      (block a p l s).right ⊆ (block a p k r).right) ∨
    (∀ i, (i ∈ (block a p k r).left ∨ i ∈ (block a p k r).right) →
      i ∉ (block a p l s).left ∧ i ∉ (block a p l s).right) := by
  rcases le_total k l with hkl | hlk
  · rcases nested_or_disjoint_of_le a p k r l s hkl with hn | hd
    · exact Or.inr (Or.inl hn)
    · exact Or.inr (Or.inr hd)
  · rcases nested_or_disjoint_of_le a p l s k r hlk with hn | hd
    · exact Or.inl hn
    · right; right
      intro i hi
      exact ⟨fun hj => hi.elim (hd i (Or.inl hj)).1 (hd i (Or.inl hj)).2,
        fun hj => hi.elim (hd i (Or.inr hj)).1 (hd i (Or.inr hj)).2⟩

end Erdos126Aux.ResidueBlocks
