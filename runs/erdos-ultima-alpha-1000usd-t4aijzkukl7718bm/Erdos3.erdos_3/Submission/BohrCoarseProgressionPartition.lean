import Submission.RestrictedPartialPartition
import Submission.NearLinearProgressionPartition

/-! Complete coarse progression fibers inside a Bohr set. Fibers meeting an
inner Bohr set are retained; the other losses lie in the Bohr boundary or the
terminal incomplete block. -/
namespace Erdos3BohrCoarseProgressionPartition
open Finset Erdos3FiniteBohr Erdos3IntervalProgressionPartition
  Erdos3RestrictedPartialPartition Erdos3ProgressionFiberEquivalence
  Erdos3NearLinearProgressionPartition Erdos3BohrArithmeticProgressions
  Erdos3FinitePartitionIncrement
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def bohrIndices (C : Finset (AddChar G ℂ)) (R : ℝ) (a h : G) (N : ℕ) : Finset (Fin N) :=
  univ.filter (fun k ↦ a+k.val • h ∈ bohr C R)

lemma mem_bohrIndices (C : Finset (AddChar G ℂ)) (R : ℝ) (a h : G) (N : ℕ) (k : Fin N) :
    k ∈ bohrIndices C R a h N ↔ a+k.val • h ∈ bohr C R := by
  simp only [bohrIndices,mem_filter,mem_univ,true_and]

lemma character_index_oscillation (χ : AddChar G ℂ) (a h : G) (b j d : ℕ) :
    ‖χ (a+(b+j*d) • h)-χ (a+b • h)‖ ≤ (j : ℝ)*‖(χ h)^d-1‖ := by
  simpa only [AddChar.map_add_eq_mul,AddChar.map_nsmul_eq_pow] using
    linear_phase_residue_oscillation (χ a) (χ h) (AddChar.norm_apply _ _) (AddChar.norm_apply _ _) b j d

lemma bohr_fiber_whole {N d M : ℕ} (hd : 0 < d) (hM : 0 < M)
    (C : Finset (AddChar G ℂ)) (a h : G) {R η ε : ℝ}
    (hclose : ∀ χ ∈ C, ‖(χ h)^d-1‖ ≤ ε) (hε : 0 ≤ ε) (hmesh : 2*(M : ℝ)*ε ≤ η)
    (x : Fin N) (hx : x ∈ bohrIndices C (R-η) a h N)
    (b : Fin N) (hxb : progressionLabel N d M x = some b) :
    cell (progressionLabel N d M) (some b) ⊆ bohrIndices C R a h N := by
  have hb : (cell (progressionLabel N d M) (some b)).Nonempty :=
    ⟨x,(mem_cell_iff _ _ _).mpr hxb⟩
  obtain ⟨_,hfiber⟩ := progressionLabel_fiber hd hM b hb
  obtain ⟨jx,hjx⟩ := (hfiber x).mp hxb
  intro y hy
  obtain ⟨jy,hjy⟩ := (hfiber y).mp ((mem_cell_iff _ _ _).mp hy)
  apply (mem_bohrIndices _ _ _ _ _ _).mpr
  apply mem_bohr.mpr
  intro χ hχ
  have hχx := mem_bohr.mp ((mem_bohrIndices _ _ _ _ _ _).mp hx) χ hχ
  have hdx : ‖χ (a+x.val • h)-χ (a+b.val • h)‖ ≤ (M : ℝ)*ε := by
    rw [hjx]
    exact (character_index_oscillation χ a h b.val jx.val d).trans
      (mul_le_mul (by exact_mod_cast jx.isLt.le) (hclose χ hχ) (norm_nonneg _) (Nat.cast_nonneg _))
  have hdy : ‖χ (a+y.val • h)-χ (a+b.val • h)‖ ≤ (M : ℝ)*ε := by
    rw [hjy]
    exact (character_index_oscillation χ a h b.val jy.val d).trans
      (mul_le_mul (by exact_mod_cast jy.isLt.le) (hclose χ hχ) (norm_nonneg _) (Nat.cast_nonneg _))
  have hxy := norm_sub_le_norm_sub_add_norm_sub (χ (a+y.val • h)) (χ (a+b.val • h)) (χ (a+x.val • h))
  rw [norm_sub_rev (χ (a+b.val • h)) (χ (a+x.val • h))] at hxy
  have ht := norm_sub_le_norm_sub_add_norm_sub (χ (a+y.val • h)) (χ (a+x.val • h)) 1
  linarith

/-- A single globally selected stride works for every coarse fiber and every
interval length. Restricting to complete fibers of the outer Bohr set loses
only its inner boundary and the terminal incomplete block. -/
theorem bohr_coarse_progression_partition (C : Finset (AddChar G ℂ)) (a h : G)
    (M n : ℕ) (hM : 0 < M) (hn : 0 < n) {R η : ℝ} (hmesh : 4*(M : ℝ)/(n : ℝ) ≤ η) :
    ∃ d : ℕ, 0 < d ∧ d ≤ (2*n+1)^(2*C.card) ∧ ∀ N : ℕ,
      (∀ x ∈ bohrIndices C (R-η) a h N, ∀ b,
        progressionLabel N d M x = some b →
          cell (progressionLabel N d M) (some b) ⊆ bohrIndices C R a h N) ∧
      (cell (restrictLabel (bohrIndices C R a h N) (progressionLabel N d M)) none).card ≤
        (2*n+1)^(2*C.card)*M+
          (bohrIndices C R a h N \ bohrIndices C (R-η) a h N).card := by
  obtain ⟨d,hd,hbound,hclose⟩ := simultaneous_linear_dirichlet
    (fun χ : C ↦ (χ : AddChar G ℂ) h) (fun χ ↦ AddChar.norm_apply _ _) n hn
  have hbound' : d ≤ (2*n+1)^(2*C.card) := by simpa only [Fintype.card_coe] using hbound
  refine ⟨d,hd,hbound',?_⟩
  intro N
  have hwhole : ∀ x ∈ bohrIndices C (R-η) a h N, ∀ b,
      progressionLabel N d M x = some b →
        cell (progressionLabel N d M) (some b) ⊆ bohrIndices C R a h N := by
    intro x hx b hxb
    exact bohr_fiber_whole hd hM C a h (fun χ hχ ↦ hclose ⟨χ,hχ⟩)
      (by positivity : 0 ≤ 2/(n : ℝ)) (by convert hmesh using 1 <;> ring) x hx b hxb
  refine ⟨hwhole,?_⟩
  have hb := restrictLabel_bad_card (bohrIndices C R a h N) (bohrIndices C (R-η) a h N)
    (progressionLabel N d M) hwhole
  rw [progressionLabel_bad_card hd hM] at hb
  apply le_trans ?_ (Nat.add_le_add_right
    ((Nat.mod_lt N (Nat.mul_pos hd hM)).le.trans (Nat.mul_le_mul_right M hbound')) _)
  convert hb using 1
  congr 1
  congr 1
  ext k
  simp only [mem_sdiff]

#print axioms bohr_coarse_progression_partition
end Erdos3BohrCoarseProgressionPartition
