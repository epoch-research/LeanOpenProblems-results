import Submission.IntegerPaletteSlicesExplore

/-! A prefix-balanced finite cyclic palette can be clipped and read in a
smaller modulus. Integer membership is retained, and both wrap terms are
included. This is not an infinite changing-palette construction. -/
namespace Erdos66ClippedModulus
open Erdos66IntegerPaletteSlices Erdos66OuterMixedPrefix Erdos66OuterCarryProfile
  Erdos66NatPairAlgebra Erdos66SaturatingCyclicFamily
open scoped Classical
set_option maxHeartbeats 2000000

variable (M : ℕ) [NeZero M]

lemma prefix_two_integer_counts (C D : Finset (ZMod M)) (z : ZMod M)
    (u : ℕ) (hu : u ≤ M) :
    prefixCount M C D z u =
      pairs (slice M C 0 u) (slice M D 0 M) z.val+
      pairs (slice M C 0 u) (slice M D 0 M) (z.val+M) := by
  rw [pairs_slice_formula M C D 0 u 0 M _ le_rfl,
    pairs_slice_formula M C D 0 u 0 M _ le_rfl]
  have hz := ZMod.val_lt z
  have h₁ : cutLo 0 u 0 M z.val=0 := by unfold cutLo cutHi; omega
  have h₂ : cutHi u 0 z.val=min u (z.val+1) := by simp [cutHi]
  have h₃ : cutLo 0 u 0 M (z.val+M)=min u (z.val+1) := by unfold cutLo cutHi; omega
  have h₄ : cutHi u 0 (z.val+M)=u := by unfold cutHi; omega
  simp only [h₁,h₂,h₃,h₄,Nat.cast_add,ZMod.natCast_self,add_zero,ZMod.natCast_zmod_val]
  have he : intervalCount M C D z 0 (min u (z.val+1)) =
      prefixCount M C D z (min u (z.val+1)) := by
    simp [intervalCount,prefixCount]
  rw [he,add_comm]
  exact (intervalCount_add_prefix M C D z _ u (min_le_left _ _)).symm

variable (L : ℕ) [NeZero L]

/-- Retain the actual first M membership bits and reinterpret them cyclically. -/
noncomputable def rebase (C : Finset (ZMod L)) : Finset (ZMod M) :=
  Finset.univ.filter (fun z ↦ (z.val : ZMod L) ∈ C)

lemma mem_rebase (C : Finset (ZMod L)) (z : ZMod M) :
    z∈rebase M L C ↔ (z.val : ZMod L)∈C := by simp [rebase]

lemma slice_rebase (hML : M ≤ L) (C : Finset (ZMod L))
    (u : ℕ) (hu : u ≤ M) :
    slice M (rebase M L C) 0 u = slice L C 0 u := by
  ext a
  simp only [mem_slice,mem_rebase]
  by_cases ha : a<u
  · have haM : a<M := ha.trans_le hu
    have haL : a<L := haM.trans_le hML
    simp only [haM,haL,ha,Nat.zero_le,true_and,ZMod.val_natCast_of_lt haM]
  · simp [ha]

lemma rebase_prefix_identity (hML : M ≤ L) (C D : Finset (ZMod L))
    (z : ZMod M) (u : ℕ) (hu : u ≤ M) :
    prefixCount M (rebase M L C) (rebase M L D) z u =
      pairs (slice L C 0 u) (slice L D 0 M) z.val+
      pairs (slice L C 0 u) (slice L D 0 M) (z.val+M) := by
  rw [prefix_two_integer_counts M _ _ z u hu,
    slice_rebase M L hML C u hu,slice_rebase M L hML D M le_rfl]

lemma two_overlap_lengths (z u : ℕ) (hz : z<M) (hu : u ≤ M) :
    ((cutHi u 0 z:ℝ)-cutLo 0 u 0 M z)+
      ((cutHi u 0 (z+M):ℝ)-cutLo 0 u 0 M (z+M))=u := by
  have h₁ : cutLo 0 u 0 M z=0 := by unfold cutLo cutHi; omega
  have h₂ : cutHi u 0 z=min u (z+1) := by simp [cutHi]
  have h₃ : cutLo 0 u 0 M (z+M)=min u (z+1) := by unfold cutLo cutHi; omega
  have h₄ : cutHi u 0 (z+M)=u := by unfold cutHi; omega
  simp only [h₁,h₂,h₃,h₄,Nat.cast_zero]
  ring

/-- Every endpoint-prefix bound transfers to the smaller modulus, with its
correct absolute normalization u/L and only four times the old error. -/
theorem rebase_prefix_error (hML : M ≤ L) (C D : Finset (ZMod L)) (η : ℝ)
    (hprefix : ∀ z u, u ≤ L →
      |(prefixCount L C D z u:ℝ)-(u:ℝ)/L*actualMean L C D| ≤ η*actualMean L C D)
    (z : ZMod M) (u : ℕ) (hu : u ≤ M) :
    |(prefixCount M (rebase M L C) (rebase M L D) z u:ℝ)-
      (u:ℝ)/L*actualMean L C D| ≤ 4*η*actualMean L C D := by
  have h₁ := pairs_slice_error L C D 0 u 0 M z.val (hu.trans hML) hML η hprefix
  have h₂ := pairs_slice_error L C D 0 u 0 M (z.val+M) (hu.trans hML) hML η hprefix
  have hlength := two_overlap_lengths M z.val u (ZMod.val_lt z) hu
  have he : (((cutHi u 0 z.val:ℝ)-cutLo 0 u 0 M z.val)/L)*actualMean L C D+
      (((cutHi u 0 (z.val+M):ℝ)-cutLo 0 u 0 M (z.val+M))/L)*actualMean L C D=
      (u:ℝ)/L*actualMean L C D := by
    rw [←add_mul,←add_div,hlength]
  rw [rebase_prefix_identity M L hML C D z u hu,Nat.cast_add,←he]
  have htri := abs_add_le
    ((pairs (slice L C 0 u) (slice L D 0 M) z.val:ℝ)-
      (((cutHi u 0 z.val:ℝ)-cutLo 0 u 0 M z.val)/L)*actualMean L C D)
    ((pairs (slice L C 0 u) (slice L D 0 M) (z.val+M):ℝ)-
      (((cutHi u 0 (z.val+M):ℝ)-cutLo 0 u 0 M (z.val+M))/L)*actualMean L C D)
  have hid :
      (pairs (slice L C 0 u) (slice L D 0 M) z.val:ℝ)+
      pairs (slice L C 0 u) (slice L D 0 M) (z.val+M)-
      ((((cutHi u 0 z.val:ℝ)-cutLo 0 u 0 M z.val)/L)*actualMean L C D+
      (((cutHi u 0 (z.val+M):ℝ)-cutLo 0 u 0 M (z.val+M))/L)*actualMean L C D)=
      ((pairs (slice L C 0 u) (slice L D 0 M) z.val:ℝ)-
      (((cutHi u 0 z.val:ℝ)-cutLo 0 u 0 M z.val)/L)*actualMean L C D)+
      ((pairs (slice L C 0 u) (slice L D 0 M) (z.val+M):ℝ)-
      (((cutHi u 0 (z.val+M):ℝ)-cutLo 0 u 0 M (z.val+M))/L)*actualMean L C D) := by ring
  rw [hid]
  exact htri.trans (by nlinarith only [h₁,h₂])

/-- In particular all mixed cyclic totals survive the change of modulus. -/
theorem rebase_cyclic_error (hML : M ≤ L) (C D : Finset (ZMod L)) (η : ℝ)
    (hprefix : ∀ z u, u ≤ L →
      |(prefixCount L C D z u:ℝ)-(u:ℝ)/L*actualMean L C D| ≤ η*actualMean L C D)
    (z : ZMod M) :
    |(cyclicCount M (rebase M L C) (rebase M L D) z:ℝ)-
      (M:ℝ)/L*actualMean L C D| ≤ 4*η*actualMean L C D := by
  have hh := rebase_prefix_error M L hML C D η hprefix z M le_rfl
  have he : prefixCount M (rebase M L C) (rebase M L D) z M=
      cyclicCount M (rebase M L C) (rebase M L D) z := by
    simp only [prefixCount,cyclicCount,ZMod.val_lt,true_and]
  rwa [he] at hh


lemma rebase_mono {C D : Finset (ZMod L)} (hCD : C ⊆ D) :
    rebase M L C ⊆ rebase M L D := by
  intro z hz
  exact (mem_rebase M L D z).mpr (hCD ((mem_rebase M L C z).mp hz))

lemma rebase_univ : rebase M L (Finset.univ : Finset (ZMod L))=Finset.univ := by
  ext z
  simp [mem_rebase]

/-- Normalize the clipped estimates to their new actual cardinality mean.
The half-size condition bounds the normalization loss, not the carry geometry. -/
theorem rebase_prefix_actual_error (hML : M ≤ L) (hLM : L ≤ 2*M)
    (C D : Finset (ZMod L)) (η : ℝ) (hη : 0 ≤ η) (hη16 : η ≤ 1/16)
    (hprefix : ∀ z u, u ≤ L →
      |(prefixCount L C D z u:ℝ)-(u:ℝ)/L*actualMean L C D| ≤ η*actualMean L C D)
    (z : ZMod M) (u : ℕ) (hu : u ≤ M) :
    |(prefixCount M (rebase M L C) (rebase M L D) z u:ℝ)-
      (u:ℝ)/M*actualMean M (rebase M L C) (rebase M L D)| ≤
      32*η*actualMean M (rebase M L C) (rebase M L D) := by
  let μ := actualMean L C D
  let ν := actualMean M (rebase M L C) (rebase M L D)
  have hμ : 0 ≤ μ := actualMean_nonneg L C D
  have hm : (0:ℝ)<M := by exact_mod_cast NeZero.pos M
  have hl : (0:ℝ)<L := by exact_mod_cast NeZero.pos L
  have hhalf : (1:ℝ)/2 ≤ (M:ℝ)/L := by
    apply (le_div_iff₀ hl).mpr
    have hh : (L:ℝ) ≤ 2*M := by exact_mod_cast hLM
    linarith
  have hmean : |ν-(M:ℝ)/L*μ| ≤ 4*η*μ :=
    actualMean_error M _ _ _ _ (rebase_cyclic_error M L hML C D η hprefix)
  have hscale : μ ≤ 4*ν := by
    have hh := (abs_le.mp hmean).1
    have h₁ := mul_le_mul_of_nonneg_right hhalf hμ
    have h₂ := mul_le_mul_of_nonneg_right hη16 hμ
    nlinarith only [hh,h₁,h₂]
  have hu0 : (0:ℝ) ≤ (u:ℝ)/M := by positivity
  have hu1 : (u:ℝ)/M ≤ 1 := (div_le_one hm).mpr (by exact_mod_cast hu)
  have hp := rebase_prefix_error M L hML C D η hprefix z u hu
  have hcost : |(u:ℝ)/L*μ-(u:ℝ)/M*ν| ≤ 4*η*μ := by
    have he : (u:ℝ)/L*μ-(u:ℝ)/M*ν=(u:ℝ)/M*((M:ℝ)/L*μ-ν) := by field_simp
    rw [he,abs_mul,abs_of_nonneg hu0,abs_sub_comm]
    exact (mul_le_mul_of_nonneg_left hmean hu0).trans
      (by nlinarith only [mul_le_mul_of_nonneg_right hu1 (show 0 ≤ 4*η*μ by positivity)])
  have hh := abs_sub_le
    (prefixCount M (rebase M L C) (rebase M L D) z u:ℝ) ((u:ℝ)/L*μ) ((u:ℝ)/M*ν)
  have hfinal := mul_le_mul_of_nonneg_left hscale hη
  change |(prefixCount M (rebase M L C) (rebase M L D) z u:ℝ)-(u:ℝ)/M*ν| ≤ 32*η*ν
  nlinarith only [hh,hp,hcost,hfinal]

end Erdos66ClippedModulus

