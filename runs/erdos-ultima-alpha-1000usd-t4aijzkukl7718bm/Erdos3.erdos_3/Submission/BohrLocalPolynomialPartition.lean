import Submission.LocalHigherProgressionPartition
import Submission.RetainedProgressionAssembly
import Submission.ZModBohrIndices

/-! Higher-degree flat progression partitions on retained fibers and stable
Bohr domains. Every exceptional-mass and natural-stride cost is explicit. -/
namespace Erdos3BohrLocalPolynomialPartition
open Finset Erdos3LocalHigherProgressionPartition Erdos3HigherPartitionParameters
  Erdos3HigherPhaseDifferences Erdos3HigherLocalPolynomialProgressions
  Erdos3RetainedProgressionAssembly Erdos3RestrictedPartialPartition
  Erdos3ProgressionFiberEquivalence Erdos3IntervalProgressionPartition
  Erdos3FinitePartitionIncrement Erdos3MaskedPhaseIncrement
  Erdos3BohrCoarseProgressionPartition Erdos3FiniteBohr Erdos3ZModBohrIndices
  Erdos3RelativeStableBohr Erdos3BohrCovering
open scoped BigOperators Classical
set_option maxHeartbeats 5000000
set_option maxRecDepth 3000

variable {G I : Type*} [AddCommGroup G] [Fintype I]

/-- Refine every complete retained coarse fiber, without losing conditional mass. -/
theorem subset_local_polynomial_partition (R : Set G) (k : ℕ) (f : I → G → Additive Circle)
    (hf : ∀ i, IsLocallyPolynomial R k (f i)) (a h : G)
    (N K L s d₀ : ℕ) (hL : 0 < L) (hd₀ : 0 < d₀)
    (hK : higherPartitionThreshold k (Fintype.card I) L s ≤ K)
    (B : Finset (Fin N)) (hB : B.Nonempty) (hBR : ∀ x ∈ B, a+x.val • h ∈ R) :
    ∃ c : B → Option (Fin N × Fin K), ∃ w : I → (Fin N × Fin K) → ℂ,
      (∀ i j, ‖w i j‖ = 1) ∧
      cellMass c none ≤ cellMass (restrictLabel B (progressionLabel N d₀ K)) none+(1/2 : ℝ)^s ∧
      (∀ x j, c x = some j → ∀ i, ‖phase (f i (a+x.val.val • h))-w i j‖ ≤ (1/2 : ℝ)^s) ∧
      ∀ j, (cell c (some j)).Nonempty →
        ∃ b d : ℕ, 0 < d ∧ d ≤ higherPartitionStride k (Fintype.card I) L s*d₀ ∧
          (∀ n < L, ∃ x : B, x.val.val = b+n*d) ∧
          ∀ x : B, c x = some j ↔ ∃ n : Fin L, x.val.val = b+n.val*d := by
  have hK0 : 0 < K := (higherPartitionThreshold_pos k (Fintype.card I) L s hL).trans_le hK
  let D := higherPartitionStride k (Fintype.card I) L s
  have hlocal (b : Fin N) :
      ∃ c : Fin K → Option (Fin K), ∃ w : I → Fin K → ℂ,
        (∀ i j, ‖w i j‖ = 1) ∧
        ((cell (restrictLabel B (progressionLabel N d₀ K)) (some b)).Nonempty →
          cellMass c none ≤ (1/2 : ℝ)^s ∧
          (∀ x j, c x = some j → ∀ i,
            ‖phase (f i ((a+b.val • h)+x.val • (d₀ • h)))-w i j‖ ≤ (1/2 : ℝ)^s) ∧
          ∀ j, (cell c (some j)).Nonempty →
            ∃ b d : ℕ, 0 < d ∧ d ≤ D ∧ (∀ n < L, b+n*d < K) ∧
              ∀ x : Fin K, c x = some j ↔ ∃ n : Fin L, x.val = b+n.val*d) := by
    by_cases hb : (cell (restrictLabel B (progressionLabel N d₀ K)) (some b)).Nonempty
    · obtain ⟨hb',hfull⟩ := retained_fiber_info B b hb
      obtain ⟨hbound,hfiber⟩ := progressionLabel_fiber hd₀ hK0 b hb'
      have hR : ∀ n < K, (a+b.val • h)+n • (d₀ • h) ∈ R := by
        intro n hn
        let x : Fin N := ⟨b.val+n*d₀,hbound n hn⟩
        have hx : x ∈ B := hfull ((mem_cell_iff _ _ _).mpr ((hfiber x).mpr ⟨⟨n,hn⟩,rfl⟩))
        simpa only [x,smul_smul,add_nsmul,add_assoc] using hBR x hx
      obtain ⟨c,w,hw,hbad,hflat,hgeom⟩ := local_polynomial_progression_partition R k f hf
        (a+b.val • h) (d₀ • h) K L s hL hR hK
      exact ⟨c,w,hw,fun _ ↦ ⟨hbad,hflat,hgeom⟩⟩
    · exact ⟨fun _ ↦ none,fun _ _ ↦ 1,fun _ _ ↦ norm_one,fun h ↦ (hb h).elim⟩
  choose c w hw hprop using hlocal
  let c' := retainedRefineLabel (d := d₀) B hK0 c
  let w' : I → (Fin N × Fin K) → ℂ := fun i j ↦ w j.1 i j.2
  refine ⟨c',w',fun i j ↦ hw j.1 i j.2,?_,?_,?_⟩
  · exact retainedRefineLabel_bad_mass B hB hd₀ hK0 c
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) s) (fun b hb ↦ (hprop b hb).1)
  · intro x j hx i
    obtain ⟨hxb,hxj⟩ := (retainedRefineLabel_some_iff B hK0 c x j.1 j.2).mp hx
    have hb : (cell (restrictLabel B (progressionLabel N d₀ K)) (some j.1)).Nonempty :=
      ⟨x,(mem_cell_iff _ _ _).mpr hxb⟩
    have hxb' := ((restrictLabel_some_iff B _ x j.1).mp hxb).1
    obtain ⟨_,hbase⟩ := progressionLabel_some_base hxb'
    have he : x.val.val = j.1.val+(x.val.val/d₀%K)*d₀ := by
      rw [hbase]
      exact (blockBase_add_offset d₀ K x.val.val).symm
    have heg : a+x.val.val • h = (a+j.1.val • h)+(x.val.val/d₀%K) • (d₀ • h) := by
      conv_lhs => rw [he]
      simp only [smul_smul,add_nsmul,add_assoc]
    change ‖phase (f i (a+x.val.val • h))-w j.1 i j.2‖ ≤ _
    rw [heg]
    exact (hprop j.1 hb).2.1 ⟨x.val.val/d₀%K,Nat.mod_lt _ hK0⟩ j.2 hxj i
  · intro j hj
    exact retainedRefineLabel_geometry B hd₀ hK0 c (fun b hb ↦ (hprop b hb).2.2) j.1 j.2 hj

/-- Coarse terminal-block and Bohr-boundary losses are the only extra losses
when passing from interval partitions to a Bohr domain. -/
theorem bohr_local_polynomial_partition [Fintype G] (C : Finset (AddChar G ℂ))
    (k : ℕ) (f : I → G → Additive Circle) {R R' η : ℝ}
    (hf : ∀ i, IsLocallyPolynomial (bohr C R' : Set G) k (f i))
    (hRR' : R ≤ R') (a h : G) (N K L n₀ s : ℕ) (hL : 0 < L) (hn₀ : 0 < n₀)
    (hK : higherPartitionThreshold k (Fintype.card I) L s ≤ K)
    (hmesh : 4*(K : ℝ)/(n₀ : ℝ) ≤ η) (hB : (bohrIndices C R a h N).Nonempty) :
    ∃ c : bohrIndices C R a h N → Option (Fin N × Fin K),
    ∃ w : I → (Fin N × Fin K) → ℂ,
      (∀ i j, ‖w i j‖ = 1) ∧
      cellMass c none ≤
        (((((2*n₀+1)^(2*C.card)*K : ℕ) : ℝ)+
          ((bohrIndices C R a h N \ bohrIndices C (R-η) a h N).card : ℝ)) /
          ((bohrIndices C R a h N).card : ℝ))+(1/2 : ℝ)^s ∧
      (∀ x j, c x = some j → ∀ i, ‖phase (f i (a+x.val.val • h))-w i j‖ ≤ (1/2 : ℝ)^s) ∧
      ∀ j, (cell c (some j)).Nonempty →
        ∃ b d : ℕ, 0 < d ∧
          d ≤ higherPartitionStride k (Fintype.card I) L s*(2*n₀+1)^(2*C.card) ∧
          (∀ n < L, ∃ x : bohrIndices C R a h N, x.val.val = b+n*d) ∧
          ∀ x : bohrIndices C R a h N, c x = some j ↔ ∃ n : Fin L, x.val.val = b+n.val*d := by
  letI : Nonempty (bohrIndices C R a h N) := hB.to_subtype
  have hK0 : 0 < K := (higherPartitionThreshold_pos k (Fintype.card I) L s hL).trans_le hK
  obtain ⟨d₀,hd₀,hd₀bound,hcoarse⟩ := bohr_coarse_progression_partition C a h K n₀ hK0 hn₀ (R := R) hmesh
  obtain ⟨c,w,hw,hbad,hflat,hgeom⟩ := subset_local_polynomial_partition (bohr C R' : Set G) k f hf
    a h N K L s d₀ hL hd₀ hK (bohrIndices C R a h N) hB
    (fun x hx ↦ bohr_mono C hRR' ((mem_bohrIndices C R a h N x).mp hx))
  refine ⟨c,w,hw,?_,hflat,?_⟩
  · apply hbad.trans
    apply add_le_add _ le_rfl
    rw [cellMass_eq_card,Fintype.card_coe]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast (hcoarse N).2
  · intro j hj
    obtain ⟨b,d,hd,hdb,hpoints,hfiber⟩ := hgeom j hj
    exact ⟨b,d,hd,hdb.trans (Nat.mul_le_mul_left _ hd₀bound),hpoints,hfiber⟩

/-- Stable-radius specialization with an explicit rank/modulus exceptional budget. -/
theorem stable_bohr_polynomial_partition (p : ℕ) [NeZero p]
    (C : Finset (AddChar (ZMod p) ℂ)) (k : ℕ) (f : I → ZMod p → Additive Circle)
    {R R' : ℝ} (hR : 1/64 ≤ R) (hRR' : R ≤ R')
    (hf : ∀ i, IsLocallyPolynomial (bohr C R' : Set (ZMod p)) k (f i))
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z R)
    (K L n₀ s : ℕ) (hL : 0 < L) (hn₀ : 0 < n₀)
    (hK : higherPartitionThreshold k (Fintype.card I) L s ≤ K)
    (hmesh : 4*(K : ℝ)/(n₀ : ℝ) ≤ relativeWidth C z R) :
    ∃ c : bohrIndices C R 0 1 p → Option (Fin p × Fin K),
    ∃ w : I → (Fin p × Fin K) → ℂ,
      (∀ i j, ‖w i j‖ = 1) ∧
      cellMass c none ≤ (((2*n₀+1)^(2*C.card)*K*257^(2*C.card) : ℕ) : ℝ)/(p : ℝ)+
        1/(z : ℝ)+(1/2 : ℝ)^s ∧
      (∀ x j, c x = some j → ∀ i, ‖phase (f i (x.val.val : ZMod p))-w i j‖ ≤ (1/2 : ℝ)^s) ∧
      ∀ j, (cell c (some j)).Nonempty →
        ∃ b d : ℕ, 0 < d ∧
          d ≤ higherPartitionStride k (Fintype.card I) L s*(2*n₀+1)^(2*C.card) ∧
          (∀ n < L, ∃ x : bohrIndices C R 0 1 p, x.val.val = b+n*d) ∧
          ∀ x : bohrIndices C R 0 1 p, c x = some j ↔ ∃ n : Fin L, x.val.val = b+n.val*d := by
  have hR0 : 0 ≤ R := by linarith
  have hB := bohrIndices_nonempty p C hR0
  obtain ⟨c,w,hw,hbad,hflat,hgeom⟩ := bohr_local_polynomial_partition C k f hf hRR' 0 1
    p K L n₀ s hL hn₀ hK hmesh hB
  have hboundary := stable_index_boundary_fraction p C hz hR0 hstable
  have hBpos : (0 : ℝ) < (bohrIndices C R 0 1 p).card := by exact_mod_cast hB.card_pos
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hcard : (p : ℝ) ≤ (257^(2*C.card) : ℕ)*((bohrIndices C R 0 1 p).card : ℝ) := by
    exact_mod_cast bohrIndices_card_lower p C hR
  have hterm : (((2*n₀+1)^(2*C.card)*K : ℕ) : ℝ)/((bohrIndices C R 0 1 p).card : ℝ) ≤
      (((2*n₀+1)^(2*C.card)*K*257^(2*C.card) : ℕ) : ℝ)/(p : ℝ) := by
    apply (div_le_div_iff₀ hBpos hp).mpr
    have hh := mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg ((2*n₀+1)^(2*C.card)*K) :
      (0 : ℝ) ≤ ((2*n₀+1)^(2*C.card)*K : ℕ))
    simpa only [Nat.cast_mul,mul_assoc] using hh
  refine ⟨c,w,hw,?_,?_,hgeom⟩
  · rw [add_div] at hbad
    exact hbad.trans (add_le_add (add_le_add hterm hboundary) le_rfl)
  · simpa only [zero_add,nsmul_eq_mul,mul_one] using hflat

#print axioms subset_local_polynomial_partition
#print axioms stable_bohr_polynomial_partition
end Erdos3BohrLocalPolynomialPartition
