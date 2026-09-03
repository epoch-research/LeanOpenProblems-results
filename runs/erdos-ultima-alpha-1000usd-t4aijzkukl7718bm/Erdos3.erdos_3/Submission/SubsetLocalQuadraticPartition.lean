import Submission.RetainedProgressionAssembly
import Submission.LocalQuadraticProgressionPartition

/-! A flat progression partition of a subset of an interval, obtained by
refining its retained complete coarse progression fibers. -/
namespace Erdos3SubsetLocalQuadraticPartition
open Finset Erdos3RetainedProgressionAssembly Erdos3RestrictedPartialPartition
  Erdos3ProgressionFiberEquivalence Erdos3IntervalProgressionPartition
  Erdos3LocalQuadraticProgressionPartition Erdos3LocalQuadraticInverse
  Erdos3SimultaneousQuadraticRecurrence Erdos3FinitePartitionIncrement
open scoped BigOperators Classical
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

variable {G I : Type*} [AddCommGroup G] [Fintype I]

/-- The only outer loss is the mass of coarse fibers not wholly retained in B.
Inside every retained coarse fiber, the quadratic partition loses only the
explicit local endpoint fractions. Every good cell is exactly a progression
whose entire list of natural indices belongs to B. -/
theorem subset_local_quadratic_partition (R : Set G) (q : I → G → ℂ)
    (hq : ∀ i x, ‖q i x‖ = 1) (hquad : ∀ i, IsLocallyQuadratic R (q i)) (a h : G)
    (N K M L n t d₀ : ℕ) (hK : 0 < K) (hM : 0 < M) (hL : 0 < L) (hn : 0 < n) (hd₀ : 0 < d₀)
    (B : Finset (Fin N)) (hB : B.Nonempty) (hBR : ∀ x ∈ B, a+x.val • h ∈ R) :
    ∃ c : B → Option (Fin N × (Fin K × Fin M)), ∃ w : I → (Fin N × (Fin K × Fin M)) → ℂ,
      (∀ i j, ‖w i j‖ = 1) ∧
      cellMass c none ≤ cellMass (restrictLabel B (progressionLabel N d₀ K)) none+
        ((recurrenceBound (Fintype.card I) t : ℝ)*(M : ℝ)/(K : ℝ)+
          (((2*n+1)^(2*Fintype.card I) : ℕ) : ℝ)*(L : ℝ)/(M : ℝ)) ∧
      (∀ x j, c x = some j → ∀ i,
        ‖q i (a+x.val.val • h)-w i j‖ ≤ 2*(M : ℝ)^2*(1/2 : ℝ)^t+2*(L : ℝ)/(n : ℝ)) ∧
      (∀ j, (cell c (some j)).Nonempty →
        ∃ b d : ℕ, 0 < d ∧ d ≤ (recurrenceBound (Fintype.card I) t*(2*n+1)^(2*Fintype.card I))*d₀ ∧
          (∀ k < L, ∃ x : B, x.val.val = b+k*d) ∧
          ∀ x : B, c x = some j ↔ ∃ k : Fin L, x.val.val = b+k.val*d) := by
  let τ : ℝ := (recurrenceBound (Fintype.card I) t : ℝ)*(M : ℝ)/(K : ℝ)+
    (((2*n+1)^(2*Fintype.card I) : ℕ) : ℝ)*(L : ℝ)/(M : ℝ)
  let ε : ℝ := 2*(M : ℝ)^2*(1/2 : ℝ)^t+2*(L : ℝ)/(n : ℝ)
  let D := recurrenceBound (Fintype.card I) t*(2*n+1)^(2*Fintype.card I)
  have hlocal (b : Fin N) :
      ∃ c : Fin K → Option (Fin K × Fin M), ∃ w : I → (Fin K × Fin M) → ℂ,
        (∀ i j, ‖w i j‖ = 1) ∧
        ((cell (restrictLabel B (progressionLabel N d₀ K)) (some b)).Nonempty →
          cellMass c none ≤ τ ∧
          (∀ x j, c x = some j → ∀ i,
            ‖q i ((a+b.val • h)+x.val • (d₀ • h))-w i j‖ ≤ ε) ∧
          (∀ j, (cell c (some j)).Nonempty →
            ∃ s d : ℕ, 0 < d ∧ d ≤ D ∧ (∀ k < L, s+k*d < K) ∧
              ∀ x : Fin K, c x = some j ↔ ∃ k : Fin L, x.val = s+k.val*d)) := by
    by_cases hb : (cell (restrictLabel B (progressionLabel N d₀ K)) (some b)).Nonempty
    · obtain ⟨hb',hfull⟩ := retained_fiber_info B b hb
      obtain ⟨hbound,hfiber⟩ := progressionLabel_fiber hd₀ hK b hb'
      have hR : ∀ k < K, (a+b.val • h)+k • (d₀ • h) ∈ R := by
        intro k hk
        let x : Fin N := ⟨b.val+k*d₀,hbound k hk⟩
        have hx : x ∈ B := hfull ((mem_cell_iff _ _ _).mpr ((hfiber x).mpr ⟨⟨k,hk⟩,rfl⟩))
        simpa only [x,smul_smul,add_nsmul,add_assoc] using hBR x hx
      obtain ⟨c,w,hw,hbad,hflat,hgeom⟩ := local_quadratic_progression_partition R q hq hquad
        (a+b.val • h) (d₀ • h) K M L n t hK hM hL hn hR
      exact ⟨c,w,hw,fun _ ↦ ⟨hbad,hflat,hgeom⟩⟩
    · exact ⟨fun _ ↦ none,fun _ _ ↦ 1,fun _ _ ↦ norm_one,fun h ↦ False.elim (hb h)⟩
  choose c w hw hprop using hlocal
  let c' := retainedRefineLabel (d := d₀) B hK c
  let w' : I → (Fin N × (Fin K × Fin M)) → ℂ := fun i j ↦ w j.1 i j.2
  have hτ : 0 ≤ τ := add_nonneg
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
  refine ⟨c',w',(fun i j ↦ hw j.1 i j.2),?_,?_,?_⟩
  · exact retainedRefineLabel_bad_mass B hB hd₀ hK c (τ := τ) hτ
      (fun b hb ↦ (hprop b hb).1)
  · intro x j hx i
    obtain ⟨hxb,hxj⟩ := (retainedRefineLabel_some_iff B hK c x j.1 j.2).mp hx
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
    change ‖q i (a+x.val.val • h)-w j.1 i j.2‖ ≤ ε
    rw [heg]
    exact (hprop j.1 hb).2.1 ⟨x.val.val/d₀%K,Nat.mod_lt _ hK⟩ j.2 hxj i
  · intro j hj
    exact retainedRefineLabel_geometry B hd₀ hK c (fun b hb ↦ (hprop b hb).2.2) j.1 j.2 hj

#print axioms subset_local_quadratic_partition
end Erdos3SubsetLocalQuadraticPartition
