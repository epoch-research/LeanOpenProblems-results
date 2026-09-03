import Submission.QuadraticSequenceDilation
import Submission.RefinedProgressionPartition

/-! An almost complete partition of an interval into fixed-length arithmetic
progressions that flatten finitely many quadratic phases. The exceptional
fraction, stride cost, and phase error are all explicit. -/
namespace Erdos3QuadraticProgressionPartition
open Finset Erdos3QuadraticSequenceDilation Erdos3NearLinearProgressionPartition
  Erdos3RefinedProgressionPartition Erdos3IntervalProgressionPartition
  Erdos3ProgressionFiberEquivalence Erdos3SimultaneousQuadraticRecurrence
  Erdos3FinitePartitionIncrement Erdos3MaskedPhaseIncrement
open scoped BigOperators Classical
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

/-- First make the curvature small along one common stride. Then each complete
outer fiber admits its own linear Dirichlet stride. All resulting good cells
are proper length-L progressions; the omitted proportion is bounded by the
sum of the outer and inner endpoint losses. -/
theorem quadratic_progression_partition {I : Type*} [Fintype I]
    (A u v : I → ℂ) (hA : ∀ i, ‖A i‖ = 1) (hu : ∀ i, ‖u i‖ = 1)
    (hv : ∀ i, ‖v i‖ = 1) (N M L n t : ℕ)
    (hN : 0 < N) (hM : 0 < M) (hL : 0 < L) (hn : 0 < n) :
    ∃ c : Fin N → Option (Fin N × Fin M), ∃ w : I → (Fin N × Fin M) → ℂ,
      (∀ i ab, ‖w i ab‖ = 1) ∧
      cellMass c none ≤ (recurrenceBound (Fintype.card I) t : ℝ)*(M : ℝ)/(N : ℝ)+
        (((2*n+1)^(2*Fintype.card I) : ℕ) : ℝ)*(L : ℝ)/(M : ℝ) ∧
      (∀ k ab, c k = some ab → ∀ i,
        ‖A i*(u i)^k.val*(v i)^(k.val.choose 2)-w i ab‖ ≤
          2*(M : ℝ)^2*(1/2 : ℝ)^t+2*(L : ℝ)/(n : ℝ)) ∧
      (∀ ab, (cell c (some ab)).Nonempty →
        ∃ a d : ℕ, 0 < d ∧ d ≤ recurrenceBound (Fintype.card I) t*(2*n+1)^(2*Fintype.card I) ∧
          (∀ j < L, a+j*d < N) ∧
          ∀ k : Fin N, c k = some ab ↔ ∃ j : Fin L, k.val = a+j.val*d) := by
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  let Q : I → ℕ → ℂ := fun i k ↦ A i*(u i)^k*(v i)^(k.choose 2)
  have hQ (i : I) (k : ℕ) : ‖Q i k‖ = 1 := by
    simp only [Q,norm_mul,norm_pow,hA,hu,hv,one_pow,one_mul]
  obtain ⟨d₁,hd₁,hd₁bound,hcurve⟩ := simultaneous_square_recurrence v hv t
  let A' : Fin N → I → ℂ := fun a i ↦ Q i a.val
  let u' : Fin N → I → ℂ := fun a i ↦ (u i)^d₁*(v i)^(a.val*d₁+d₁.choose 2)
  let v' : I → ℂ := fun i ↦ (v i)^(d₁^2)
  have hA' (a : Fin N) (i : I) : ‖A' a i‖ = 1 := hQ i a.val
  have hu' (a : Fin N) (i : I) : ‖u' a i‖ = 1 := by
    simp only [u',norm_mul,norm_pow,hu,hv,one_pow,one_mul]
  have hv' (i : I) : ‖v' i‖ = 1 := by simp only [v',norm_pow,hv,one_pow]
  have hrep (a : Fin N) (i : I) (k : ℕ) :
      Q i (a.val+k*d₁) = A' a i*(u' a i)^k*(v' i)^(k.choose 2) :=
    binomial_phase_dilate (A i) (u i) (v i) a.val k d₁
  have hin (a : Fin N) := near_linear_progression_partition
    (fun i k ↦ Q i (a.val+k*d₁)) (A' a) (u' a) v' (hA' a) (hu' a) hv'
    hcurve M L n hL hn (fun i k _ ↦ hrep a i k)
  choose d₂ hd₂ hd₂bound hbad₂ hflat₂ using hin
  let c := refinedProgressionLabel N d₁ M L hM d₂
  let w : I → (Fin N × Fin M) → ℂ := fun i ab ↦ Q i (ab.1.val+ab.2.val*d₁)
  refine ⟨c,w,(fun i ab ↦ hQ i _),?_,?_,?_⟩
  · have hb := refinedProgressionLabel_bad_mass hN hd₁ hM d₂
      (B := (((2*n+1)^(2*Fintype.card I)*L : ℕ) : ℝ))
      (Nat.cast_nonneg _) (fun a ↦ by exact_mod_cast (hbad₂ a).le)
    have ho : cellMass (progressionLabel N d₁ M) none ≤
        ((recurrenceBound (Fintype.card I) t*M : ℕ) : ℝ)/(N : ℝ) := by
      rw [cellMass_eq_card,progressionLabel_bad_card hd₁ hM,Fintype.card_fin]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast (Nat.mod_lt N (Nat.mul_pos hd₁ hM)).le.trans
        (Nat.mul_le_mul_right M hd₁bound.le)
    simpa only [Nat.cast_mul] using hb.trans (add_le_add ho le_rfl)
  · intro k ab hk i
    obtain ⟨hka,hkb⟩ := (refinedProgressionLabel_some_iff hM d₂ k ab.1 ab.2).mp hk
    obtain ⟨_,hak⟩ := progressionLabel_some_base hka
    have he : k.val = ab.1.val+(k.val/d₁%M)*d₁ := by
      rw [hak]
      exact (blockBase_add_offset d₁ M k.val).symm
    change ‖Q i k.val-Q i (ab.1.val+ab.2.val*d₁)‖ ≤ _
    rw [he]
    exact hflat₂ ab.1 ⟨k.val/d₁%M,Nat.mod_lt _ hM⟩ ab.2 hkb i
  · intro ab hab
    obtain ⟨hbound,hfiber⟩ := refinedProgressionLabel_geometry hd₁ hM hL d₂ hd₂ ab.1 ab.2 hab
    refine ⟨ab.1.val+ab.2.val*d₁,d₂ ab.1*d₁,Nat.mul_pos (hd₂ ab.1) hd₁,?_,hbound,hfiber⟩
    simpa only [Nat.mul_comm] using Nat.mul_le_mul (hd₂bound ab.1) hd₁bound.le

#print axioms quadratic_progression_partition
end Erdos3QuadraticProgressionPartition
