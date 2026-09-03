import Submission.IntervalProgressionPartition
import Submission.BohrArithmeticProgressions

/-! A quadratic phase with small curvature admits an almost complete partition
into fixed-length flat arithmetic progressions, by linear Dirichlet approximation. -/
namespace Erdos3NearLinearProgressionPartition
open Finset Erdos3IntervalProgressionPartition Erdos3BohrArithmeticProgressions
  Erdos3LocalQuadraticProgressions Erdos3QuadraticProgressionCurvature
  Erdos3FinitePartitionIncrement
open scoped Classical
set_option maxHeartbeats 3000000

lemma binomial_phase_near_linear (A u v : ℂ) (hA : ‖A‖ = 1) (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) {η : ℝ} (hη : ‖v-1‖ ≤ η) {k M : ℕ} (hk : k ≤ M) :
    ‖A*u^k*v^(k.choose 2)-A*u^k‖ ≤ (M : ℝ)^2*η := by
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hη
  have hchoose : (k.choose 2 : ℝ) ≤ (M : ℝ)^2 := by
    have h : 2*((k.choose 2 : ℕ) : ℝ)+(k : ℝ) = (k : ℝ)^2 := by
      exact_mod_cast two_choose_two_add k
    have hk' : (k : ℝ) ≤ M := by exact_mod_cast hk
    nlinarith [Nat.cast_nonneg (α := ℝ) k,Nat.cast_nonneg (α := ℝ) M]
  calc
    _ = ‖v^(k.choose 2)-1‖ := by
      rw [← mul_sub_one,norm_mul,norm_mul,norm_pow,hA,hu,one_pow,one_mul,one_mul]
    _ ≤ (k.choose 2 : ℝ)*‖v-1‖ := unit_power_oscillation v hv _
    _ ≤ (k.choose 2 : ℝ)*η := mul_le_mul_of_nonneg_left hη (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right hchoose hη0

lemma linear_phase_residue_oscillation (A u : ℂ) (hA : ‖A‖ = 1) (hu : ‖u‖ = 1)
    (r j d : ℕ) : ‖A*u^(r+j*d)-A*u^r‖ ≤ (j : ℝ)*‖u^d-1‖ := by
  calc
    _ = ‖(u^d)^j-1‖ := by
      rw [pow_add,show j*d = d*j by ring,pow_mul]
      have he : A*(u^r*(u^d)^j)-A*u^r = (A*u^r)*((u^d)^j-1) := by ring
      rw [he,norm_mul,norm_mul,norm_pow,hA,hu,one_pow,one_mul,one_mul]
    _ ≤ _ := unit_power_oscillation (u^d) (by rw [norm_pow,hu,one_pow]) j

lemma binomial_phase_residue_oscillation (A u v : ℂ)
    (hA : ‖A‖ = 1) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {η : ℝ} (hη : ‖v-1‖ ≤ η) {r j d M : ℕ} (hindex : r+j*d ≤ M) :
    ‖A*u^(r+j*d)*v^((r+j*d).choose 2)-A*u^r*v^(r.choose 2)‖ ≤
      2*(M : ℝ)^2*η+(j : ℝ)*‖u^d-1‖ := by
  have hfirst := binomial_phase_near_linear A u v hA hu hv hη hindex
  have hlast := binomial_phase_near_linear A u v hA hu hv hη (show r ≤ M by omega)
  have hmid := linear_phase_residue_oscillation A u hA hu r j d
  have htri := norm_sub_le_norm_sub_add_norm_sub (A*u^(r+j*d)*v^((r+j*d).choose 2)) (A*u^(r+j*d))
    (A*u^r*v^(r.choose 2))
  have htri' := norm_sub_le_norm_sub_add_norm_sub (A*u^(r+j*d)) (A*u^r) (A*u^r*v^(r.choose 2))
  rw [norm_sub_rev (A*u^r) (A*u^r*v^(r.choose 2))] at htri'
  linarith

/-- All but fewer than D*L indices are partitioned into proper length-L
progressions on which every prescribed small-curvature quadratic is flat.
Here D=(2n+1)^(2*card I) is only the linear Dirichlet cost. -/
theorem near_linear_progression_partition {I : Type*} [Fintype I]
    (f : I → ℕ → ℂ) (A u v : I → ℂ)
    (hA : ∀ i, ‖A i‖ = 1) (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1)
    {η : ℝ} (hη : ∀ i, ‖v i-1‖ ≤ η) (M L n : ℕ) (hL : 0 < L) (hn : 0 < n)
    (hrep : ∀ i k, k < M → f i k = A i*(u i)^k*(v i)^(k.choose 2)) :
    ∃ d : ℕ, 0 < d ∧ d ≤ (2*n+1)^(2*Fintype.card I) ∧
      (cell (progressionLabel M d L) none).card < (2*n+1)^(2*Fintype.card I)*L ∧
      ∀ k a : Fin M, progressionLabel M d L k = some a →
        ∀ i, ‖f i k.val-f i a.val‖ ≤ 2*(M : ℝ)^2*η+2*(L : ℝ)/(n : ℝ) := by
  obtain ⟨d,hd,hdb,hclose⟩ := simultaneous_linear_dirichlet u hu n hn
  refine ⟨d,hd,hdb,?_,?_⟩
  · rw [progressionLabel_bad_card hd hL]
    exact (Nat.mod_lt _ (Nat.mul_pos hd hL)).trans_le (Nat.mul_le_mul_right L hdb)
  · intro k a hka i
    have hcell : (cell (progressionLabel M d L) (some a)).Nonempty := by
      refine ⟨k,?_⟩
      simpa only [cell,mem_filter,mem_univ,true_and] using hka
    obtain ⟨_,hfiber⟩ := progressionLabel_fiber hd hL a hcell
    obtain ⟨j,hkj⟩ := (hfiber k).mp hka
    rw [hrep i k.val k.isLt,hrep i a.val a.isLt,hkj]
    apply (binomial_phase_residue_oscillation (A i) (u i) (v i)
      (hA i) (hu i) (hv i) (hη i) (by omega : a.val+j.val*d ≤ M)).trans
    apply add_le_add_right
    calc
      _ ≤ (L : ℝ)*(2/(n : ℝ)) := mul_le_mul
        (by exact_mod_cast j.isLt.le) (hclose i) (norm_nonneg _) (Nat.cast_nonneg _)
      _ = _ := by ring

#print axioms near_linear_progression_partition
end Erdos3NearLinearProgressionPartition
