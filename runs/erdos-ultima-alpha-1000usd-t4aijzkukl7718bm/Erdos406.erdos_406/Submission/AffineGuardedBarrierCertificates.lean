import Submission.AffineBarrierCertificates

/-! A divisibility-guarded barrier criterion. The missing separating barrier
is a hypothesis, not a constructed witness or a settlement of Erdős 406. -/
namespace Erdos406GuardedBarrier
open Erdos406AffineCertificate Erdos406GroupedCertificate Erdos406AffinePotential
  Erdos406AffineBarrier

/-- An invariant guard can restrict both the threshold-preservation condition
and the bound on good words. -/
theorem guarded_threshold_criterion (G : ℕ → Prop) (V : ℕ → ℝ) (B : ℝ) (E : ℕ)
    (hguard : ∀ n, G n → G (4*n+1))
    (hpres : ∀ n, G n → B < V n → B < V (4*n+1))
    (hgood : ∀ n, G n → Good n → V n ≤ B)
    (hseedG : G (orbit 4 1 E)) (hseed : B < V (orbit 4 1 E)) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  have horbit : ∀ j : ℕ, G (orbit 4 1 (E+j)) ∧ B < V (orbit 4 1 (E+j)) := by
    intro j
    induction j with
    | zero => simpa using And.intro hseedG hseed
    | succ j ih =>
      simpa only [Nat.add_succ, orbit_succ] using
        And.intro (hguard _ ih.1) (hpres _ ih.1 ih.2)
  have hcut : ∀ t : ℕ, E ≤ t → ¬ Good (orbit 4 1 t) := by
    intro t ht hg
    have hh := horbit (t-E)
    rw [Nat.add_sub_of_le ht] at hh
    exact (not_lt_of_ge (hgood _ hh.1 hg)) hh.2
  apply Erdos406SingleAffine.single_affine_criterion
  refine ((Finset.range E).finite_toSet.image (orbit 4 1)).subset ?_
  rintro n ⟨⟨t,rfl⟩,hg⟩
  refine ⟨t, ?_, rfl⟩
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra ht
  exact hcut t (by omega) hg

/-- The guard is satisfied by a late power-of-four affine orbit and is
preserved exactly. No potential with the required separation is supplied. -/
theorem divisibility_guarded_barrier_criterion (M E : ℕ) (hM : M ∣ 4^E)
    (V : ℕ → ℝ) (B a : ℝ) (ha : 0 < a)
    (hstep : ∀ n, M ∣ 3*n+1 → a*(V n-B) ≤ V (4*n+1)-B)
    (hgood : ∀ n, M ∣ 3*n+1 → Good n → V n ≤ B)
    (hseed : B < V (orbit 4 1 E)) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  apply guarded_threshold_criterion (fun n => M ∣ 3*n+1) V B E ?_ ?_ hgood ?_ hseed
  · intro n hn
    have he : 3*(4*n+1)+1 = 4*(3*n+1) := by ring
    rw [he]
    exact dvd_mul_of_dvd_right hn 4
  · intro n hn hv
    exact sub_pos.mp ((mul_pos ha (sub_pos.mpr hv)).trans_le (hstep n hn))
  · simpa only [Erdos406SingleAffine.single_orbit_identity] using hM

#print axioms guarded_threshold_criterion
#print axioms divisibility_guarded_barrier_criterion
end Erdos406GuardedBarrier
