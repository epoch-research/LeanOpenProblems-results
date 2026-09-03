import Submission.LinearRecurrenceObstruction

/-! Cayley-Hamilton extends the recurrence obstruction to every finite-rank
integer-linear orbit and every Gaussian-integer linear observation of it.
This excludes a broad class of explicit self-similar constructions, not all
bounded-step paths. -/
namespace Erdos952Investigation
namespace LinearOrbitObstruction

open LinearRecurrenceObstruction
set_option maxHeartbeats 0

variable {M : Type*} [AddCommGroup M]
  [Module.Free ℤ M] [Module.Finite ℤ M]

lemma linear_orbit_recurrence (f : M →ₗ[ℤ] M) (g : M →ₗ[ℤ] GaussianInt) (v : M) :
    ∃ k : ℕ, ∃ a : Fin k → ℤ, ∀ n : ℕ,
      g ((f^(n+k)) v) = ∑ i : Fin k, (a i : GaussianInt)*g ((f^(n+i.val)) v) := by
  classical
  letI : Algebra ℤ (M →ₗ[ℤ] M) := Module.End.instAlgebra ℤ ℤ M
  let k := f.charpoly.natDegree
  let a : Fin k → ℤ := fun i => -f.charpoly.coeff i.val
  have hCH := f.aeval_self_charpoly
  rw [Polynomial.aeval_eq_sum_range,Finset.sum_range_succ,
    f.charpoly_monic.coeff_natDegree,one_smul] at hCH
  have hp : f^k = ∑ i : Fin k, a i • f^i.val := by
    have hh : f^k = -(∑ i ∈ Finset.range k,
        f.charpoly.coeff i • f^i) :=
      eq_neg_of_add_eq_zero_right hCH
    rw [hh]
    simp only [a,neg_smul,Finset.sum_neg_distrib]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => f.charpoly.coeff i • f^i)]
  refine ⟨k,a,?_⟩
  intro n
  have hh := congrArg (fun h : M →ₗ[ℤ] M => g (h ((f^n) v))) hp
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul] at hh
  simpa only [← Module.End.mul_apply,← pow_add,Nat.add_comm,zsmul_eq_mul] using hh

/-- No injective Gaussian-prime sequence can be an integer-linear observation
of a finite-rank integer-linear orbit, even with a constant offset. -/
theorem no_prime_linear_orbit (f : M →ₗ[ℤ] M) (g : M →ₗ[ℤ] GaussianInt)
    (v : M) (c : GaussianInt) :
    ¬ (Function.Injective (fun n : ℕ => c+g ((f^n) v)) ∧
      ∀ n : ℕ, Prime (c+g ((f^n) v))) := by
  rintro ⟨hx,hp⟩
  obtain ⟨k,a,hrec⟩ := linear_orbit_recurrence f g v
  let b := c-∑ i : Fin k, (a i : GaussianInt)*c
  apply no_eventual_affine_recurrence (fun n => c+g ((f^n) v)) hx hp k 0 a b
  intro n hn
  simp only [mul_add,Finset.sum_add_distrib,b,hrec]
  abel

/-- Even a linear-orbit representation restricted to geometrically spaced
indices is incompatible with an injective Gaussian-prime sequence. -/
theorem no_geometric_index_linear_orbit (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (q : ℕ) (hq : 2 ≤ q) (f : M →ₗ[ℤ] M) (g : M →ₗ[ℤ] GaussianInt)
    (v : M) (c : GaussianInt) :
    ¬ ∀ n : ℕ, x (q^n) = c+g ((f^n) v) := by
  intro hrep
  apply no_prime_linear_orbit f g v c
  constructor
  · intro i j he
    apply Nat.pow_right_injective hq
    apply hx
    simpa only [hrep] using he
  · intro n
    rw [← hrep n]
    exact hp (q^n)

/-- An equivalent form using recursively evolved states instead of powers of
an endomorphism. -/
theorem no_geometric_index_linear_state (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n))
    (q : ℕ) (hq : 2 ≤ q) (f : M →ₗ[ℤ] M) (g : M →ₗ[ℤ] GaussianInt)
    (state : ℕ → M) (c : GaussianInt)
    (hstate : ∀ n, state (n+1) = f (state n)) :
    ¬ ∀ n : ℕ, x (q^n) = c+g (state n) := by
  have hpow (n : ℕ) : state n = (f^n) (state 0) := by
    induction n with
    | zero => simp
    | succ n ih => rw [hstate,ih,pow_succ',Module.End.mul_apply]
  intro hrep
  apply no_geometric_index_linear_orbit x hx hp q hq f g (state 0) c
  intro n
  rw [hrep,hpow]

#print axioms no_geometric_index_linear_orbit
#print axioms no_geometric_index_linear_state
#print axioms linear_orbit_recurrence
#print axioms no_prime_linear_orbit

end LinearOrbitObstruction
end Erdos952Investigation
