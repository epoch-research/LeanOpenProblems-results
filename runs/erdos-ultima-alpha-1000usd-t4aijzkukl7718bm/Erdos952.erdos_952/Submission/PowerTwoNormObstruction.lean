import Submission.SimilarityStepObstruction

/-! No injective Gaussian-prime ray can have every jump of the same squared
norm2^k, for any k. Mixtures of different squared norms are not excluded. -/
namespace Erdos952Investigation.PowerTwoNormObstruction
open SimilarityStepObstruction
set_option maxHeartbeats 0

def ramified : GaussianInt := ⟨1,1⟩
lemma ramified_norm : ramified.norm = 2 := by norm_num [ramified,gaussian_norm_sq]

lemma norm_power (z : GaussianInt) (k : ℕ) : (z^k).norm = z.norm^k :=
  Zsqrtd.normMonoidHom.map_pow z k

lemma factor_ramified_of_even_norm (z : GaussianInt) (hn : z.norm%2 = 0) :
    ∃ w : GaussianInt, z = ramified*w := by
  have he : Even (z.re+z.im) := Int.even_iff.mpr (by rw [← norm_mod_two,hn])
  obtain ⟨a,ha⟩ := he
  refine ⟨⟨a,z.im-a⟩,?_⟩
  apply Zsqrtd.ext <;> simp [ramified,Zsqrtd.re_mul,Zsqrtd.im_mul] <;> omega

/-- A Gaussian integer with norm2^k is a unit multiple of (1+i)^k. -/
theorem norm_two_power_factorization (k : ℕ) (z : GaussianInt)
    (hn : z.norm = (2 : ℤ)^k) :
    ∃ e : GaussianInt, e.norm = 1 ∧ z = ramified^k*e := by
  induction k generalizing z with
  | zero => exact ⟨z,by simpa using hn,by simp⟩
  | succ k ih =>
    have hev : z.norm%2 = 0 := by rw [hn,pow_succ]; omega
    obtain ⟨w,hw⟩ := factor_ramified_of_even_norm z hev
    have hwn : w.norm = (2 : ℤ)^k := by
      rw [hw,Zsqrtd.norm_mul,ramified_norm,pow_succ] at hn
      omega
    obtain ⟨e,he,hwe⟩ := ih w hwn
    refine ⟨e,he,?_⟩
    rw [hw,hwe,pow_succ']
    ring

lemma ramified_power_coprime (k : ℕ) : IsCoprime (ramified^k).norm 65 := by
  rw [norm_power,ramified_norm]
  exact (show IsCoprime (2 : ℤ) 65 from ⟨-32,1,by norm_num⟩).pow_left

/-- The exponent is unrestricted, so this excludes an unbounded family of
single squared-norm jump constraints. It is not the original negation. -/
theorem no_constant_power_two_norm_prime_ray (k : ℕ) (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) :
    ¬ ∀ n, (x (n+1)-x n).norm = (2 : ℤ)^k := by
  intro hs
  exact no_unit_multiple_prime_ray (ramified^k) (ramified_power_coprime k) x hx hp
    (fun n => norm_two_power_factorization k (x (n+1)-x n) (hs n))

/-- No tail of an injective prime sequence has one constant power-of-two
squared jump norm. -/
theorem infinitely_often_not_power_two_norm (k : ℕ) (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) (N : ℕ) :
    ∃ n ≥ N, (x (n+1)-x n).norm ≠ (2 : ℤ)^k := by
  by_contra! hs
  apply no_constant_power_two_norm_prime_ray k (fun n => x (N+n))
    (fun _ _ he => Nat.add_left_cancel (hx he)) (fun n => hp (N+n))
  intro n
  simpa only [Nat.add_assoc] using hs (N+n) (by omega)

/-- One tail index works for every exponent: no block of4225 jumps in that
    tail can have one constant power-of-two squared norm. -/
theorem power_two_runs_eventually_break (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hp : ∀ n, Prime (x n)) :
    ∃ K : ℕ, ∀ k N : ℕ, K ≤ N → ∃ n, N ≤ n ∧ n < N+4225 ∧
      (x (n+1)-x n).norm ≠ (2 : ℤ)^k := by
  obtain ⟨K,hK⟩ := similar_step_runs_eventually_break x hx hp
  refine ⟨K,?_⟩
  intro k N hN
  obtain ⟨n,hn,hn',hno⟩ := hK (ramified^k) (ramified_power_coprime k) N hN
  exact ⟨n,hn,hn',fun he => hno (norm_two_power_factorization k _ he)⟩

#print axioms power_two_runs_eventually_break
#print axioms norm_two_power_factorization
#print axioms no_constant_power_two_norm_prime_ray
#print axioms infinitely_often_not_power_two_norm
end Erdos952Investigation.PowerTwoNormObstruction
