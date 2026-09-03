import Submission.BinaryCriticalAntidifferenceObstruction

/-! Exact left-Jordan projections and a necessary slope bound. This justifies
critical-slope tests for fixed dynamics; it does not settle Erdős 406. -/
namespace Erdos406BinaryCriticalRecurrence
open scoped Matrix BigOperators

lemma left_eigen_orbit (N : ℕ) (M : Matrix (Fin N) (Fin N) ℝ)
    (l v : Fin N → ℝ) (τ : ℝ) (hl : l ᵥ* M = τ • l) (n : ℕ) :
    l ⬝ᵥ ((M^n)*ᵥ v) = τ^n*(l ⬝ᵥ v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      hl, smul_dotProduct, smul_eq_mul, ih, pow_succ']
    ring

lemma left_jordan_orbit (N : ℕ) (M : Matrix (Fin N) (Fin N) ℝ)
    (x y v : Fin N → ℝ) (β : ℝ) (hy : y ᵥ* M = y)
    (hx : x ᵥ* M = x+β • y) (n : ℕ) :
    x ⬝ᵥ ((M^n)*ᵥ v) = x ⬝ᵥ v+n*β*(y ⬝ᵥ v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hey := left_eigen_orbit N M y v 1 (by simpa using hy) n
    simp only [one_pow, one_mul] at hey
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      hx, add_dotProduct, smul_dotProduct, smul_eq_mul, ih, hey]
    push_cast
    ring

lemma affine_slope_le (a b c d : ℝ)
    (h : ∀ n : ℕ, a*n-b ≤ c*n+d) : a ≤ c := by
  by_contra hh
  have hac : 0 < a-c := by linarith
  obtain ⟨n,hn⟩ := exists_nat_gt ((b+d)/(a-c))
  have hn' := (div_lt_iff₀ hac).mp hn
  have hh := h n
  nlinarith

/-- A bounded residual cannot change the linear slope of the critical
Jordan projection. No sign restrictions on observer coordinates are needed. -/
theorem jordan_observer_slope_lower (N : ℕ) (M : Matrix (Fin N) (Fin N) ℝ)
    (x y z u v : Fin N → ℝ) (α δ β a b C : ℝ)
    (hy : y ᵥ* M = y) (hx : x ᵥ* M = x+β • y)
    (hu : u = α • x+δ • y+z)
    (hz : ∀ n : ℕ, z ⬝ᵥ ((M^n)*ᵥ v) ≤ C)
    (hlower : ∀ n : ℕ, a*n-b ≤ u ⬝ᵥ ((M^n)*ᵥ v)) :
    a ≤ α*β*(y ⬝ᵥ v) := by
  apply affine_slope_le a b (α*β*(y ⬝ᵥ v))
    (α*(x ⬝ᵥ v)+δ*(y ⬝ᵥ v)+C)
  intro n
  have hxn := left_jordan_orbit N M x y v β hy hx n
  have hyn := left_eigen_orbit N M y v 1 (by simpa using hy) n
  simp only [one_pow, one_mul] at hyn
  have hz' := hz n
  have hl := hlower n
  rw [hu, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct,
    smul_eq_mul, smul_eq_mul, hxn, hyn] at hl
  nlinarith

/-- One subcritical real eigenmode supplies a uniformly bounded residual. -/
lemma bounded_left_eigen_orbit (N : ℕ) (M : Matrix (Fin N) (Fin N) ℝ)
    (z v : Fin N → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hz : z ᵥ* M = τ • z) (n : ℕ) :
    z ⬝ᵥ ((M^n)*ᵥ v) ≤ |z ⬝ᵥ v| := by
  rw [left_eigen_orbit N M z v τ hz n]
  have hpow : 0 ≤ τ^n := pow_nonneg hτ n
  have hpow1 : τ^n ≤ 1 := pow_le_one₀ hτ hτ1
  have hval := le_abs_self (z ⬝ᵥ v)
  have habs := abs_nonneg (z ⬝ᵥ v)
  nlinarith

/-- On a return cycle, comparing with the least leading observer coefficient
removes the freedom to rescale observers. This applies to EVERY finite
minimum family, not just a fixed number of pieces or a single observer. -/
theorem minimum_coefficient_slope_lower {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) (hx : ∀ i, 0 < x i) (a c B : ℝ) (ha : 0 ≤ a)
    (F G : ι → ℕ → ℝ) (C : ι → ℝ)
    (hG : ∀ i n, a*x i*n-B ≤ G i n)
    (hF : ∀ i n, F i n ≤ c*x i*n+C i)
    (hmatch : ∀ n j, ∃ i, G i n ≤ F j n) : a ≤ c := by
  classical
  obtain ⟨j,_,hj⟩ := (Finset.univ : Finset ι).exists_min_image x Finset.univ_nonempty
  have hj' : ∀ i, x j ≤ x i := fun i => hj i (Finset.mem_univ i)
  have hh : a*x j ≤ c*x j := by
    apply affine_slope_le (a*x j) B (c*x j) (C j)
    intro n
    obtain ⟨i,hi⟩ := hmatch n j
    have hmul : (a*x j)*n ≤ (a*x i)*n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hj' i) ha)
        (Nat.cast_nonneg n)
    have hlo := hG i n
    have hup := hF j n
    linarith
  exact (mul_le_mul_iff_left₀ (hx j)).mp (by simpa [mul_comm] using hh)

#print axioms minimum_coefficient_slope_lower
#print axioms left_eigen_orbit
#print axioms left_jordan_orbit
#print axioms jordan_observer_slope_lower
#print axioms bounded_left_eigen_orbit
end Erdos406BinaryCriticalRecurrence
