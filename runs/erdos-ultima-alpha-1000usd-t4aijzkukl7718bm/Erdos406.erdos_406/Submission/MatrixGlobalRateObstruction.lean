import Submission.MatrixCertificates

/-! Global radix-rate obstructions. These results do not settle Erdős 406. -/
namespace Erdos406MatrixGlobalRate
open Erdos406Matrix Erdos406AffineCertificate Erdos406GroupedCertificate
  Erdos406AffinePotential
open scoped BigOperators Matrix

/-- A global ternary upper bound, unlike a bound restricted to good words,
cannot coexist with strictly faster growth along the affine orbit. -/
theorem global_rate_obstruction (S : ℕ → ℝ) (lam ρ K : ℝ)
    (hlam : 1 < lam) (hρ : 1 ≤ ρ) (hK : 0 < K) (hzero : 0 < S 0)
    (hgrow : ∀ n, lam * S n ≤ S (4 * n + 1))
    (hupper : ∀ n, S n ≤ K * ρ ^ (Nat.digits 3 n).length) :
    Real.log lam * Real.log 3 ≤ Real.log ρ * Real.log 4 := by
  by_contra hnot
  have hcrit : Real.log ρ * Real.log 4 < Real.log lam * Real.log 3 := lt_of_not_ge hnot
  have hlam0 : 0 < lam := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogρ : 0 ≤ Real.log ρ := Real.log_nonneg hρ
  have hgap : 0 < Real.log lam * Real.log 3 - Real.log ρ * Real.log 4 := by linarith
  have horbit : ∀ t : ℕ, lam ^ t * S 0 ≤ S (orbit 4 1 t) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hs := hgrow (orbit 4 1 t)
      have hh := mul_le_mul_of_nonneg_left ih hlam0.le
      rw [orbit_succ, pow_succ]
      nlinarith
  obtain ⟨t, ht⟩ := exists_nat_gt
    ((Real.log K - Real.log (S 0)) * Real.log 3 /
      (Real.log lam * Real.log 3 - Real.log ρ * Real.log 4))
  have hlarge := (div_lt_iff₀ hgap).mp ht
  have hb := (horbit t).trans (hupper _)
  have hl := Real.log_le_log (mul_pos (pow_pos hlam0 t) hzero) hb
  rw [Real.log_mul (ne_of_gt (pow_pos hlam0 t)) (ne_of_gt hzero),
    Real.log_mul (ne_of_gt hK) (ne_of_gt (pow_pos hρ0 _)),
    Real.log_pow, Real.log_pow] at hl
  have hl' := mul_le_mul_of_nonneg_right hl hlog3.le
  have hlen := mul_le_mul_of_nonneg_left (orbit_length_log_le t) hlogρ
  nlinarith

/-- Any digit-independent affine upper recurrence gives the same global
radix rate, even if its additive constants depend on the digit. -/
lemma uniform_recurrence_upper (S : ℕ → ℝ) (ρ B : ℝ)
    (hρ : 1 < ρ) (hB : 0 ≤ B)
    (hrec : ∀ n, 0 < n → S n ≤ ρ * S (n / 3) + B) (n : ℕ) :
    S n ≤ (S 0 + B / (ρ - 1)) * ρ ^ (Nat.digits 3 n).length := by
  have hC : 0 ≤ B / (ρ - 1) := div_nonneg hB (by linarith)
  have hCeq : B + B / (ρ - 1) = ρ * (B / (ρ - 1)) := by
    field_simp [ne_of_gt (sub_pos.mpr hρ)]
    ring
  have hbound : ∀ n, S n + B / (ρ - 1) ≤
      (S 0 + B / (ρ - 1)) * ρ ^ (Nat.digits 3 n).length := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n = 0
      · subst n; simp
      have hp : 0 < n := Nat.pos_of_ne_zero hn
      have hi := ih (n / 3) (Nat.div_lt_self hp (by decide))
      have hh := mul_le_mul_of_nonneg_left hi (by linarith : 0 ≤ ρ)
      have hr := hrec n hp
      rw [Nat.digits_of_two_le_of_pos (by decide) hp, List.length_cons, pow_succ]
      nlinarith
  exact (le_add_of_nonneg_right hC).trans (hbound n)

/-- In particular, a common scalar register multiplier cannot give a
subcritical matrix certificate merely by changing digit injections. -/
theorem uniform_recurrence_obstruction (S : ℕ → ℝ) (lam ρ B : ℝ)
    (hlam : 1 < lam) (hρ : 1 < ρ) (hB : 0 ≤ B) (hzero : 0 < S 0)
    (hgrow : ∀ n, lam * S n ≤ S (4 * n + 1))
    (hrec : ∀ n, 0 < n → S n ≤ ρ * S (n / 3) + B) :
    Real.log lam * Real.log 3 ≤ Real.log ρ * Real.log 4 := by
  have hK : 0 < S 0 + B / (ρ - 1) :=
    add_pos_of_pos_of_nonneg hzero (div_nonneg hB (by linarith))
  exact global_rate_obstruction S lam ρ _ hlam hρ.le hK hzero hgrow
    (uniform_recurrence_upper S ρ B hρ hB hrec)

variable {σ : Type*} [Fintype σ]

lemma all_digits_rate (D : Dynamics σ) (ell : σ → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hstep : ∀ d < 3, ∀ j, Matrix.vecMul ell (D.A d) j ≤ ρ * ell j)
    (n : ℕ) :
    ell ⬝ᵥ D.v n ≤ ρ ^ (Nat.digits 3 n).length * (ell ⬝ᵥ D.v 0) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · subst n; simp
    have hp : 0 < n := Nat.pos_of_ne_zero hz
    have hi := ih (n / 3) (Nat.div_lt_self hp (by decide))
    have hs := dot_mono_left (hstep (n % 3) (Nat.mod_lt _ (by decide)))
      (D.value_nonneg (n / 3))
    have hm := mul_le_mul_of_nonneg_left hi hρ
    rw [D.recurrence n hp, Matrix.dotProduct_mulVec,
      Nat.digits_of_two_le_of_pos (by decide) hp, List.length_cons, pow_succ]
    have he : (fun j => ρ * ell j) ⬝ᵥ D.v (n / 3) = ρ * (ell ⬝ᵥ D.v (n / 3)) := by
      simp only [dotProduct, Finset.mul_sum, mul_assoc]
    rw [he] at hs
    nlinarith

/-- If a dominating functional has the claimed rate on all three digits,
the strict rate gap required by `matrix_affine_criterion` is impossible. -/
theorem global_matrix_rate_obstruction (D : Dynamics σ) (u ell : σ → ℝ)
    (lam ρ : ℝ) (hu : 0 ≤ u) (hul : u ≤ ell) (hzero : 0 < u ⬝ᵥ D.v 0)
    (hlam : 1 < lam) (hρ : 1 ≤ ρ)
    (hfinish : ∀ j, lam * u j ≤ Matrix.vecMul u (D.H 1) j)
    (hstep : ∀ d < 3, ∀ j, Matrix.vecMul ell (D.A d) j ≤ ρ * ell j) :
    Real.log lam * Real.log 3 ≤ Real.log ρ * Real.log 4 := by
  have hK : 0 < ell ⬝ᵥ D.v 0 := hzero.trans_le (dot_mono_left hul (D.value_nonneg 0))
  apply global_rate_obstruction (fun n => u ⬝ᵥ D.v n) lam ρ _
    hlam hρ hK hzero (D.scalar_growth u lam hu hfinish)
  intro n
  have hh := (dot_mono_left hul (D.value_nonneg n)).trans
    (all_digits_rate D ell ρ (by linarith) hstep n)
  simpa [mul_comm] using hh

#print axioms global_rate_obstruction
#print axioms uniform_recurrence_obstruction
#print axioms global_matrix_rate_obstruction
end Erdos406MatrixGlobalRate
