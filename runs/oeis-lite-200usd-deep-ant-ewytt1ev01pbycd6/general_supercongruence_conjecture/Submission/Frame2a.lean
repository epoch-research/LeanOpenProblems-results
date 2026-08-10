import Submission.Frame1
open PowerSeries
namespace Frame2a
open ExpFrame Frame1 Finset

lemma term_deriv (K : PowerSeries ℚ) (i : ℕ) :
    d⁄dX ℚ ((1/((i+1).factorial:ℚ)) • K^(i+1)) = (1/(i.factorial:ℚ)) • (K^i * d⁄dX ℚ K) := by
  rw [Derivation.map_smul_of_tower, Derivation.leibniz_pow]
  simp only [Nat.add_sub_cancel, smul_eq_mul]
  rw [← Nat.cast_smul_eq_nsmul ℚ (i+1), smul_smul]
  congr 1
  have h1 : ((i+1).factorial : ℚ) = ((i+1:ℕ):ℚ) * (i.factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [h1]
  have hf : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hi : ((i+1:ℕ):ℚ) ≠ 0 := by positivity
  field_simp

noncomputable def S (K : PowerSeries ℚ) (J : ℕ) : PowerSeries ℚ :=
  ∑ i ∈ Finset.range J, (1/(i.factorial:ℚ)) • K^i

lemma coeff_S (K : PowerSeries ℚ) (n J : ℕ) :
    coeff n (S K J) = ∑ i ∈ Finset.range J, coeff n (K^i) / (i.factorial:ℚ) := by
  rw [S, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [coeff_smul, smul_eq_mul]; ring

lemma vanish (K : PowerSeries ℚ) (hK : constantCoeff K = 0) (i n : ℕ) (hn : n < i) :
    coeff n (K^i) = 0 := by
  have hpow : (X:PowerSeries ℚ)^i ∣ K^i := pow_dvd_pow_of_dvd (X_dvd_iff.mpr hK) i
  exact (X_pow_dvd_iff.mp hpow) n hn

lemma deriv_S (K : PowerSeries ℚ) (J : ℕ) :
    d⁄dX ℚ (S K (J+1)) = S K J * d⁄dX ℚ K := by
  rw [S, map_sum, Finset.sum_range_succ']
  have hlast : d⁄dX ℚ ((1/((0:ℕ).factorial:ℚ)) • K^(0:ℕ)) = 0 := by
    simp
  rw [hlast, add_zero, S, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [term_deriv, smul_mul_assoc]

theorem Exp_eq_sum (K : PowerSeries ℚ) (hK : PowerSeries.constantCoeff K = 0) :
    Exp K = PowerSeries.mk (fun n => ∑ j ∈ Finset.range (n+1), PowerSeries.coeff n (K^j) / (j.factorial : ℚ)) := by
  set G : PowerSeries ℚ :=
    PowerSeries.mk (fun n => ∑ j ∈ Finset.range (n+1), coeff n (K^j) / (j.factorial : ℚ)) with hGdef
  rw [Exp]
  symm
  apply expOf_unique
  · -- coeff 0 G = 1
    rw [hGdef, coeff_mk, Finset.sum_range_one, pow_zero, coeff_one]
    simp
  · -- ODE
    have hGS : ∀ n J, n < J → coeff n G = coeff n (S K J) := by
      intro n J hnJ
      rw [hGdef, coeff_mk, coeff_S]
      apply Finset.sum_subset
      · intro x hx; rw [Finset.mem_range] at hx ⊢; omega
      · intro x hx hxnot
        rw [Finset.mem_range] at hx hxnot
        rw [vanish K hK x n (by omega)]; simp
    ext n
    rw [coeff_derivative]
    rw [hGS (n+1) (n+1+1) (by omega)]
    rw [← coeff_derivative (S K (n+1+1)) n]
    rw [deriv_S K (n+1)]
    rw [coeff_mul, coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    rw [hGS p.1 (n+1) (by omega)]

#print axioms Frame2a.Exp_eq_sum
end Frame2a
