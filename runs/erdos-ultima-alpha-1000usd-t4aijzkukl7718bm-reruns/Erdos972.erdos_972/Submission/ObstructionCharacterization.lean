import Submission.Exploration
import Submission.LocalObstructions

/-!
# Characterization of finite-modulus obstructions

This is an auxiliary characterization for Erdős 972. The indices in the main
characterization are arbitrary natural numbers, not necessarily prime.
-/

namespace Explore972

/-- Among slopes greater than one, the integer slopes are exactly the ones
that can obstruct simultaneous coprimality with a fixed modulus. This does
not imply simultaneous primality. -/
theorem noninteger_iff_all_moduli_avoidable {α : ℝ} (hα : 1 < α) :
    (¬ ∃ m : ℕ, α = m) ↔
      ∀ M : ℕ, 0 < M → ∀ N : ℕ, ∃ n : ℕ,
        N < n ∧ n.Coprime M ∧ (⌊(α * n)⌋₊).Coprime M := by
  constructor
  · intro hnot M hM N
    by_cases hi : Irrational α
    · exact simultaneous_coprime_indices hα hi M hM N
    obtain ⟨q, rfl⟩ := exists_rat_of_not_irrational hi
    have hqnonneg : (0 : ℚ) ≤ q := by
      exact_mod_cast (show (0 : ℝ) ≤ q by linarith)
    have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hqnonneg
    let a : ℕ := q.num.toNat
    have hnuma : (a : ℤ) = q.num := Int.toNat_of_nonneg hnum
    have haabs : a = q.num.natAbs := by
      simpa using congrArg Int.natAbs hnuma
    have ha : (q : ℝ) = (a : ℝ) / q.den := by
      rw [Rat.cast_def, ← hnuma]
      simp only [Int.cast_natCast]
    have hab : a.Coprime q.den := by
      rw [haabs]
      exact q.reduced
    have hb : 1 < q.den := by
      have hd := q.den_pos
      by_contra h
      have he : q.den = 1 := by omega
      exact hnot ⟨a, by simpa [he] using ha⟩
    obtain ⟨p, hbound, hp, hc⟩ :=
      rational_slope_prime_indices_coprime a q.den hb hab M hM (max M N)
    have hMp : M < p := lt_of_le_of_lt (le_max_left M N) hbound
    have hNp : N < p := lt_of_le_of_lt (le_max_right M N) hbound
    refine ⟨p, hNp, hp.coprime_iff_not_dvd.mpr ?_, ?_⟩
    · intro hdiv
      have := Nat.le_of_dvd hM hdiv
      omega
    · rwa [ha]
  · rintro h ⟨m, rfl⟩
    have hm : 1 < m := by exact_mod_cast hα
    obtain ⟨n, _, _, hc⟩ := h m (by omega) 0
    have hf : ⌊((m : ℝ) * n)⌋₊ = m * n := by
      rw [← Nat.cast_mul, Nat.floor_natCast]
    rw [hf] at hc
    have hm1 := Nat.eq_one_of_dvd_coprimes hc (dvd_mul_right m n) (dvd_refl m)
    omega

/-- A fixed-modulus obstruction at all sufficiently large indices exists
exactly for integer slopes. This statement does not restrict the indices
to primes. -/
theorem finite_modulus_obstruction_iff_integer {α : ℝ} (hα : 1 < α) :
    (∃ M : ℕ, 0 < M ∧ ∃ N : ℕ, ∀ n : ℕ, N < n →
      n.Coprime M → ¬ (⌊(α * n)⌋₊).Coprime M) ↔ ∃ m : ℕ, α = m := by
  have h := not_congr (noninteger_iff_all_moduli_avoidable hα)
  push_neg at h
  exact h.symm

#print axioms noninteger_iff_all_moduli_avoidable
#print axioms finite_modulus_obstruction_iff_integer

end Explore972
