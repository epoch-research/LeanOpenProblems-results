import FormalConjectures.Util.ProblemImports
open Nat BigOperators Finset

lemma sq_eq_three_mul_add_one_imp_zform {k r : ℕ} (h : r * r = 3 * k + 1) :
    ∃ z : ℤ, (z * (3 * z + 2)).toNat = k := by
  let a := r / 3
  have hdiv := Nat.div_add_mod r 3
  have hmodlt : r % 3 < 3 := Nat.mod_lt _ (by decide : 0 < 3)
  interval_cases hm : r % 3
  · exfalso
    have hr : r = 3 * a := by
      dsimp [a]
      omega
    have hmod := congrArg (fun t : ℕ => t % 3) h
    norm_num [hr, Nat.add_mod, Nat.mul_mod] at hmod
  · refine ⟨(a : ℤ), ?_⟩
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg]
    · have hr : r = 3 * a + 1 := by
        dsimp [a]
        omega
      apply_fun (fun t : ℕ => (t : ℤ)) at h
      norm_num at h
      rw [hr] at h
      norm_num at h
      ring_nf at h ⊢
      nlinarith
    · show (0 : ℤ) ≤ (a : ℤ) * (3 * (a : ℤ) + 2)
      nlinarith [show (0 : ℤ) ≤ a by exact_mod_cast Nat.zero_le a]
  · refine ⟨-((a + 1 : ℕ) : ℤ), ?_⟩
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg]
    · have hr : r = 3 * a + 2 := by
        dsimp [a]
        omega
      have h2 : 2 ≤ 3 * (a + 1) := by nlinarith
      apply_fun (fun t : ℕ => (t : ℤ)) at h
      norm_num at h
      rw [hr] at h
      norm_num at h
      ring_nf at h ⊢
      norm_num [Nat.cast_sub h2]
      ring_nf
      nlinarith
    · show (0 : ℤ) ≤ (-(↑(a + 1))) * (3 * (-(↑(a + 1))) + 2)
      ring_nf
      nlinarith [show (0 : ℤ) ≤ a by exact_mod_cast Nat.zero_le a]
