import FormalConjectures.Util.ProblemImports

open Nat

#check Nat.Prime.dvd_iff_one_le_factorization
#check Nat.Prime.dvd_factorial
#check Nat.factorization_le_iff_dvd
#check Nat.factorization_factorial

lemma div_le_factorization_factorial {m p : ℕ} (hp : p.Prime) :
    m / p ≤ (m !).factorization p := by
  by_cases hpm : p ≤ m
  · rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p m))]
    -- term i=1 of the sum is m/p.
    have hlogpos : 0 < Nat.log p m := Nat.log_pos hp.one_lt hpm
    have hmem : 1 ∈ Finset.Ico 1 (Nat.log p m + 1) := by
      simp only [Finset.mem_Ico]
      exact ⟨le_rfl, Nat.succ_lt_succ hlogpos⟩
    have hterm : (fun i : ℕ => m / p ^ i) 1 = m / p := by simp
    calc
      m / p = (fun i : ℕ => m / p ^ i) 1 := hterm.symm
      _ ≤ ∑ i ∈ Finset.Ico 1 (Nat.log p m + 1), m / p ^ i := by
        exact Finset.single_le_sum (f := fun i : ℕ => m / p ^ i) (s := Finset.Ico 1 (Nat.log p m + 1)) (fun i hi => by omega) hmem
  · have : m / p = 0 := Nat.div_eq_of_lt (Nat.lt_of_not_ge hpm)
    simp [this]
